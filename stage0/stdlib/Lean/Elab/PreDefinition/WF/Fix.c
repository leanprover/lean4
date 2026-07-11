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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0;
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
lean_object* v___x_710_; lean_object* v_env_711_; uint8_t v___y_713_; uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_710_);
v___x_769_ = l_Lean_Name_isAnonymous(v_declHint_707_);
v___x_770_ = lean_bool_not(v___x_769_);
if (v___x_770_ == 0)
{
v___y_713_ = v___x_770_;
goto v___jp_712_;
}
else
{
uint8_t v_isExporting_771_; 
v_isExporting_771_ = lean_ctor_get_uint8(v_env_711_, sizeof(void*)*8);
v___y_713_ = v_isExporting_771_;
goto v___jp_712_;
}
v___jp_712_:
{
if (v___y_713_ == 0)
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
uint8_t v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = 0;
lean_inc_ref(v_env_711_);
v___x_716_ = l_Lean_Environment_setExporting(v_env_711_, v___x_715_);
lean_inc(v_declHint_707_);
lean_inc_ref(v___x_716_);
v___x_717_ = l_Lean_Environment_contains(v___x_716_, v_declHint_707_, v___y_713_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v___x_716_);
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_msg_706_);
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
lean_inc(v_declHint_707_);
v___x_723_ = l_Lean_MessageData_ofConstName(v_declHint_707_, v___x_715_);
v_c_724_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_724_, 0, v___x_722_);
lean_ctor_set(v_c_724_, 1, v___x_723_);
v___x_725_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_711_, v_declHint_707_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
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
lean_ctor_set(v___x_731_, 0, v_msg_706_);
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
v___x_738_ = l_Lean_Environment_header(v_env_711_);
lean_dec_ref(v_env_711_);
v___x_739_ = l_Lean_EnvironmentHeader_moduleNames(v___x_738_);
v_mod_740_ = lean_array_get(v___x_737_, v___x_739_, v_val_733_);
lean_dec(v_val_733_);
lean_dec_ref(v___x_739_);
v___x_741_ = l_Lean_isPrivateName(v_declHint_707_);
lean_dec(v_declHint_707_);
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
lean_ctor_set(v___x_751_, 0, v_msg_706_);
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
lean_ctor_set(v___x_764_, 0, v_msg_706_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_772_, lean_object* v_declHint_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_772_, v_declHint_773_, v___y_774_);
lean_dec(v___y_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_777_, lean_object* v_declHint_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_798_; 
v___x_788_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_777_, v_declHint_778_, v___y_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_798_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = l_Lean_unknownIdentifierMessageTag;
v___x_794_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_799_, lean_object* v_declHint_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_799_, v_declHint_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec(v___y_801_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_811_, lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_fileName_822_; lean_object* v_fileMap_823_; lean_object* v_options_824_; lean_object* v_currRecDepth_825_; lean_object* v_maxRecDepth_826_; lean_object* v_ref_827_; lean_object* v_currNamespace_828_; lean_object* v_openDecls_829_; lean_object* v_initHeartbeats_830_; lean_object* v_maxHeartbeats_831_; lean_object* v_quotContext_832_; lean_object* v_currMacroScope_833_; uint8_t v_diag_834_; lean_object* v_cancelTk_x3f_835_; uint8_t v_suppressElabErrors_836_; lean_object* v_inheritedTraceOptions_837_; lean_object* v_ref_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_fileName_822_ = lean_ctor_get(v___y_819_, 0);
v_fileMap_823_ = lean_ctor_get(v___y_819_, 1);
v_options_824_ = lean_ctor_get(v___y_819_, 2);
v_currRecDepth_825_ = lean_ctor_get(v___y_819_, 3);
v_maxRecDepth_826_ = lean_ctor_get(v___y_819_, 4);
v_ref_827_ = lean_ctor_get(v___y_819_, 5);
v_currNamespace_828_ = lean_ctor_get(v___y_819_, 6);
v_openDecls_829_ = lean_ctor_get(v___y_819_, 7);
v_initHeartbeats_830_ = lean_ctor_get(v___y_819_, 8);
v_maxHeartbeats_831_ = lean_ctor_get(v___y_819_, 9);
v_quotContext_832_ = lean_ctor_get(v___y_819_, 10);
v_currMacroScope_833_ = lean_ctor_get(v___y_819_, 11);
v_diag_834_ = lean_ctor_get_uint8(v___y_819_, sizeof(void*)*14);
v_cancelTk_x3f_835_ = lean_ctor_get(v___y_819_, 12);
v_suppressElabErrors_836_ = lean_ctor_get_uint8(v___y_819_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_837_ = lean_ctor_get(v___y_819_, 13);
v_ref_838_ = l_Lean_replaceRef(v_ref_811_, v_ref_827_);
lean_inc_ref(v_inheritedTraceOptions_837_);
lean_inc(v_cancelTk_x3f_835_);
lean_inc(v_currMacroScope_833_);
lean_inc(v_quotContext_832_);
lean_inc(v_maxHeartbeats_831_);
lean_inc(v_initHeartbeats_830_);
lean_inc(v_openDecls_829_);
lean_inc(v_currNamespace_828_);
lean_inc(v_maxRecDepth_826_);
lean_inc(v_currRecDepth_825_);
lean_inc_ref(v_options_824_);
lean_inc_ref(v_fileMap_823_);
lean_inc_ref(v_fileName_822_);
v___x_839_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_839_, 0, v_fileName_822_);
lean_ctor_set(v___x_839_, 1, v_fileMap_823_);
lean_ctor_set(v___x_839_, 2, v_options_824_);
lean_ctor_set(v___x_839_, 3, v_currRecDepth_825_);
lean_ctor_set(v___x_839_, 4, v_maxRecDepth_826_);
lean_ctor_set(v___x_839_, 5, v_ref_838_);
lean_ctor_set(v___x_839_, 6, v_currNamespace_828_);
lean_ctor_set(v___x_839_, 7, v_openDecls_829_);
lean_ctor_set(v___x_839_, 8, v_initHeartbeats_830_);
lean_ctor_set(v___x_839_, 9, v_maxHeartbeats_831_);
lean_ctor_set(v___x_839_, 10, v_quotContext_832_);
lean_ctor_set(v___x_839_, 11, v_currMacroScope_833_);
lean_ctor_set(v___x_839_, 12, v_cancelTk_x3f_835_);
lean_ctor_set(v___x_839_, 13, v_inheritedTraceOptions_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*14, v_diag_834_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*14 + 1, v_suppressElabErrors_836_);
v___x_840_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_812_, v___y_817_, v___y_818_, v___x_839_, v___y_820_);
lean_dec_ref_known(v___x_839_, 14);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_841_, lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_841_, v_msg_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec(v_ref_841_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_853_, lean_object* v_msg_854_, lean_object* v_declHint_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; 
v___x_865_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_854_, v_declHint_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_853_, v_a_866_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_868_, lean_object* v_msg_869_, lean_object* v_declHint_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_868_, v_msg_869_, v_declHint_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v_ref_868_);
return v_res_880_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_887_, lean_object* v_constName_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_898_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_899_ = 0;
lean_inc(v_constName_888_);
v___x_900_ = l_Lean_MessageData_ofConstName(v_constName_888_, v___x_899_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_898_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_887_, v___x_903_, v_constName_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_905_, lean_object* v_constName_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_905_, v_constName_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v___y_907_);
lean_dec(v_ref_905_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_ref_927_; lean_object* v___x_928_; 
v_ref_927_ = lean_ctor_get(v___y_924_, 5);
v___x_928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_927_, v_constName_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_env_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v___x_950_ = lean_st_ref_get(v___y_948_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
v___x_952_ = 0;
lean_inc(v_constName_940_);
v___x_953_ = l_Lean_Environment_find_x3f(v_env_951_, v_constName_940_, v___x_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_constName_940_);
v_val_955_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_953_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v___x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_env_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_st_ref_get(v___y_975_);
v_env_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_977_);
v___x_979_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_978_, v_declName_974_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_981_, v___y_982_);
lean_dec(v___y_982_);
return v_res_984_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_instMonadEIO(lean_box(0));
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_toApplicative_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1097_; 
v___x_1002_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_1003_ = l_StateRefT_x27_instMonad___redArg(v___x_1002_);
v_toApplicative_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1003_, 1);
lean_dec(v_unused_1098_);
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1097_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_toApplicative_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1097_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_toFunctor_1008_; lean_object* v_toSeq_1009_; lean_object* v_toSeqLeft_1010_; lean_object* v_toSeqRight_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1095_; 
v_toFunctor_1008_ = lean_ctor_get(v_toApplicative_1004_, 0);
v_toSeq_1009_ = lean_ctor_get(v_toApplicative_1004_, 2);
v_toSeqLeft_1010_ = lean_ctor_get(v_toApplicative_1004_, 3);
v_toSeqRight_1011_ = lean_ctor_get(v_toApplicative_1004_, 4);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_toApplicative_1004_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_toApplicative_1004_, 1);
lean_dec(v_unused_1096_);
v___x_1013_ = v_toApplicative_1004_;
v_isShared_1014_ = v_isSharedCheck_1095_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_toSeqRight_1011_);
lean_inc(v_toSeqLeft_1010_);
lean_inc(v_toSeq_1009_);
lean_inc(v_toFunctor_1008_);
lean_dec(v_toApplicative_1004_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1095_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___x_1024_; 
v___f_1015_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1016_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1008_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toFunctor_1008_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toFunctor_1008_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___f_1017_);
lean_ctor_set(v___x_1019_, 1, v___f_1018_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toSeqRight_1011_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toSeqLeft_1010_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeq_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 4, v___f_1020_);
lean_ctor_set(v___x_1013_, 3, v___f_1021_);
lean_ctor_set(v___x_1013_, 2, v___f_1022_);
lean_ctor_set(v___x_1013_, 1, v___f_1015_);
lean_ctor_set(v___x_1013_, 0, v___x_1019_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___f_1015_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v___f_1022_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___f_1021_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v___f_1020_);
v___x_1024_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___f_1016_);
lean_ctor_set(v___x_1006_, 0, v___x_1024_);
v___x_1026_ = v___x_1006_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___f_1016_);
v___x_1026_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v_toApplicative_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1091_; 
v___x_1027_ = l_StateRefT_x27_instMonad___redArg(v___x_1026_);
v_toApplicative_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1027_, 1);
lean_dec(v_unused_1092_);
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1091_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_toApplicative_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1091_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_toFunctor_1032_; lean_object* v_toSeq_1033_; lean_object* v_toSeqLeft_1034_; lean_object* v_toSeqRight_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1089_; 
v_toFunctor_1032_ = lean_ctor_get(v_toApplicative_1028_, 0);
v_toSeq_1033_ = lean_ctor_get(v_toApplicative_1028_, 2);
v_toSeqLeft_1034_ = lean_ctor_get(v_toApplicative_1028_, 3);
v_toSeqRight_1035_ = lean_ctor_get(v_toApplicative_1028_, 4);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_toApplicative_1028_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_toApplicative_1028_, 1);
lean_dec(v_unused_1090_);
v___x_1037_ = v_toApplicative_1028_;
v_isShared_1038_ = v_isSharedCheck_1089_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_toSeqRight_1035_);
lean_inc(v_toSeqLeft_1034_);
lean_inc(v_toSeq_1033_);
lean_inc(v_toFunctor_1032_);
lean_dec(v_toApplicative_1028_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1089_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1048_; 
v___f_1039_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1040_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1032_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toFunctor_1032_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toFunctor_1032_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___f_1041_);
lean_ctor_set(v___x_1043_, 1, v___f_1042_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toSeqRight_1035_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toSeqLeft_1034_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toSeq_1033_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 4, v___f_1044_);
lean_ctor_set(v___x_1037_, 3, v___f_1045_);
lean_ctor_set(v___x_1037_, 2, v___f_1046_);
lean_ctor_set(v___x_1037_, 1, v___f_1039_);
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1048_ = v___x_1037_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___f_1039_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v___f_1046_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v___f_1045_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___f_1044_);
v___x_1048_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___f_1040_);
lean_ctor_set(v___x_1030_, 0, v___x_1048_);
v___x_1050_ = v___x_1030_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___f_1040_);
v___x_1050_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v_toApplicative_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1085_; 
v___x_1051_ = l_StateRefT_x27_instMonad___redArg(v___x_1050_);
v_toApplicative_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_1051_, 1);
lean_dec(v_unused_1086_);
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1085_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_toApplicative_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1085_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_toFunctor_1056_; lean_object* v_toSeq_1057_; lean_object* v_toSeqLeft_1058_; lean_object* v_toSeqRight_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1083_; 
v_toFunctor_1056_ = lean_ctor_get(v_toApplicative_1052_, 0);
v_toSeq_1057_ = lean_ctor_get(v_toApplicative_1052_, 2);
v_toSeqLeft_1058_ = lean_ctor_get(v_toApplicative_1052_, 3);
v_toSeqRight_1059_ = lean_ctor_get(v_toApplicative_1052_, 4);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_toApplicative_1052_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_toApplicative_1052_, 1);
lean_dec(v_unused_1084_);
v___x_1061_ = v_toApplicative_1052_;
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_toSeqRight_1059_);
lean_inc(v_toSeqLeft_1058_);
lean_inc(v_toSeq_1057_);
lean_inc(v_toFunctor_1056_);
lean_dec(v_toApplicative_1052_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1072_; 
v___f_1063_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1064_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1056_);
v___f_1065_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1065_, 0, v_toFunctor_1056_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toFunctor_1056_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___f_1065_);
lean_ctor_set(v___x_1067_, 1, v___f_1066_);
v___f_1068_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1068_, 0, v_toSeqRight_1059_);
v___f_1069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1069_, 0, v_toSeqLeft_1058_);
v___f_1070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1070_, 0, v_toSeq_1057_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v___f_1068_);
lean_ctor_set(v___x_1061_, 3, v___f_1069_);
lean_ctor_set(v___x_1061_, 2, v___f_1070_);
lean_ctor_set(v___x_1061_, 1, v___f_1063_);
lean_ctor_set(v___x_1061_, 0, v___x_1067_);
v___x_1072_ = v___x_1061_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1063_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v___f_1070_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v___f_1069_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v___f_1068_);
v___x_1072_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___f_1064_);
lean_ctor_set(v___x_1054_, 0, v___x_1072_);
v___x_1074_ = v___x_1054_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1064_);
v___x_1074_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_58328__overap_1079_; lean_object* v___x_1080_; 
v___x_1075_ = l_StateRefT_x27_instMonad___redArg(v___x_1074_);
v___x_1076_ = l_StateRefT_x27_instMonad___redArg(v___x_1075_);
v___x_1077_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1078_ = l_instInhabitedOfMonad___redArg(v___x_1076_, v___x_1077_);
v___x_58328__overap_1079_ = lean_panic_fn_borrowed(v___x_1078_, v_msg_992_);
lean_dec(v___x_1078_);
lean_inc(v___y_1000_);
lean_inc_ref(v___y_999_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc(v___y_993_);
v___x_1080_ = lean_apply_9(v___x_58328__overap_1079_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, lean_box(0));
return v___x_1080_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
return v_res_1109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1114_ = lean_unsigned_to_nat(53u);
v___x_1115_ = lean_unsigned_to_nat(62u);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1118_ = l_mkPanicMessageWithDecl(v___x_1117_, v___x_1116_, v___x_1115_, v___x_1114_, v___x_1113_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_bs_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_usize_dec_lt(v_i_1120_, v_sz_1119_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_bs_1121_);
return v___x_1132_;
}
else
{
lean_object* v_v_1133_; lean_object* v___x_1134_; 
v_v_1133_ = lean_array_uget_borrowed(v_bs_1121_, v_i_1120_);
lean_inc(v_v_1133_);
v___x_1134_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1133_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v_bs_x27_1137_; lean_object* v_a_1139_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = lean_unsigned_to_nat(0u);
v_bs_x27_1137_ = lean_array_uset(v_bs_1121_, v_i_1120_, v___x_1136_);
if (lean_obj_tag(v_a_1135_) == 6)
{
lean_object* v_val_1144_; lean_object* v_numFields_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v_val_1144_ = lean_ctor_get(v_a_1135_, 0);
lean_inc_ref(v_val_1144_);
lean_dec_ref_known(v_a_1135_, 1);
v_numFields_1145_ = lean_ctor_get(v_val_1144_, 4);
lean_inc(v_numFields_1145_);
lean_dec_ref(v_val_1144_);
v___x_1146_ = 0;
v___x_1147_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1147_, 0, v_numFields_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1136_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*2, v___x_1146_);
v_a_1139_ = v___x_1147_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v_a_1135_);
v___x_1148_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1149_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1148_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v_a_1139_ = v_a_1150_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_bs_x27_1137_);
v_a_1151_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1149_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
v___jp_1138_:
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1120_, v___x_1140_);
v___x_1142_ = lean_array_uset(v_bs_x27_1137_, v_i_1120_, v_a_1139_);
v_i_1120_ = v___x_1141_;
v_bs_1121_ = v___x_1142_;
goto _start;
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_bs_1121_);
v_a_1159_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1134_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1134_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_bs_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1179_, v_i_boxed_1180_, v_bs_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v___y_1170_);
return v_res_1181_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1182_; lean_object* v_dummy_1183_; 
v___x_1182_ = lean_box(0);
v_dummy_1183_ = l_Lean_Expr_sort___override(v___x_1182_);
return v_dummy_1183_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_unsigned_to_nat(16u);
v___x_1186_ = lean_mk_array(v___x_1185_, v___x_1184_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1192_, uint8_t v_alsoCasesOn_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_Expr_isApp(v_e_1192_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec_ref(v_e_1192_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Expr_getAppFn(v_e_1192_);
if (lean_obj_tag(v___x_1209_) == 4)
{
lean_object* v_declName_1210_; lean_object* v_us_1211_; lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1367_; 
v_declName_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc_n(v_declName_1210_, 2);
v_us_1211_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_us_1211_);
lean_dec_ref_known(v___x_1209_, 2);
v___x_1212_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1210_, v___y_1201_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1367_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1367_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
if (lean_obj_tag(v_a_1213_) == 1)
{
lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1259_; 
v_val_1217_ = lean_ctor_get(v_a_1213_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1213_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1219_ = v_a_1213_;
v_isShared_1220_ = v_isSharedCheck_1259_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_dec(v_a_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1259_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_dummy_1221_; lean_object* v_nargs_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_args_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_dummy_1221_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1222_ = l_Lean_Expr_getAppNumArgs(v_e_1192_);
lean_inc(v_nargs_1222_);
v___x_1223_ = lean_mk_array(v_nargs_1222_, v_dummy_1221_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_sub(v_nargs_1222_, v___x_1224_);
lean_dec(v_nargs_1222_);
v_args_1226_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1192_, v___x_1223_, v___x_1225_);
v___x_1227_ = lean_array_get_size(v_args_1226_);
v___x_1228_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1217_);
v___x_1229_ = lean_nat_dec_lt(v___x_1227_, v___x_1228_);
lean_dec(v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v_numParams_1230_; lean_object* v_numDiscrs_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_numParams_1230_ = lean_ctor_get(v_val_1217_, 0);
v_numDiscrs_1231_ = lean_ctor_get(v_val_1217_, 1);
v___x_1232_ = lean_array_mk(v_us_1211_);
v___x_1233_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1230_);
v___x_1234_ = l_Array_extract___redArg(v_args_1226_, v___x_1233_, v_numParams_1230_);
v___x_1235_ = l_Lean_instInhabitedExpr;
v___x_1236_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1217_);
v___x_1237_ = lean_array_get(v___x_1235_, v_args_1226_, v___x_1236_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_nat_add(v_numParams_1230_, v___x_1224_);
v___x_1239_ = lean_nat_add(v___x_1238_, v_numDiscrs_1231_);
lean_inc(v___x_1239_);
lean_inc_ref_n(v_args_1226_, 2);
v___x_1240_ = l_Array_toSubarray___redArg(v_args_1226_, v___x_1238_, v___x_1239_);
v___x_1241_ = l_Subarray_copy___redArg(v___x_1240_);
v___x_1242_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1217_);
v___x_1243_ = lean_nat_add(v___x_1239_, v___x_1242_);
lean_dec(v___x_1242_);
lean_inc(v___x_1243_);
v___x_1244_ = l_Array_toSubarray___redArg(v_args_1226_, v___x_1239_, v___x_1243_);
v___x_1245_ = l_Subarray_copy___redArg(v___x_1244_);
v___x_1246_ = l_Array_toSubarray___redArg(v_args_1226_, v___x_1243_, v___x_1227_);
v___x_1247_ = l_Subarray_copy___redArg(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1248_, 0, v_val_1217_);
lean_ctor_set(v___x_1248_, 1, v_declName_1210_);
lean_ctor_set(v___x_1248_, 2, v___x_1232_);
lean_ctor_set(v___x_1248_, 3, v___x_1234_);
lean_ctor_set(v___x_1248_, 4, v___x_1237_);
lean_ctor_set(v___x_1248_, 5, v___x_1241_);
lean_ctor_set(v___x_1248_, 6, v___x_1245_);
lean_ctor_set(v___x_1248_, 7, v___x_1247_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1248_);
v___x_1250_ = v___x_1219_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1250_);
v___x_1252_ = v___x_1215_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
lean_dec_ref(v_args_1226_);
lean_del_object(v___x_1219_);
lean_dec(v_val_1217_);
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
v___x_1255_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1255_);
v___x_1257_ = v___x_1215_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v___x_1260_; 
lean_del_object(v___x_1215_);
lean_dec(v_a_1213_);
v___x_1260_ = lean_st_ref_get(v___y_1201_);
if (v_alsoCasesOn_1193_ == 0)
{
lean_dec(v___x_1260_);
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
lean_dec_ref(v_e_1192_);
goto v___jp_1203_;
}
else
{
lean_object* v_env_1261_; uint8_t v___x_1262_; 
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1260_);
lean_inc(v_declName_1210_);
v___x_1262_ = l_Lean_isCasesOnRecursor(v_env_1261_, v_declName_1210_);
if (v___x_1262_ == 0)
{
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
lean_dec_ref(v_e_1192_);
goto v___jp_1203_;
}
else
{
lean_object* v_indName_1263_; lean_object* v___x_1264_; 
v_indName_1263_ = l_Lean_Name_getPrefix(v_declName_1210_);
v___x_1264_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1263_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1358_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1358_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1358_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
if (lean_obj_tag(v_a_1265_) == 5)
{
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1353_; 
v_val_1269_ = lean_ctor_get(v_a_1265_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_a_1265_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1271_ = v_a_1265_;
v_isShared_1272_ = v_isSharedCheck_1353_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v_a_1265_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1353_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_toConstantVal_1273_; lean_object* v_numParams_1274_; lean_object* v_numIndices_1275_; lean_object* v_ctors_1276_; lean_object* v_nargs_1277_; lean_object* v_dummy_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_args_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_toConstantVal_1273_ = lean_ctor_get(v_val_1269_, 0);
lean_inc_ref(v_toConstantVal_1273_);
v_numParams_1274_ = lean_ctor_get(v_val_1269_, 1);
lean_inc(v_numParams_1274_);
v_numIndices_1275_ = lean_ctor_get(v_val_1269_, 2);
lean_inc(v_numIndices_1275_);
v_ctors_1276_ = lean_ctor_get(v_val_1269_, 4);
lean_inc(v_ctors_1276_);
v_nargs_1277_ = l_Lean_Expr_getAppNumArgs(v_e_1192_);
v_dummy_1278_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1277_);
v___x_1279_ = lean_mk_array(v_nargs_1277_, v_dummy_1278_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_sub(v_nargs_1277_, v___x_1280_);
lean_dec(v_nargs_1277_);
v_args_1282_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1192_, v___x_1279_, v___x_1281_);
v___x_1283_ = lean_nat_add(v_numParams_1274_, v___x_1280_);
v___x_1284_ = lean_nat_add(v___x_1283_, v_numIndices_1275_);
v___x_1285_ = lean_nat_add(v___x_1284_, v___x_1280_);
lean_dec(v___x_1284_);
v___x_1286_ = l_Lean_InductiveVal_numCtors(v_val_1269_);
lean_dec_ref(v_val_1269_);
v___x_1287_ = lean_nat_add(v___x_1285_, v___x_1286_);
lean_dec(v___x_1286_);
v___x_1288_ = lean_array_get_size(v_args_1282_);
v___x_1289_ = lean_nat_dec_le(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
lean_dec(v___x_1287_);
lean_dec(v___x_1285_);
lean_dec(v___x_1283_);
lean_dec_ref(v_args_1282_);
lean_dec(v_ctors_1276_);
lean_dec(v_numIndices_1275_);
lean_dec(v_numParams_1274_);
lean_dec_ref(v_toConstantVal_1273_);
lean_del_object(v___x_1271_);
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
v___x_1290_ = lean_box(0);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1290_);
v___x_1292_ = v___x_1267_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v___x_1294_; lean_object* v_params_1295_; lean_object* v___x_1296_; lean_object* v_motive_1297_; lean_object* v_discrs_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_discrInfos_1301_; lean_object* v_alts_1302_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v_lower_1344_; lean_object* v_upper_1345_; uint8_t v___x_1352_; 
lean_del_object(v___x_1267_);
v___x_1294_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1274_);
lean_inc_ref_n(v_args_1282_, 3);
v_params_1295_ = l_Array_toSubarray___redArg(v_args_1282_, v___x_1294_, v_numParams_1274_);
v___x_1296_ = l_Lean_instInhabitedExpr;
v_motive_1297_ = lean_array_get(v___x_1296_, v_args_1282_, v_numParams_1274_);
lean_dec(v_numParams_1274_);
lean_inc(v___x_1285_);
v_discrs_1298_ = l_Array_toSubarray___redArg(v_args_1282_, v___x_1283_, v___x_1285_);
v___x_1299_ = lean_nat_add(v_numIndices_1275_, v___x_1280_);
lean_dec(v_numIndices_1275_);
v___x_1300_ = lean_box(0);
v_discrInfos_1301_ = lean_mk_array(v___x_1299_, v___x_1300_);
lean_inc(v___x_1287_);
v_alts_1302_ = l_Array_toSubarray___redArg(v_args_1282_, v___x_1285_, v___x_1287_);
v___x_1352_ = lean_nat_dec_le(v___x_1287_, v___x_1294_);
if (v___x_1352_ == 0)
{
v_lower_1344_ = v___x_1287_;
v_upper_1345_ = v___x_1288_;
goto v___jp_1343_;
}
else
{
lean_dec(v___x_1287_);
v_lower_1344_ = v___x_1294_;
v_upper_1345_ = v___x_1288_;
goto v___jp_1343_;
}
v___jp_1303_:
{
lean_object* v___x_1306_; size_t v_sz_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_array_mk(v_ctors_1276_);
v_sz_1307_ = lean_array_size(v___x_1306_);
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1307_, v___x_1308_, v___x_1306_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1334_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1334_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1334_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_start_1314_; lean_object* v_stop_1315_; lean_object* v_start_1316_; lean_object* v_stop_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v_start_1314_ = lean_ctor_get(v_params_1295_, 1);
lean_inc(v_start_1314_);
v_stop_1315_ = lean_ctor_get(v_params_1295_, 2);
lean_inc(v_stop_1315_);
v_start_1316_ = lean_ctor_get(v_discrs_1298_, 1);
lean_inc(v_start_1316_);
v_stop_1317_ = lean_ctor_get(v_discrs_1298_, 2);
lean_inc(v_stop_1317_);
v___x_1318_ = lean_nat_sub(v_stop_1315_, v_start_1314_);
lean_dec(v_start_1314_);
lean_dec(v_stop_1315_);
v___x_1319_ = lean_nat_sub(v_stop_1317_, v_start_1316_);
lean_dec(v_start_1316_);
lean_dec(v_stop_1317_);
v___x_1320_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1318_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
lean_ctor_set(v___x_1321_, 2, v_a_1310_);
lean_ctor_set(v___x_1321_, 3, v___y_1305_);
lean_ctor_set(v___x_1321_, 4, v_discrInfos_1301_);
lean_ctor_set(v___x_1321_, 5, v___x_1320_);
v___x_1322_ = lean_array_mk(v_us_1211_);
v___x_1323_ = l_Subarray_copy___redArg(v_params_1295_);
v___x_1324_ = l_Subarray_copy___redArg(v_discrs_1298_);
v___x_1325_ = l_Subarray_copy___redArg(v_alts_1302_);
v___x_1326_ = l_Subarray_copy___redArg(v___y_1304_);
v___x_1327_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1321_);
lean_ctor_set(v___x_1327_, 1, v_declName_1210_);
lean_ctor_set(v___x_1327_, 2, v___x_1322_);
lean_ctor_set(v___x_1327_, 3, v___x_1323_);
lean_ctor_set(v___x_1327_, 4, v_motive_1297_);
lean_ctor_set(v___x_1327_, 5, v___x_1324_);
lean_ctor_set(v___x_1327_, 6, v___x_1325_);
lean_ctor_set(v___x_1327_, 7, v___x_1326_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 1);
lean_ctor_set(v___x_1271_, 0, v___x_1327_);
v___x_1329_ = v___x_1271_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1329_);
v___x_1331_ = v___x_1312_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_alts_1302_);
lean_dec_ref(v_discrInfos_1301_);
lean_dec_ref(v_discrs_1298_);
lean_dec(v_motive_1297_);
lean_dec_ref(v_params_1295_);
lean_del_object(v___x_1271_);
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
v_a_1335_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1309_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1309_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
v___jp_1343_:
{
lean_object* v_levelParams_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_levelParams_1346_ = lean_ctor_get(v_toConstantVal_1273_, 1);
lean_inc(v_levelParams_1346_);
lean_dec_ref(v_toConstantVal_1273_);
v___x_1347_ = l_Array_toSubarray___redArg(v_args_1282_, v_lower_1344_, v_upper_1345_);
v___x_1348_ = l_List_lengthTR___redArg(v_levelParams_1346_);
lean_dec(v_levelParams_1346_);
v___x_1349_ = l_List_lengthTR___redArg(v_us_1211_);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
lean_dec(v___x_1349_);
lean_dec(v___x_1348_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1304_ = v___x_1347_;
v___y_1305_ = v___x_1351_;
goto v___jp_1303_;
}
else
{
v___y_1304_ = v___x_1347_;
v___y_1305_ = v___x_1300_;
goto v___jp_1303_;
}
}
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec(v_a_1265_);
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
lean_dec_ref(v_e_1192_);
v___x_1354_ = lean_box(0);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1354_);
v___x_1356_ = v___x_1267_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
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
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_us_1211_);
lean_dec(v_declName_1210_);
lean_dec_ref(v_e_1192_);
v_a_1359_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1264_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1264_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
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
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_e_1192_);
goto v___jp_1203_;
}
}
v___jp_1203_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1368_, lean_object* v_alsoCasesOn_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1379_; lean_object* v_res_1380_; 
v_alsoCasesOn_boxed_1379_ = lean_unbox(v_alsoCasesOn_1369_);
v_res_1380_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1368_, v_alsoCasesOn_boxed_1379_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec(v___y_1370_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v_b_1386_, lean_object* v_c_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1384_);
lean_inc(v___y_1383_);
lean_inc(v___y_1382_);
v___x_1393_ = lean_apply_11(v_k_1381_, v_b_1386_, v_c_1387_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, lean_box(0));
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v_b_1399_, lean_object* v_c_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v_b_1399_, v_c_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1407_, lean_object* v_maxFVars_1408_, lean_object* v_k_1409_, uint8_t v_cleanupAnnotations_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___f_1420_; uint8_t v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v___y_1412_);
lean_inc(v___y_1411_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1420_, 0, v_k_1409_);
lean_closure_set(v___f_1420_, 1, v___y_1411_);
lean_closure_set(v___f_1420_, 2, v___y_1412_);
lean_closure_set(v___f_1420_, 3, v___y_1413_);
lean_closure_set(v___f_1420_, 4, v___y_1414_);
v___x_1421_ = 1;
v___x_1422_ = 0;
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_maxFVars_1408_);
v___x_1424_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1407_, v___x_1421_, v___x_1422_, v___x_1421_, v___x_1422_, v___x_1423_, v___f_1420_, v_cleanupAnnotations_1410_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref_known(v___x_1423_, 1);
if (lean_obj_tag(v___x_1424_) == 0)
{
return v___x_1424_;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1433_, lean_object* v_maxFVars_1434_, lean_object* v_k_1435_, lean_object* v_cleanupAnnotations_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1446_; lean_object* v_res_1447_; 
v_cleanupAnnotations_boxed_1446_ = lean_unbox(v_cleanupAnnotations_1436_);
v_res_1447_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1433_, v_maxFVars_1434_, v_k_1435_, v_cleanupAnnotations_boxed_1446_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec(v___y_1437_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v___y_1450_);
lean_inc(v___y_1449_);
v___x_1459_ = lean_apply_10(v_k_1448_, v_b_1453_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, lean_box(0));
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v_b_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v_b_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1472_, lean_object* v_type_1473_, lean_object* v_val_1474_, lean_object* v_k_1475_, uint8_t v_nondep_1476_, uint8_t v_kind_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; 
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc(v___y_1478_);
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1487_, 0, v_k_1475_);
lean_closure_set(v___f_1487_, 1, v___y_1478_);
lean_closure_set(v___f_1487_, 2, v___y_1479_);
lean_closure_set(v___f_1487_, 3, v___y_1480_);
lean_closure_set(v___f_1487_, 4, v___y_1481_);
v___x_1488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1472_, v_type_1473_, v_val_1474_, v___f_1487_, v_nondep_1476_, v_kind_1477_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1488_) == 0)
{
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1497_, lean_object* v_type_1498_, lean_object* v_val_1499_, lean_object* v_k_1500_, lean_object* v_nondep_1501_, lean_object* v_kind_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_nondep_boxed_1512_; uint8_t v_kind_boxed_1513_; lean_object* v_res_1514_; 
v_nondep_boxed_1512_ = lean_unbox(v_nondep_1501_);
v_kind_boxed_1513_ = lean_unbox(v_kind_1502_);
v_res_1514_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1497_, v_type_1498_, v_val_1499_, v_k_1500_, v_nondep_boxed_1512_, v_kind_boxed_1513_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec(v___y_1503_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1515_, uint8_t v_usedLetOnly_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; 
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1522_);
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v_x_1517_);
v___x_1527_ = lean_apply_10(v_k_1515_, v_x_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, lean_box(0));
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_mk_empty_array_with_capacity(v___x_1529_);
v___x_1531_ = lean_array_push(v___x_1530_, v_x_1517_);
v___x_1532_ = 0;
v___x_1533_ = 1;
v___x_1534_ = l_Lean_Meta_mkLetFVars(v___x_1531_, v_a_1528_, v_usedLetOnly_1516_, v___x_1532_, v___x_1533_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec_ref(v___x_1531_);
return v___x_1534_;
}
else
{
lean_dec_ref(v_x_1517_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1535_, lean_object* v_usedLetOnly_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_usedLetOnly_boxed_1547_; lean_object* v_res_1548_; 
v_usedLetOnly_boxed_1547_ = lean_unbox(v_usedLetOnly_1536_);
v_res_1548_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1535_, v_usedLetOnly_boxed_1547_, v_x_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1549_, lean_object* v_type_1550_, lean_object* v_val_1551_, lean_object* v_k_1552_, uint8_t v_nondep_1553_, uint8_t v_kind_1554_, uint8_t v_usedLetOnly_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(v_usedLetOnly_1555_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1566_, 0, v_k_1552_);
lean_closure_set(v___f_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1549_, v_type_1550_, v_val_1551_, v___f_1566_, v_nondep_1553_, v_kind_1554_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1568_, lean_object* v_type_1569_, lean_object* v_val_1570_, lean_object* v_k_1571_, lean_object* v_nondep_1572_, lean_object* v_kind_1573_, lean_object* v_usedLetOnly_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v_nondep_boxed_1584_; uint8_t v_kind_boxed_1585_; uint8_t v_usedLetOnly_boxed_1586_; lean_object* v_res_1587_; 
v_nondep_boxed_1584_ = lean_unbox(v_nondep_1572_);
v_kind_boxed_1585_ = lean_unbox(v_kind_1573_);
v_usedLetOnly_boxed_1586_ = lean_unbox(v_usedLetOnly_1574_);
v_res_1587_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1568_, v_type_1569_, v_val_1570_, v_k_1571_, v_nondep_boxed_1584_, v_kind_boxed_1585_, v_usedLetOnly_boxed_1586_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec(v___y_1575_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1588_, uint8_t v_bi_1589_, lean_object* v_type_1590_, lean_object* v_k_1591_, uint8_t v_kind_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; 
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc(v___y_1594_);
lean_inc(v___y_1593_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1602_, 0, v_k_1591_);
lean_closure_set(v___f_1602_, 1, v___y_1593_);
lean_closure_set(v___f_1602_, 2, v___y_1594_);
lean_closure_set(v___f_1602_, 3, v___y_1595_);
lean_closure_set(v___f_1602_, 4, v___y_1596_);
v___x_1603_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1588_, v_bi_1589_, v_type_1590_, v___f_1602_, v_kind_1592_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
return v___x_1603_;
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1612_, lean_object* v_bi_1613_, lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v_kind_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_bi_boxed_1626_; uint8_t v_kind_boxed_1627_; lean_object* v_res_1628_; 
v_bi_boxed_1626_ = lean_unbox(v_bi_1613_);
v_kind_boxed_1627_ = lean_unbox(v_kind_1616_);
v_res_1628_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1612_, v_bi_boxed_1626_, v_type_1614_, v_k_1615_, v_kind_boxed_1627_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc(v___y_1630_);
v___x_1639_ = lean_apply_9(v_k_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, lean_box(0));
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1651_, uint8_t v_allowLevelAssignments_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___f_1662_; lean_object* v___x_1663_; 
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc(v___y_1653_);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1662_, 0, v_k_1651_);
lean_closure_set(v___f_1662_, 1, v___y_1653_);
lean_closure_set(v___f_1662_, 2, v___y_1654_);
lean_closure_set(v___f_1662_, 3, v___y_1655_);
lean_closure_set(v___f_1662_, 4, v___y_1656_);
v___x_1663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1652_, v___f_1662_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1663_) == 0)
{
return v___x_1663_;
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1672_, lean_object* v_allowLevelAssignments_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1683_; lean_object* v_res_1684_; 
v_allowLevelAssignments_boxed_1683_ = lean_unbox(v_allowLevelAssignments_1673_);
v_res_1684_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1672_, v_allowLevelAssignments_boxed_1683_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec(v___y_1674_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1685_, lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_box(0);
return v___x_1687_;
}
else
{
lean_object* v_key_1688_; lean_object* v_value_1689_; lean_object* v_tail_1690_; uint8_t v___x_1691_; 
v_key_1688_ = lean_ctor_get(v_x_1686_, 0);
v_value_1689_ = lean_ctor_get(v_x_1686_, 1);
v_tail_1690_ = lean_ctor_get(v_x_1686_, 2);
v___x_1691_ = lean_expr_eqv(v_key_1688_, v_a_1685_);
if (v___x_1691_ == 0)
{
v_x_1686_ = v_tail_1690_;
goto _start;
}
else
{
lean_object* v___x_1693_; 
lean_inc(v_value_1689_);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_value_1689_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1694_, v_x_1695_);
lean_dec(v_x_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_buckets_1699_; lean_object* v___x_1700_; uint64_t v___x_1701_; uint64_t v___x_1702_; uint64_t v___x_1703_; uint64_t v_fold_1704_; uint64_t v___x_1705_; uint64_t v___x_1706_; uint64_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_buckets_1699_ = lean_ctor_get(v_m_1697_, 1);
v___x_1700_ = lean_array_get_size(v_buckets_1699_);
v___x_1701_ = l_Lean_Expr_hash(v_a_1698_);
v___x_1702_ = 32ULL;
v___x_1703_ = lean_uint64_shift_right(v___x_1701_, v___x_1702_);
v_fold_1704_ = lean_uint64_xor(v___x_1701_, v___x_1703_);
v___x_1705_ = 16ULL;
v___x_1706_ = lean_uint64_shift_right(v_fold_1704_, v___x_1705_);
v___x_1707_ = lean_uint64_xor(v_fold_1704_, v___x_1706_);
v___x_1708_ = lean_uint64_to_usize(v___x_1707_);
v___x_1709_ = lean_usize_of_nat(v___x_1700_);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_sub(v___x_1709_, v___x_1710_);
v___x_1712_ = lean_usize_land(v___x_1708_, v___x_1711_);
v___x_1713_ = lean_array_uget_borrowed(v_buckets_1699_, v___x_1712_);
v___x_1714_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1698_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1715_, v_a_1716_);
lean_dec_ref(v_a_1716_);
lean_dec_ref(v_m_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1718_, lean_object* v_opt_1719_){
_start:
{
lean_object* v_name_1720_; lean_object* v_defValue_1721_; lean_object* v_map_1722_; lean_object* v___x_1723_; 
v_name_1720_ = lean_ctor_get(v_opt_1719_, 0);
v_defValue_1721_ = lean_ctor_get(v_opt_1719_, 1);
v_map_1722_ = lean_ctor_get(v_opts_1718_, 0);
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1722_, v_name_1720_);
if (lean_obj_tag(v___x_1723_) == 0)
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_unbox(v_defValue_1721_);
return v___x_1724_;
}
else
{
lean_object* v_val_1725_; 
v_val_1725_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v___x_1723_, 1);
if (lean_obj_tag(v_val_1725_) == 1)
{
uint8_t v_v_1726_; 
v_v_1726_ = lean_ctor_get_uint8(v_val_1725_, 0);
lean_dec_ref_known(v_val_1725_, 0);
return v_v_1726_;
}
else
{
uint8_t v___x_1727_; 
lean_dec(v_val_1725_);
v___x_1727_ = lean_unbox(v_defValue_1721_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1728_, lean_object* v_opt_1729_){
_start:
{
uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_res_1730_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1728_, v_opt_1729_);
lean_dec_ref(v_opt_1729_);
lean_dec_ref(v_opts_1728_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1732_, lean_object* v_b_1733_){
_start:
{
lean_object* v_array_1734_; lean_object* v_start_1735_; lean_object* v_stop_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1749_; 
v_array_1734_ = lean_ctor_get(v_a_1732_, 0);
v_start_1735_ = lean_ctor_get(v_a_1732_, 1);
v_stop_1736_ = lean_ctor_get(v_a_1732_, 2);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1732_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1738_ = v_a_1732_;
v_isShared_1739_ = v_isSharedCheck_1749_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_stop_1736_);
lean_inc(v_start_1735_);
lean_inc(v_array_1734_);
lean_dec(v_a_1732_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1749_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_lt(v_start_1735_, v_stop_1736_);
if (v___x_1740_ == 0)
{
lean_del_object(v___x_1738_);
lean_dec(v_stop_1736_);
lean_dec(v_start_1735_);
lean_dec_ref(v_array_1734_);
return v_b_1733_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_nat_add(v_start_1735_, v___x_1741_);
lean_inc_ref(v_array_1734_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___x_1742_);
v___x_1744_ = v___x_1738_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_array_1734_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_stop_1736_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_array_fget(v_array_1734_, v_start_1735_);
lean_dec(v_start_1735_);
lean_dec_ref(v_array_1734_);
v___x_1746_ = lean_array_push(v_b_1733_, v___x_1745_);
v_a_1732_ = v___x_1744_;
v_b_1733_ = v___x_1746_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1750_, lean_object* v_recFnName_1751_, lean_object* v_fixedPrefixSize_1752_, lean_object* v_F_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_expr_instantiate1(v_body_1750_, v_x_1754_);
v___x_1765_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1751_, v_fixedPrefixSize_1752_, v_F_1753_, v___x_1764_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_mk_empty_array_with_capacity(v___x_1767_);
v___x_1769_ = lean_array_push(v___x_1768_, v_x_1754_);
v___x_1770_ = 0;
v___x_1771_ = 1;
v___x_1772_ = 1;
v___x_1773_ = l_Lean_Meta_mkLambdaFVars(v___x_1769_, v_a_1766_, v___x_1770_, v___x_1771_, v___x_1770_, v___x_1771_, v___x_1772_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec_ref(v___x_1769_);
return v___x_1773_;
}
else
{
lean_dec_ref(v_x_1754_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1774_, lean_object* v_recFnName_1775_, lean_object* v_fixedPrefixSize_1776_, lean_object* v_F_1777_, lean_object* v_x_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1774_, v_recFnName_1775_, v_fixedPrefixSize_1776_, v_F_1777_, v_x_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_body_1774_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1789_, lean_object* v_recFnName_1790_, lean_object* v_fixedPrefixSize_1791_, lean_object* v_F_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_expr_instantiate1(v_body_1789_, v_x_1793_);
v___x_1804_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1790_, v_fixedPrefixSize_1791_, v_F_1792_, v___x_1803_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
v___x_1808_ = lean_array_push(v___x_1807_, v_x_1793_);
v___x_1809_ = 0;
v___x_1810_ = 1;
v___x_1811_ = 1;
v___x_1812_ = l_Lean_Meta_mkForallFVars(v___x_1808_, v_a_1805_, v___x_1809_, v___x_1810_, v___x_1810_, v___x_1811_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v___x_1808_);
return v___x_1812_;
}
else
{
lean_dec_ref(v_x_1793_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1813_, lean_object* v_recFnName_1814_, lean_object* v_fixedPrefixSize_1815_, lean_object* v_F_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1813_, v_recFnName_1814_, v_fixedPrefixSize_1815_, v_F_1816_, v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v_body_1813_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1828_, lean_object* v_recFnName_1829_, lean_object* v_fixedPrefixSize_1830_, lean_object* v_F_1831_, lean_object* v_x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1828_, v_recFnName_1829_, v_fixedPrefixSize_1830_, v_F_1831_, v_x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v_x_1832_);
lean_dec_ref(v_body_1828_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1845_, lean_object* v_fixedPrefixSize_1846_, lean_object* v_F_1847_, size_t v_sz_1848_, size_t v_i_1849_, lean_object* v_bs_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1849_, v_sz_1848_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_F_1847_);
lean_dec(v_fixedPrefixSize_1846_);
lean_dec(v_recFnName_1845_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_bs_1850_);
return v___x_1861_;
}
else
{
lean_object* v_v_1862_; lean_object* v___x_1863_; 
v_v_1862_ = lean_array_uget_borrowed(v_bs_1850_, v_i_1849_);
lean_inc(v_v_1862_);
lean_inc_ref(v_F_1847_);
lean_inc(v_fixedPrefixSize_1846_);
lean_inc(v_recFnName_1845_);
v___x_1863_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1845_, v_fixedPrefixSize_1846_, v_F_1847_, v_v_1862_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v_bs_x27_1866_; size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = lean_unsigned_to_nat(0u);
v_bs_x27_1866_ = lean_array_uset(v_bs_1850_, v_i_1849_, v___x_1865_);
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1849_, v___x_1867_);
v___x_1869_ = lean_array_uset(v_bs_x27_1866_, v_i_1849_, v_a_1864_);
v_i_1849_ = v___x_1868_;
v_bs_1850_ = v___x_1869_;
goto _start;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_bs_1850_);
lean_dec_ref(v_F_1847_);
lean_dec(v_fixedPrefixSize_1846_);
lean_dec(v_recFnName_1845_);
v_a_1871_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1863_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1863_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_cls_1886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1888_ = l_Lean_Name_append(v___x_1887_, v_cls_1886_);
return v___x_1888_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1891_ = l_Lean_stringToMessageData(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1892_, lean_object* v_fixedPrefixSize_1893_, lean_object* v_F_1894_, lean_object* v_e_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1917_ = l_Lean_Expr_getAppNumArgs(v_e_1895_);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_add(v_fixedPrefixSize_1893_, v___x_1918_);
v___x_1920_ = lean_nat_dec_lt(v___x_1917_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v_dummy_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_args_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_dummy_1921_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1917_);
v___x_1922_ = lean_mk_array(v___x_1917_, v_dummy_1921_);
v___x_1923_ = lean_nat_sub(v___x_1917_, v___x_1918_);
lean_dec(v___x_1917_);
v_args_1924_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1895_, v___x_1922_, v___x_1923_);
v___x_1925_ = l_Lean_instInhabitedExpr;
v___x_1926_ = lean_array_get(v___x_1925_, v_args_1924_, v_fixedPrefixSize_1893_);
lean_inc_ref(v_F_1894_);
lean_inc(v_fixedPrefixSize_1893_);
lean_inc(v_recFnName_1892_);
v___x_1927_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1892_, v_fixedPrefixSize_1893_, v_F_1894_, v___x_1926_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
lean_inc_ref(v_F_1894_);
v___x_1929_ = l_Lean_Expr_app___override(v_F_1894_, v_a_1928_);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc_ref(v___x_1929_);
v___x_1930_ = lean_infer_type(v___x_1929_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
v___x_1932_ = lean_whnf(v_a_1931_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = l_Lean_Expr_bindingDomain_x21(v_a_1933_);
lean_dec(v_a_1933_);
v___x_1935_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1934_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v_lower_1939_; lean_object* v_upper_1940_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l_Lean_Expr_app___override(v___x_1929_, v_a_1936_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_array_get_size(v_args_1924_);
v___x_1966_ = lean_nat_dec_le(v___x_1919_, v___x_1964_);
if (v___x_1966_ == 0)
{
v_lower_1939_ = v___x_1919_;
v_upper_1940_ = v___x_1965_;
goto v___jp_1938_;
}
else
{
lean_dec(v___x_1919_);
v_lower_1939_ = v___x_1964_;
v_upper_1940_ = v___x_1965_;
goto v___jp_1938_;
}
v___jp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; size_t v_sz_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1941_ = l_Array_toSubarray___redArg(v_args_1924_, v_lower_1939_, v_upper_1940_);
v___x_1942_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1943_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1941_, v___x_1942_);
v_sz_1944_ = lean_array_size(v___x_1943_);
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1892_, v_fixedPrefixSize_1893_, v_F_1894_, v_sz_1944_, v___x_1945_, v___x_1943_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = l_Lean_mkAppN(v___x_1937_, v_a_1947_);
lean_dec(v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___x_1937_);
v_a_1956_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_args_1924_);
lean_dec(v___x_1919_);
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
return v___x_1935_;
}
}
else
{
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_args_1924_);
lean_dec(v___x_1919_);
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
return v___x_1932_;
}
}
else
{
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_args_1924_);
lean_dec(v___x_1919_);
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
return v___x_1930_;
}
}
else
{
lean_dec_ref(v_args_1924_);
lean_dec(v___x_1919_);
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
return v___x_1927_;
}
}
else
{
lean_object* v_options_1967_; uint8_t v_hasTrace_1968_; 
lean_dec(v___x_1919_);
lean_dec(v___x_1917_);
v_options_1967_ = lean_ctor_get(v_a_1902_, 2);
v_hasTrace_1968_ = lean_ctor_get_uint8(v_options_1967_, sizeof(void*)*1);
if (v_hasTrace_1968_ == 0)
{
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
goto v___jp_1905_;
}
else
{
lean_object* v_inheritedTraceOptions_1969_; lean_object* v_cls_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_inheritedTraceOptions_1969_ = lean_ctor_get(v_a_1902_, 13);
v_cls_1970_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1971_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1972_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1969_, v_options_1967_, v___x_1971_);
if (v___x_1972_ == 0)
{
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1973_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1895_);
v___x_1974_ = l_Lean_indentExpr(v_e_1895_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1970_, v___x_1975_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_dec_ref_known(v___x_1976_, 1);
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
}
v___jp_1905_:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Meta_etaExpand(v_e_1895_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1892_, v_fixedPrefixSize_1893_, v_F_1894_, v_a_1915_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1916_;
}
else
{
lean_dec_ref(v_F_1894_);
lean_dec(v_fixedPrefixSize_1893_);
lean_dec(v_recFnName_1892_);
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1985_, lean_object* v_fixedPrefixSize_1986_, lean_object* v_F_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 5)
{
lean_object* v_fn_2000_; lean_object* v_arg_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_fn_2000_ = lean_ctor_get(v_x_1988_, 0);
lean_inc_ref(v_fn_2000_);
v_arg_2001_ = lean_ctor_get(v_x_1988_, 1);
lean_inc_ref(v_arg_2001_);
lean_dec_ref_known(v_x_1988_, 2);
v___x_2002_ = lean_array_set(v_x_1989_, v_x_1990_, v_arg_2001_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_sub(v_x_1990_, v___x_2003_);
lean_dec(v_x_1990_);
v_x_1988_ = v_fn_2000_;
v_x_1989_ = v___x_2002_;
v_x_1990_ = v___x_2004_;
goto _start;
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_x_1990_);
lean_inc_ref(v_F_1987_);
lean_inc(v_fixedPrefixSize_1986_);
lean_inc(v_recFnName_1985_);
v___x_2006_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1985_, v_fixedPrefixSize_1986_, v_F_1987_, v_x_1988_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_sz_2008_ = lean_array_size(v_x_1989_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1985_, v_fixedPrefixSize_1986_, v_F_1987_, v_sz_2008_, v___x_2009_, v_x_1989_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = l_Lean_mkAppN(v_a_2007_, v_a_2011_);
lean_dec(v_a_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_a_2007_);
v_a_2020_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2010_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2010_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_dec_ref(v_x_1989_);
lean_dec_ref(v_F_1987_);
lean_dec(v_fixedPrefixSize_1986_);
lean_dec(v_recFnName_1985_);
return v___x_2006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2028_, lean_object* v_fixedPrefixSize_2029_, lean_object* v_F_2030_, lean_object* v_e_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_isAppOf(v_e_2031_, v_recFnName_2028_);
if (v___x_2041_ == 0)
{
lean_object* v_dummy_2042_; lean_object* v_nargs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_dummy_2042_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2043_ = l_Lean_Expr_getAppNumArgs(v_e_2031_);
lean_inc(v_nargs_2043_);
v___x_2044_ = lean_mk_array(v_nargs_2043_, v_dummy_2042_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v_nargs_2043_, v___x_2045_);
lean_dec(v_nargs_2043_);
v___x_2047_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2028_, v_fixedPrefixSize_2029_, v_F_2030_, v_e_2031_, v___x_2044_, v___x_2046_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2028_, v_fixedPrefixSize_2029_, v_F_2030_, v_e_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
return v___x_2048_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2055_, lean_object* v_b_2056_, lean_object* v_recFnName_2057_, lean_object* v_fixedPrefixSize_2058_, uint8_t v___x_2059_, lean_object* v___x_2060_, lean_object* v_a_2061_, lean_object* v_e_2062_, lean_object* v_xs_2063_, lean_object* v_altBody_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = lean_array_get_size(v_xs_2063_);
v___x_2082_ = lean_nat_dec_eq(v___x_2081_, v___x_2060_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_altBody_2064_);
lean_dec(v_fixedPrefixSize_2058_);
lean_dec(v_recFnName_2057_);
v___x_2083_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2084_ = l_Lean_indentExpr(v_a_2061_);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_indentExpr(v_e_2062_);
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2089_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_dec_ref(v_e_2062_);
lean_dec_ref(v_a_2061_);
goto v___jp_2074_;
}
v___jp_2074_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_array_get_borrowed(v___x_2055_, v_xs_2063_, v_b_2056_);
lean_inc(v___x_2075_);
v___x_2076_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2057_, v_fixedPrefixSize_2058_, v___x_2075_, v_altBody_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = 0;
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Meta_mkLambdaFVars(v_xs_2063_, v_a_2077_, v___x_2078_, v___x_2059_, v___x_2078_, v___x_2059_, v___x_2079_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2080_;
}
else
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2099_ = _args[0];
lean_object* v_b_2100_ = _args[1];
lean_object* v_recFnName_2101_ = _args[2];
lean_object* v_fixedPrefixSize_2102_ = _args[3];
lean_object* v___x_2103_ = _args[4];
lean_object* v___x_2104_ = _args[5];
lean_object* v_a_2105_ = _args[6];
lean_object* v_e_2106_ = _args[7];
lean_object* v_xs_2107_ = _args[8];
lean_object* v_altBody_2108_ = _args[9];
lean_object* v___y_2109_ = _args[10];
lean_object* v___y_2110_ = _args[11];
lean_object* v___y_2111_ = _args[12];
lean_object* v___y_2112_ = _args[13];
lean_object* v___y_2113_ = _args[14];
lean_object* v___y_2114_ = _args[15];
lean_object* v___y_2115_ = _args[16];
lean_object* v___y_2116_ = _args[17];
lean_object* v___y_2117_ = _args[18];
_start:
{
uint8_t v___x_66760__boxed_2118_; lean_object* v_res_2119_; 
v___x_66760__boxed_2118_ = lean_unbox(v___x_2103_);
v_res_2119_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2099_, v_b_2100_, v_recFnName_2101_, v_fixedPrefixSize_2102_, v___x_66760__boxed_2118_, v___x_2104_, v_a_2105_, v_e_2106_, v_xs_2107_, v_altBody_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v_xs_2107_);
lean_dec(v___x_2104_);
lean_dec(v_b_2100_);
lean_dec_ref(v___x_2099_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2120_, lean_object* v_fixedPrefixSize_2121_, lean_object* v_e_2122_, lean_object* v_as_2123_, lean_object* v_bs_2124_, lean_object* v_i_2125_, lean_object* v_cs_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_array_get_size(v_as_2123_);
v___x_2137_ = lean_nat_dec_lt(v_i_2125_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_i_2125_);
lean_dec_ref(v_e_2122_);
lean_dec(v_fixedPrefixSize_2121_);
lean_dec(v_recFnName_2120_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_cs_2126_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = lean_array_get_size(v_bs_2124_);
v___x_2140_ = lean_nat_dec_lt(v_i_2125_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_i_2125_);
lean_dec_ref(v_e_2122_);
lean_dec(v_fixedPrefixSize_2121_);
lean_dec(v_recFnName_2120_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_cs_2126_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v_a_2143_; lean_object* v_b_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2142_ = l_Lean_instInhabitedExpr;
v_a_2143_ = lean_array_fget_borrowed(v_as_2123_, v_i_2125_);
v_b_2144_ = lean_array_fget_borrowed(v_bs_2124_, v_i_2125_);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_b_2144_, v___x_2145_);
v___x_2147_ = lean_box(v___x_2140_);
lean_inc_ref(v_e_2122_);
lean_inc_n(v_a_2143_, 2);
lean_inc(v___x_2146_);
lean_inc(v_fixedPrefixSize_2121_);
lean_inc(v_recFnName_2120_);
lean_inc(v_b_2144_);
v___f_2148_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2148_, 0, v___x_2142_);
lean_closure_set(v___f_2148_, 1, v_b_2144_);
lean_closure_set(v___f_2148_, 2, v_recFnName_2120_);
lean_closure_set(v___f_2148_, 3, v_fixedPrefixSize_2121_);
lean_closure_set(v___f_2148_, 4, v___x_2147_);
lean_closure_set(v___f_2148_, 5, v___x_2146_);
lean_closure_set(v___f_2148_, 6, v_a_2143_);
lean_closure_set(v___f_2148_, 7, v_e_2122_);
v___x_2149_ = 0;
v___x_2150_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2143_, v___x_2146_, v___f_2148_, v___x_2149_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = lean_nat_add(v_i_2125_, v___x_2145_);
lean_dec(v_i_2125_);
v___x_2153_ = lean_array_push(v_cs_2126_, v_a_2151_);
v_i_2125_ = v___x_2152_;
v_cs_2126_ = v___x_2153_;
goto _start;
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_cs_2126_);
lean_dec(v_i_2125_);
lean_dec_ref(v_e_2122_);
lean_dec(v_fixedPrefixSize_2121_);
lean_dec(v_recFnName_2120_);
v_a_2155_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2150_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2150_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2163_, lean_object* v_fixedPrefixSize_2164_, lean_object* v_F_2165_, lean_object* v_e_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
switch(lean_obj_tag(v_e_2166_))
{
case 6:
{
lean_object* v_binderName_2176_; lean_object* v_binderType_2177_; lean_object* v_body_2178_; uint8_t v_binderInfo_2179_; lean_object* v___x_2180_; 
v_binderName_2176_ = lean_ctor_get(v_e_2166_, 0);
lean_inc(v_binderName_2176_);
v_binderType_2177_ = lean_ctor_get(v_e_2166_, 1);
lean_inc_ref(v_binderType_2177_);
v_body_2178_ = lean_ctor_get(v_e_2166_, 2);
lean_inc_ref(v_body_2178_);
v_binderInfo_2179_ = lean_ctor_get_uint8(v_e_2166_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2166_, 3);
lean_inc_ref(v_F_2165_);
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
v___x_2180_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_binderType_2177_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___f_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2182_, 0, v_body_2178_);
lean_closure_set(v___f_2182_, 1, v_recFnName_2163_);
lean_closure_set(v___f_2182_, 2, v_fixedPrefixSize_2164_);
lean_closure_set(v___f_2182_, 3, v_F_2165_);
v___x_2183_ = 0;
v___x_2184_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2176_, v_binderInfo_2179_, v_a_2181_, v___f_2182_, v___x_2183_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2184_;
}
else
{
lean_dec_ref(v_body_2178_);
lean_dec(v_binderName_2176_);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
return v___x_2180_;
}
}
case 7:
{
lean_object* v_binderName_2185_; lean_object* v_binderType_2186_; lean_object* v_body_2187_; uint8_t v_binderInfo_2188_; lean_object* v___x_2189_; 
v_binderName_2185_ = lean_ctor_get(v_e_2166_, 0);
lean_inc(v_binderName_2185_);
v_binderType_2186_ = lean_ctor_get(v_e_2166_, 1);
lean_inc_ref(v_binderType_2186_);
v_body_2187_ = lean_ctor_get(v_e_2166_, 2);
lean_inc_ref(v_body_2187_);
v_binderInfo_2188_ = lean_ctor_get_uint8(v_e_2166_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2166_, 3);
lean_inc_ref(v_F_2165_);
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
v___x_2189_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_binderType_2186_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___f_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2191_, 0, v_body_2187_);
lean_closure_set(v___f_2191_, 1, v_recFnName_2163_);
lean_closure_set(v___f_2191_, 2, v_fixedPrefixSize_2164_);
lean_closure_set(v___f_2191_, 3, v_F_2165_);
v___x_2192_ = 0;
v___x_2193_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2185_, v_binderInfo_2188_, v_a_2190_, v___f_2191_, v___x_2192_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2193_;
}
else
{
lean_dec_ref(v_body_2187_);
lean_dec(v_binderName_2185_);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
return v___x_2189_;
}
}
case 8:
{
lean_object* v_declName_2194_; lean_object* v_type_2195_; lean_object* v_value_2196_; lean_object* v_body_2197_; uint8_t v_nondep_2198_; lean_object* v___x_2199_; 
v_declName_2194_ = lean_ctor_get(v_e_2166_, 0);
lean_inc(v_declName_2194_);
v_type_2195_ = lean_ctor_get(v_e_2166_, 1);
lean_inc_ref(v_type_2195_);
v_value_2196_ = lean_ctor_get(v_e_2166_, 2);
lean_inc_ref(v_value_2196_);
v_body_2197_ = lean_ctor_get(v_e_2166_, 3);
lean_inc_ref(v_body_2197_);
v_nondep_2198_ = lean_ctor_get_uint8(v_e_2166_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2166_, 4);
lean_inc_ref(v_F_2165_);
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
v___x_2199_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_type_2195_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
lean_inc_ref(v_F_2165_);
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
v___x_2201_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_value_2196_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___f_2203_; uint8_t v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2203_, 0, v_body_2197_);
lean_closure_set(v___f_2203_, 1, v_recFnName_2163_);
lean_closure_set(v___f_2203_, 2, v_fixedPrefixSize_2164_);
lean_closure_set(v___f_2203_, 3, v_F_2165_);
v___x_2204_ = 0;
v___x_2205_ = 0;
v___x_2206_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2194_, v_a_2200_, v_a_2202_, v___f_2203_, v_nondep_2198_, v___x_2204_, v___x_2205_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2206_;
}
else
{
lean_dec(v_a_2200_);
lean_dec_ref(v_body_2197_);
lean_dec(v_declName_2194_);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
return v___x_2201_;
}
}
else
{
lean_dec_ref(v_body_2197_);
lean_dec_ref(v_value_2196_);
lean_dec(v_declName_2194_);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
return v___x_2199_;
}
}
case 10:
{
lean_object* v_data_2207_; lean_object* v_expr_2208_; lean_object* v___x_2209_; 
v_data_2207_ = lean_ctor_get(v_e_2166_, 0);
lean_inc(v_data_2207_);
v_expr_2208_ = lean_ctor_get(v_e_2166_, 1);
lean_inc_ref(v_expr_2208_);
v___x_2209_ = l_Lean_getRecAppSyntax_x3f(v_e_2166_);
lean_dec_ref_known(v_e_2166_, 2);
if (lean_obj_tag(v___x_2209_) == 1)
{
lean_object* v_val_2210_; lean_object* v_fileName_2211_; lean_object* v_fileMap_2212_; lean_object* v_options_2213_; lean_object* v_currRecDepth_2214_; lean_object* v_maxRecDepth_2215_; lean_object* v_ref_2216_; lean_object* v_currNamespace_2217_; lean_object* v_openDecls_2218_; lean_object* v_initHeartbeats_2219_; lean_object* v_maxHeartbeats_2220_; lean_object* v_quotContext_2221_; lean_object* v_currMacroScope_2222_; uint8_t v_diag_2223_; lean_object* v_cancelTk_x3f_2224_; uint8_t v_suppressElabErrors_2225_; lean_object* v_inheritedTraceOptions_2226_; lean_object* v_ref_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v_data_2207_);
v_val_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v_fileName_2211_ = lean_ctor_get(v_a_2173_, 0);
v_fileMap_2212_ = lean_ctor_get(v_a_2173_, 1);
v_options_2213_ = lean_ctor_get(v_a_2173_, 2);
v_currRecDepth_2214_ = lean_ctor_get(v_a_2173_, 3);
v_maxRecDepth_2215_ = lean_ctor_get(v_a_2173_, 4);
v_ref_2216_ = lean_ctor_get(v_a_2173_, 5);
v_currNamespace_2217_ = lean_ctor_get(v_a_2173_, 6);
v_openDecls_2218_ = lean_ctor_get(v_a_2173_, 7);
v_initHeartbeats_2219_ = lean_ctor_get(v_a_2173_, 8);
v_maxHeartbeats_2220_ = lean_ctor_get(v_a_2173_, 9);
v_quotContext_2221_ = lean_ctor_get(v_a_2173_, 10);
v_currMacroScope_2222_ = lean_ctor_get(v_a_2173_, 11);
v_diag_2223_ = lean_ctor_get_uint8(v_a_2173_, sizeof(void*)*14);
v_cancelTk_x3f_2224_ = lean_ctor_get(v_a_2173_, 12);
v_suppressElabErrors_2225_ = lean_ctor_get_uint8(v_a_2173_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2226_ = lean_ctor_get(v_a_2173_, 13);
v_ref_2227_ = l_Lean_replaceRef(v_val_2210_, v_ref_2216_);
lean_dec(v_val_2210_);
lean_inc_ref(v_inheritedTraceOptions_2226_);
lean_inc(v_cancelTk_x3f_2224_);
lean_inc(v_currMacroScope_2222_);
lean_inc(v_quotContext_2221_);
lean_inc(v_maxHeartbeats_2220_);
lean_inc(v_initHeartbeats_2219_);
lean_inc(v_openDecls_2218_);
lean_inc(v_currNamespace_2217_);
lean_inc(v_maxRecDepth_2215_);
lean_inc(v_currRecDepth_2214_);
lean_inc_ref(v_options_2213_);
lean_inc_ref(v_fileMap_2212_);
lean_inc_ref(v_fileName_2211_);
v___x_2228_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2228_, 0, v_fileName_2211_);
lean_ctor_set(v___x_2228_, 1, v_fileMap_2212_);
lean_ctor_set(v___x_2228_, 2, v_options_2213_);
lean_ctor_set(v___x_2228_, 3, v_currRecDepth_2214_);
lean_ctor_set(v___x_2228_, 4, v_maxRecDepth_2215_);
lean_ctor_set(v___x_2228_, 5, v_ref_2227_);
lean_ctor_set(v___x_2228_, 6, v_currNamespace_2217_);
lean_ctor_set(v___x_2228_, 7, v_openDecls_2218_);
lean_ctor_set(v___x_2228_, 8, v_initHeartbeats_2219_);
lean_ctor_set(v___x_2228_, 9, v_maxHeartbeats_2220_);
lean_ctor_set(v___x_2228_, 10, v_quotContext_2221_);
lean_ctor_set(v___x_2228_, 11, v_currMacroScope_2222_);
lean_ctor_set(v___x_2228_, 12, v_cancelTk_x3f_2224_);
lean_ctor_set(v___x_2228_, 13, v_inheritedTraceOptions_2226_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*14, v_diag_2223_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*14 + 1, v_suppressElabErrors_2225_);
v___x_2229_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_expr_2208_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v___x_2228_, v_a_2174_);
lean_dec_ref_known(v___x_2228_, 14);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; 
lean_dec(v___x_2209_);
v___x_2230_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_expr_2208_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2239_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = l_Lean_mkMData(v_data_2207_, v_a_2231_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2235_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
else
{
lean_dec(v_data_2207_);
return v___x_2230_;
}
}
}
case 11:
{
lean_object* v_typeName_2240_; lean_object* v_idx_2241_; lean_object* v_struct_2242_; lean_object* v___x_2243_; 
v_typeName_2240_ = lean_ctor_get(v_e_2166_, 0);
lean_inc(v_typeName_2240_);
v_idx_2241_ = lean_ctor_get(v_e_2166_, 1);
lean_inc(v_idx_2241_);
v_struct_2242_ = lean_ctor_get(v_e_2166_, 2);
lean_inc_ref(v_struct_2242_);
lean_dec_ref_known(v_e_2166_, 3);
v___x_2243_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_struct_2242_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2252_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = l_Lean_mkProj(v_typeName_2240_, v_idx_2241_, v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_dec(v_idx_2241_);
lean_dec(v_typeName_2240_);
return v___x_2243_;
}
}
case 4:
{
uint8_t v___x_2253_; 
v___x_2253_ = l_Lean_Expr_isConstOf(v_e_2166_, v_recFnName_2163_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_e_2166_);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_e_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2255_;
}
}
case 5:
{
uint8_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = 1;
lean_inc_ref(v_e_2166_);
v___x_2257_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2166_, v___x_2256_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
if (lean_obj_tag(v_a_2258_) == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_e_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2259_;
}
else
{
lean_object* v_val_2260_; lean_object* v___x_2261_; 
v_val_2260_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v_a_2258_, 1);
lean_inc_ref(v_F_2165_);
v___x_2261_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2260_, v_F_2165_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
if (lean_obj_tag(v_a_2262_) == 1)
{
lean_object* v_val_2263_; lean_object* v_toMatcherInfo_2264_; lean_object* v_matcherName_2265_; lean_object* v_matcherLevels_2266_; lean_object* v_params_2267_; lean_object* v_motive_2268_; lean_object* v_discrs_2269_; lean_object* v_alts_2270_; lean_object* v_remaining_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_val_2263_ = lean_ctor_get(v_a_2262_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v_a_2262_, 1);
v_toMatcherInfo_2264_ = lean_ctor_get(v_val_2263_, 0);
lean_inc_ref(v_toMatcherInfo_2264_);
v_matcherName_2265_ = lean_ctor_get(v_val_2263_, 1);
lean_inc(v_matcherName_2265_);
v_matcherLevels_2266_ = lean_ctor_get(v_val_2263_, 2);
lean_inc_ref(v_matcherLevels_2266_);
v_params_2267_ = lean_ctor_get(v_val_2263_, 3);
lean_inc_ref(v_params_2267_);
v_motive_2268_ = lean_ctor_get(v_val_2263_, 4);
lean_inc_ref(v_motive_2268_);
v_discrs_2269_ = lean_ctor_get(v_val_2263_, 5);
lean_inc_ref(v_discrs_2269_);
v_alts_2270_ = lean_ctor_get(v_val_2263_, 6);
lean_inc_ref(v_alts_2270_);
v_remaining_2271_ = lean_ctor_get(v_val_2263_, 7);
lean_inc_ref(v_remaining_2271_);
v___x_2272_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2263_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
v___x_2275_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_e_2166_, v_alts_2270_, v___x_2272_, v___x_2273_, v___x_2274_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec_ref(v___x_2272_);
lean_dec_ref(v_alts_2270_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; size_t v_sz_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v_sz_2277_ = lean_array_size(v_discrs_2269_);
v___x_2278_ = ((size_t)0ULL);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_sz_2277_, v___x_2278_, v_discrs_2269_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2289_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2284_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2284_, 0, v_toMatcherInfo_2264_);
lean_ctor_set(v___x_2284_, 1, v_matcherName_2265_);
lean_ctor_set(v___x_2284_, 2, v_matcherLevels_2266_);
lean_ctor_set(v___x_2284_, 3, v_params_2267_);
lean_ctor_set(v___x_2284_, 4, v_motive_2268_);
lean_ctor_set(v___x_2284_, 5, v_a_2280_);
lean_ctor_set(v___x_2284_, 6, v_a_2276_);
lean_ctor_set(v___x_2284_, 7, v_remaining_2271_);
v___x_2285_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2284_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2285_);
v___x_2287_ = v___x_2282_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2276_);
lean_dec_ref(v_remaining_2271_);
lean_dec_ref(v_motive_2268_);
lean_dec_ref(v_params_2267_);
lean_dec_ref(v_matcherLevels_2266_);
lean_dec(v_matcherName_2265_);
lean_dec_ref(v_toMatcherInfo_2264_);
v_a_2290_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2279_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2279_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_remaining_2271_);
lean_dec_ref(v_discrs_2269_);
lean_dec_ref(v_motive_2268_);
lean_dec_ref(v_params_2267_);
lean_dec_ref(v_matcherLevels_2266_);
lean_dec(v_matcherName_2265_);
lean_dec_ref(v_toMatcherInfo_2264_);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v_a_2298_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2275_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2275_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v___x_2306_; 
lean_dec(v_a_2262_);
v___x_2306_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2163_, v_fixedPrefixSize_2164_, v_F_2165_, v_e_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2306_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref_known(v_e_2166_, 2);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v_a_2307_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2261_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2261_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref_known(v_e_2166_, 2);
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v_a_2315_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2257_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2257_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
default: 
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_F_2165_);
lean_dec(v_fixedPrefixSize_2164_);
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_mk_empty_array_with_capacity(v___x_2323_);
v___x_2325_ = lean_array_push(v___x_2324_, v_recFnName_2163_);
lean_inc_ref(v_e_2166_);
v___x_2326_ = l_Lean_Elab_ensureNoRecFn(v___x_2325_, v_e_2166_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v___x_2326_, 0);
lean_dec(v_unused_2334_);
v___x_2328_ = v___x_2326_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v___x_2326_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_e_2166_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_e_2166_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_e_2166_);
v_a_2335_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2326_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2326_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0(void){
_start:
{
uint8_t v___x_2343_; uint64_t v___x_2344_; 
v___x_2343_ = 0;
v___x_2344_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2345_, lean_object* v_fixedPrefixSize_2346_, lean_object* v_F_2347_, lean_object* v_e_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2358_; 
lean_inc_ref(v_e_2348_);
lean_inc(v_recFnName_2345_);
v___x_2358_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2345_, v_e_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2497_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2497_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2497_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
uint8_t v___x_2363_; uint8_t v___x_2364_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; 
v___x_2363_ = lean_unbox(v_a_2359_);
lean_dec(v_a_2359_);
v___x_2364_ = lean_bool_not(v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_del_object(v___x_2361_);
v___x_2471_ = lean_st_ref_get(v_a_2350_);
v___x_2472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2471_, v_e_2348_);
lean_dec(v___x_2471_);
if (lean_obj_tag(v___x_2472_) == 1)
{
lean_object* v_val_2473_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; 
v_val_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_val_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v_fst_2474_ = lean_ctor_get(v_val_2473_, 0);
lean_inc(v_fst_2474_);
v_snd_2475_ = lean_ctor_get(v_val_2473_, 1);
lean_inc(v_snd_2475_);
lean_dec(v_val_2473_);
v___x_2476_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2475_, v_a_2353_);
lean_dec(v_snd_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2485_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
if (v___x_2481_ == 0)
{
lean_del_object(v___x_2479_);
lean_dec(v_fst_2474_);
v___y_2366_ = v_a_2349_;
v___y_2367_ = v_a_2350_;
v___y_2368_ = v_a_2351_;
v___y_2369_ = v_a_2352_;
v___y_2370_ = v_a_2353_;
v___y_2371_ = v_a_2354_;
v___y_2372_ = v_a_2355_;
v___y_2373_ = v_a_2356_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2483_; 
lean_dec_ref(v_e_2348_);
lean_dec_ref(v_F_2347_);
lean_dec(v_fixedPrefixSize_2346_);
lean_dec(v_recFnName_2345_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_fst_2474_);
v___x_2483_ = v___x_2479_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_fst_2474_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_fst_2474_);
lean_dec_ref(v_e_2348_);
lean_dec_ref(v_F_2347_);
lean_dec(v_fixedPrefixSize_2346_);
lean_dec(v_recFnName_2345_);
v_a_2486_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2476_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2476_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_dec(v___x_2472_);
v___y_2366_ = v_a_2349_;
v___y_2367_ = v_a_2350_;
v___y_2368_ = v_a_2351_;
v___y_2369_ = v_a_2352_;
v___y_2370_ = v_a_2353_;
v___y_2371_ = v_a_2354_;
v___y_2372_ = v_a_2355_;
v___y_2373_ = v_a_2356_;
goto v___jp_2365_;
}
}
else
{
lean_object* v___x_2495_; 
lean_dec_ref(v_F_2347_);
lean_dec(v_fixedPrefixSize_2346_);
lean_dec(v_recFnName_2345_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v_e_2348_);
v___x_2495_ = v___x_2361_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_e_2348_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
v___jp_2365_:
{
lean_object* v___x_2374_; 
lean_inc_ref(v_e_2348_);
v___x_2374_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2345_, v_fixedPrefixSize_2346_, v_F_2347_, v_e_2348_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2462_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2462_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2462_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_options_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2381_ = lean_st_ref_take(v___y_2367_);
lean_inc(v_a_2375_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_a_2375_);
lean_ctor_set(v___x_2382_, 1, v_a_2377_);
lean_inc_ref(v_e_2348_);
v___x_2383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2381_, v_e_2348_, v___x_2382_);
v___x_2384_ = lean_st_ref_set(v___y_2367_, v___x_2383_);
v_options_2385_ = lean_ctor_get(v___y_2372_, 2);
v___x_2386_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2387_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2389_; 
lean_dec_ref(v_e_2348_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v_a_2375_);
v___x_2389_ = v___x_2379_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2375_);
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
lean_object* v___x_2391_; uint8_t v_foApprox_2392_; uint8_t v_ctxApprox_2393_; uint8_t v_quasiPatternApprox_2394_; uint8_t v_constApprox_2395_; uint8_t v_isDefEqStuckEx_2396_; uint8_t v_unificationHints_2397_; uint8_t v_proofIrrelevance_2398_; uint8_t v_assignSyntheticOpaque_2399_; uint8_t v_offsetCnstrs_2400_; uint8_t v_etaStruct_2401_; uint8_t v_univApprox_2402_; uint8_t v_iota_2403_; uint8_t v_beta_2404_; uint8_t v_proj_2405_; uint8_t v_zeta_2406_; uint8_t v_zetaDelta_2407_; uint8_t v_zetaUnused_2408_; uint8_t v_zetaHave_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2461_; 
lean_del_object(v___x_2379_);
v___x_2391_ = l_Lean_Meta_Context_config(v___y_2370_);
v_foApprox_2392_ = lean_ctor_get_uint8(v___x_2391_, 0);
v_ctxApprox_2393_ = lean_ctor_get_uint8(v___x_2391_, 1);
v_quasiPatternApprox_2394_ = lean_ctor_get_uint8(v___x_2391_, 2);
v_constApprox_2395_ = lean_ctor_get_uint8(v___x_2391_, 3);
v_isDefEqStuckEx_2396_ = lean_ctor_get_uint8(v___x_2391_, 4);
v_unificationHints_2397_ = lean_ctor_get_uint8(v___x_2391_, 5);
v_proofIrrelevance_2398_ = lean_ctor_get_uint8(v___x_2391_, 6);
v_assignSyntheticOpaque_2399_ = lean_ctor_get_uint8(v___x_2391_, 7);
v_offsetCnstrs_2400_ = lean_ctor_get_uint8(v___x_2391_, 8);
v_etaStruct_2401_ = lean_ctor_get_uint8(v___x_2391_, 10);
v_univApprox_2402_ = lean_ctor_get_uint8(v___x_2391_, 11);
v_iota_2403_ = lean_ctor_get_uint8(v___x_2391_, 12);
v_beta_2404_ = lean_ctor_get_uint8(v___x_2391_, 13);
v_proj_2405_ = lean_ctor_get_uint8(v___x_2391_, 14);
v_zeta_2406_ = lean_ctor_get_uint8(v___x_2391_, 15);
v_zetaDelta_2407_ = lean_ctor_get_uint8(v___x_2391_, 16);
v_zetaUnused_2408_ = lean_ctor_get_uint8(v___x_2391_, 17);
v_zetaHave_2409_ = lean_ctor_get_uint8(v___x_2391_, 18);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2411_ = v___x_2391_;
v_isShared_2412_ = v_isSharedCheck_2461_;
goto v_resetjp_2410_;
}
else
{
lean_dec(v___x_2391_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2461_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
uint8_t v_trackZetaDelta_2413_; lean_object* v_zetaDeltaSet_2414_; lean_object* v_lctx_2415_; lean_object* v_localInstances_2416_; lean_object* v_defEqCtx_x3f_2417_; lean_object* v_synthPendingDepth_2418_; lean_object* v_canUnfold_x3f_2419_; uint8_t v_univApprox_2420_; uint8_t v_inTypeClassResolution_2421_; uint8_t v_cacheInferType_2422_; uint8_t v___x_2423_; lean_object* v_config_2425_; 
v_trackZetaDelta_2413_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*7);
v_zetaDeltaSet_2414_ = lean_ctor_get(v___y_2370_, 1);
v_lctx_2415_ = lean_ctor_get(v___y_2370_, 2);
v_localInstances_2416_ = lean_ctor_get(v___y_2370_, 3);
v_defEqCtx_x3f_2417_ = lean_ctor_get(v___y_2370_, 4);
v_synthPendingDepth_2418_ = lean_ctor_get(v___y_2370_, 5);
v_canUnfold_x3f_2419_ = lean_ctor_get(v___y_2370_, 6);
v_univApprox_2420_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2421_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*7 + 2);
v_cacheInferType_2422_ = lean_ctor_get_uint8(v___y_2370_, sizeof(void*)*7 + 3);
v___x_2423_ = 0;
if (v_isShared_2412_ == 0)
{
v_config_2425_ = v___x_2411_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 0, v_foApprox_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 1, v_ctxApprox_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 2, v_quasiPatternApprox_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 3, v_constApprox_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 4, v_isDefEqStuckEx_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 5, v_unificationHints_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 6, v_proofIrrelevance_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 7, v_assignSyntheticOpaque_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 8, v_offsetCnstrs_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 10, v_etaStruct_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 11, v_univApprox_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 12, v_iota_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 13, v_beta_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 14, v_proj_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 15, v_zeta_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 16, v_zetaDelta_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 17, v_zetaUnused_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 18, v_zetaHave_2409_);
v_config_2425_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v___x_2428_; lean_object* v___f_2429_; uint64_t v___x_2430_; uint64_t v___x_2431_; uint64_t v_key_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_ctor_set_uint8(v_config_2425_, 9, v___x_2423_);
v___x_2426_ = l_Lean_Meta_Context_configKey(v___y_2370_);
v___x_2427_ = 3ULL;
v___x_2428_ = lean_uint64_shift_right(v___x_2426_, v___x_2427_);
lean_inc(v_a_2375_);
v___f_2429_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2429_, 0, v_a_2375_);
lean_closure_set(v___f_2429_, 1, v_e_2348_);
v___x_2430_ = lean_uint64_shift_left(v___x_2428_, v___x_2427_);
v___x_2431_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2432_ = lean_uint64_lor(v___x_2430_, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2433_, 0, v_config_2425_);
lean_ctor_set_uint64(v___x_2433_, sizeof(void*)*1, v_key_2432_);
lean_inc(v_canUnfold_x3f_2419_);
lean_inc(v_synthPendingDepth_2418_);
lean_inc(v_defEqCtx_x3f_2417_);
lean_inc_ref(v_localInstances_2416_);
lean_inc_ref(v_lctx_2415_);
lean_inc(v_zetaDeltaSet_2414_);
v___x_2434_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v_zetaDeltaSet_2414_);
lean_ctor_set(v___x_2434_, 2, v_lctx_2415_);
lean_ctor_set(v___x_2434_, 3, v_localInstances_2416_);
lean_ctor_set(v___x_2434_, 4, v_defEqCtx_x3f_2417_);
lean_ctor_set(v___x_2434_, 5, v_synthPendingDepth_2418_);
lean_ctor_set(v___x_2434_, 6, v_canUnfold_x3f_2419_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*7, v_trackZetaDelta_2413_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*7 + 1, v_univApprox_2420_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2421_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*7 + 3, v_cacheInferType_2422_);
v___x_2435_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2429_, v___x_2364_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___x_2434_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec_ref_known(v___x_2434_, 7);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; 
v_unused_2443_ = lean_ctor_get(v___x_2435_, 0);
lean_dec(v_unused_2443_);
v___x_2437_ = v___x_2435_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_dec(v___x_2435_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_a_2375_);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2375_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2435_, 0);
lean_dec(v_unused_2451_);
v___x_2445_ = v___x_2435_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_dec(v___x_2435_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
lean_ctor_set(v___x_2445_, 0, v_a_2375_);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2375_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_a_2375_);
v_a_2452_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2435_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2435_);
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
}
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2375_);
lean_dec_ref(v_e_2348_);
v_a_2463_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2376_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2376_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_dec_ref(v_e_2348_);
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref(v_e_2348_);
lean_dec_ref(v_F_2347_);
lean_dec(v_fixedPrefixSize_2346_);
lean_dec(v_recFnName_2345_);
v_a_2498_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2358_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2358_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2506_, lean_object* v_recFnName_2507_, lean_object* v_fixedPrefixSize_2508_, lean_object* v_F_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_expr_instantiate1(v_body_2506_, v_x_2510_);
v___x_2521_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2507_, v_fixedPrefixSize_2508_, v_F_2509_, v___x_2520_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2522_, lean_object* v_fixedPrefixSize_2523_, lean_object* v_F_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2522_, v_fixedPrefixSize_2523_, v_F_2524_, v_e_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec(v_a_2526_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2536_, lean_object* v_fixedPrefixSize_2537_, lean_object* v_F_2538_, lean_object* v_sz_2539_, lean_object* v_i_2540_, lean_object* v_bs_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
size_t v_sz_boxed_2551_; size_t v_i_boxed_2552_; lean_object* v_res_2553_; 
v_sz_boxed_2551_ = lean_unbox_usize(v_sz_2539_);
lean_dec(v_sz_2539_);
v_i_boxed_2552_ = lean_unbox_usize(v_i_2540_);
lean_dec(v_i_2540_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2536_, v_fixedPrefixSize_2537_, v_F_2538_, v_sz_boxed_2551_, v_i_boxed_2552_, v_bs_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v___y_2542_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2554_, lean_object* v_fixedPrefixSize_2555_, lean_object* v_F_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2554_, v_fixedPrefixSize_2555_, v_F_2556_, v_x_2557_, v_x_2558_, v_x_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec(v___y_2560_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2570_, lean_object* v_fixedPrefixSize_2571_, lean_object* v_e_2572_, lean_object* v_as_2573_, lean_object* v_bs_2574_, lean_object* v_i_2575_, lean_object* v_cs_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2570_, v_fixedPrefixSize_2571_, v_e_2572_, v_as_2573_, v_bs_2574_, v_i_2575_, v_cs_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v_bs_2574_);
lean_dec_ref(v_as_2573_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2587_, lean_object* v_fixedPrefixSize_2588_, lean_object* v_F_2589_, lean_object* v_e_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2587_, v_fixedPrefixSize_2588_, v_F_2589_, v_e_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec(v_a_2591_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2601_, lean_object* v_fixedPrefixSize_2602_, lean_object* v_F_2603_, lean_object* v_e_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2601_, v_fixedPrefixSize_2602_, v_F_2603_, v_e_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec(v_a_2605_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2615_, lean_object* v_fixedPrefixSize_2616_, lean_object* v_F_2617_, lean_object* v_e_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2615_, v_fixedPrefixSize_2616_, v_F_2617_, v_e_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec(v_a_2619_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2629_, lean_object* v_k_2630_, uint8_t v_allowLevelAssignments_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2630_, v_allowLevelAssignments_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_k_2643_, lean_object* v_allowLevelAssignments_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2654_; lean_object* v_res_2655_; 
v_allowLevelAssignments_boxed_2654_ = lean_unbox(v_allowLevelAssignments_2644_);
v_res_2655_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2642_, v_k_2643_, v_allowLevelAssignments_boxed_2654_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2656_, lean_object* v_name_2657_, uint8_t v_bi_2658_, lean_object* v_type_2659_, lean_object* v_k_2660_, uint8_t v_kind_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2657_, v_bi_2658_, v_type_2659_, v_k_2660_, v_kind_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2672_, lean_object* v_name_2673_, lean_object* v_bi_2674_, lean_object* v_type_2675_, lean_object* v_k_2676_, lean_object* v_kind_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v_bi_boxed_2687_; uint8_t v_kind_boxed_2688_; lean_object* v_res_2689_; 
v_bi_boxed_2687_ = lean_unbox(v_bi_2674_);
v_kind_boxed_2688_ = lean_unbox(v_kind_2677_);
v_res_2689_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2672_, v_name_2673_, v_bi_boxed_2687_, v_type_2675_, v_k_2676_, v_kind_boxed_2688_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v___y_2678_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2690_, lean_object* v_e_2691_, lean_object* v_maxFVars_2692_, lean_object* v_k_2693_, uint8_t v_cleanupAnnotations_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2691_, v_maxFVars_2692_, v_k_2693_, v_cleanupAnnotations_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_e_2706_, lean_object* v_maxFVars_2707_, lean_object* v_k_2708_, lean_object* v_cleanupAnnotations_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2719_; lean_object* v_res_2720_; 
v_cleanupAnnotations_boxed_2719_ = lean_unbox(v_cleanupAnnotations_2709_);
v_res_2720_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2705_, v_e_2706_, v_maxFVars_2707_, v_k_2708_, v_cleanupAnnotations_boxed_2719_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2721_, lean_object* v_R_2722_, lean_object* v_a_2723_, lean_object* v_b_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2723_, v_b_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2726_, lean_object* v_msg_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2726_, v_msg_2727_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2738_, lean_object* v_msg_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2738_, v_msg_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2750_, lean_object* v_m_2751_, lean_object* v_a_2752_, lean_object* v_b_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2751_, v_a_2752_, v_b_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2756_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_msg_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2767_, v_msg_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2779_, lean_object* v_m_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2780_, v_a_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2783_, lean_object* v_m_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2783_, v_m_2784_, v_a_2785_);
lean_dec_ref(v_a_2785_);
lean_dec_ref(v_m_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2787_, lean_object* v_name_2788_, lean_object* v_type_2789_, lean_object* v_val_2790_, lean_object* v_k_2791_, uint8_t v_nondep_2792_, uint8_t v_kind_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2788_, v_type_2789_, v_val_2790_, v_k_2791_, v_nondep_2792_, v_kind_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2804_, lean_object* v_name_2805_, lean_object* v_type_2806_, lean_object* v_val_2807_, lean_object* v_k_2808_, lean_object* v_nondep_2809_, lean_object* v_kind_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
uint8_t v_nondep_boxed_2820_; uint8_t v_kind_boxed_2821_; lean_object* v_res_2822_; 
v_nondep_boxed_2820_ = lean_unbox(v_nondep_2809_);
v_kind_boxed_2821_ = lean_unbox(v_kind_2810_);
v_res_2822_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2804_, v_name_2805_, v_type_2806_, v_val_2807_, v_k_2808_, v_nondep_boxed_2820_, v_kind_boxed_2821_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2823_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
return v_res_2844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2845_, lean_object* v_a_2846_, lean_object* v_x_2847_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2846_, v_x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2849_, lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
uint8_t v_res_2852_; lean_object* v_r_2853_; 
v_res_2852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2849_, v_a_2850_, v_x_2851_);
lean_dec(v_x_2851_);
lean_dec_ref(v_a_2850_);
v_r_2853_ = lean_box(v_res_2852_);
return v_r_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2854_, lean_object* v_data_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2857_, lean_object* v_a_2858_, lean_object* v_b_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2858_, v_b_2859_, v_x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2862_, lean_object* v_a_2863_, lean_object* v_x_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2863_, v_x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2866_, lean_object* v_a_2867_, lean_object* v_x_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2866_, v_a_2867_, v_x_2868_);
lean_dec(v_x_2868_);
lean_dec_ref(v_a_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2870_, lean_object* v_i_2871_, lean_object* v_source_2872_, lean_object* v_target_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2871_, v_source_2872_, v_target_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2875_, lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_constName_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2887_, v_constName_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2900_, v_x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2903_, lean_object* v_ref_2904_, lean_object* v_constName_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2904_, v_constName_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_ref_2917_, lean_object* v_constName_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2916_, v_ref_2917_, v_constName_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec(v_ref_2917_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2929_, lean_object* v_ref_2930_, lean_object* v_msg_2931_, lean_object* v_declHint_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2930_, v_msg_2931_, v_declHint_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_ref_2944_, lean_object* v_msg_2945_, lean_object* v_declHint_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2943_, v_ref_2944_, v_msg_2945_, v_declHint_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec(v_ref_2944_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2957_, lean_object* v_declHint_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2957_, v_declHint_2958_, v___y_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2969_, lean_object* v_declHint_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2969_, v_declHint_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec(v___y_2971_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2981_, lean_object* v_ref_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2982_, v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2994_, lean_object* v_ref_2995_, lean_object* v_msg_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2994_, v_ref_2995_, v_msg_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v_ref_2995_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3007_, lean_object* v_msg_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_ref_3014_; lean_object* v___x_3015_; lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3060_; 
v_ref_3014_ = lean_ctor_get(v___y_3011_, 5);
v___x_3015_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3060_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3060_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v_traceState_3021_; lean_object* v_env_3022_; lean_object* v_nextMacroScope_3023_; lean_object* v_ngen_3024_; lean_object* v_auxDeclNGen_3025_; lean_object* v_cache_3026_; lean_object* v_messages_3027_; lean_object* v_infoState_3028_; lean_object* v_snapshotTasks_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3059_; 
v___x_3020_ = lean_st_ref_take(v___y_3012_);
v_traceState_3021_ = lean_ctor_get(v___x_3020_, 4);
v_env_3022_ = lean_ctor_get(v___x_3020_, 0);
v_nextMacroScope_3023_ = lean_ctor_get(v___x_3020_, 1);
v_ngen_3024_ = lean_ctor_get(v___x_3020_, 2);
v_auxDeclNGen_3025_ = lean_ctor_get(v___x_3020_, 3);
v_cache_3026_ = lean_ctor_get(v___x_3020_, 5);
v_messages_3027_ = lean_ctor_get(v___x_3020_, 6);
v_infoState_3028_ = lean_ctor_get(v___x_3020_, 7);
v_snapshotTasks_3029_ = lean_ctor_get(v___x_3020_, 8);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3031_ = v___x_3020_;
v_isShared_3032_ = v_isSharedCheck_3059_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_snapshotTasks_3029_);
lean_inc(v_infoState_3028_);
lean_inc(v_messages_3027_);
lean_inc(v_cache_3026_);
lean_inc(v_traceState_3021_);
lean_inc(v_auxDeclNGen_3025_);
lean_inc(v_ngen_3024_);
lean_inc(v_nextMacroScope_3023_);
lean_inc(v_env_3022_);
lean_dec(v___x_3020_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3059_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
uint64_t v_tid_3033_; lean_object* v_traces_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3058_; 
v_tid_3033_ = lean_ctor_get_uint64(v_traceState_3021_, sizeof(void*)*1);
v_traces_3034_ = lean_ctor_get(v_traceState_3021_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_traceState_3021_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3036_ = v_traceState_3021_;
v_isShared_3037_ = v_isSharedCheck_3058_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_traces_3034_);
lean_dec(v_traceState_3021_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3058_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; double v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3040_ = 0;
v___x_3041_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3042_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3042_, 0, v_cls_3007_);
lean_ctor_set(v___x_3042_, 1, v___x_3038_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
lean_ctor_set_float(v___x_3042_, sizeof(void*)*3, v___x_3039_);
lean_ctor_set_float(v___x_3042_, sizeof(void*)*3 + 8, v___x_3039_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*3 + 16, v___x_3040_);
v___x_3043_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3044_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v_a_3016_);
lean_ctor_set(v___x_3044_, 2, v___x_3043_);
lean_inc(v_ref_3014_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_ref_3014_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_PersistentArray_push___redArg(v_traces_3034_, v___x_3045_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3046_);
v___x_3048_ = v___x_3036_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3046_);
lean_ctor_set_uint64(v_reuseFailAlloc_3057_, sizeof(void*)*1, v_tid_3033_);
v___x_3048_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 4, v___x_3048_);
v___x_3050_ = v___x_3031_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_env_3022_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_nextMacroScope_3023_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_ngen_3024_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_auxDeclNGen_3025_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3056_, 5, v_cache_3026_);
lean_ctor_set(v_reuseFailAlloc_3056_, 6, v_messages_3027_);
lean_ctor_set(v_reuseFailAlloc_3056_, 7, v_infoState_3028_);
lean_ctor_set(v_reuseFailAlloc_3056_, 8, v_snapshotTasks_3029_);
v___x_3050_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3051_ = lean_st_ref_set(v___y_3012_, v___x_3050_);
v___x_3052_ = lean_box(0);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3052_);
v___x_3054_ = v___x_3018_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3061_, lean_object* v_msg_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3061_, v_msg_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3068_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_unsigned_to_nat(16u);
v___x_3071_ = lean_mk_array(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3077_ = l_Lean_stringToMessageData(v___x_3076_);
return v___x_3077_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3080_ = l_Lean_stringToMessageData(v___x_3079_);
return v___x_3080_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3083_ = l_Lean_stringToMessageData(v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3084_, lean_object* v_fixedPrefixSize_3085_, lean_object* v_F_3086_, lean_object* v_e_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v_options_3116_; uint8_t v_hasTrace_3117_; 
v_options_3116_ = lean_ctor_get(v_a_3092_, 2);
v_hasTrace_3117_ = lean_ctor_get_uint8(v_options_3116_, sizeof(void*)*1);
if (v_hasTrace_3117_ == 0)
{
v___y_3096_ = v_a_3088_;
v___y_3097_ = v_a_3089_;
v___y_3098_ = v_a_3090_;
v___y_3099_ = v_a_3091_;
v___y_3100_ = v_a_3092_;
v___y_3101_ = v_a_3093_;
goto v___jp_3095_;
}
else
{
lean_object* v_inheritedTraceOptions_3118_; lean_object* v_cls_3119_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v_options_3126_; lean_object* v_inheritedTraceOptions_3127_; lean_object* v___y_3128_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_inheritedTraceOptions_3118_ = lean_ctor_get(v_a_3092_, 13);
v_cls_3119_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3149_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3118_, v_options_3116_, v___x_3149_);
if (v___x_3150_ == 0)
{
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v_options_3126_ = v_options_3116_;
v_inheritedTraceOptions_3127_ = v_inheritedTraceOptions_3118_;
v___y_3128_ = v_a_3093_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3151_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3087_);
v___x_3152_ = l_Lean_indentExpr(v_e_3087_);
v___x_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3119_, v___x_3153_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v_options_3126_ = v_options_3116_;
v_inheritedTraceOptions_3127_ = v_inheritedTraceOptions_3118_;
v___y_3128_ = v_a_3093_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_e_3087_);
lean_dec_ref(v_F_3086_);
lean_dec(v_fixedPrefixSize_3085_);
lean_dec(v_recFnName_3084_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3127_, v_options_3126_, v___x_3129_);
if (v___x_3130_ == 0)
{
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3125_;
v___y_3101_ = v___y_3128_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3131_; 
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3123_);
lean_inc_ref(v_F_3086_);
v___x_3131_ = lean_infer_type(v_F_3086_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v___x_3133_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3086_);
v___x_3134_ = l_Lean_MessageData_ofExpr(v_F_3086_);
v___x_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Lean_indentExpr(v_a_3132_);
v___x_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3137_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3119_, v___x_3139_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3128_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_dec_ref_known(v___x_3140_, 1);
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3125_;
v___y_3101_ = v___y_3128_;
goto v___jp_3095_;
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_e_3087_);
lean_dec_ref(v_F_3086_);
lean_dec(v_fixedPrefixSize_3085_);
lean_dec(v_recFnName_3084_);
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_dec_ref(v_e_3087_);
lean_dec_ref(v_F_3086_);
lean_dec(v_fixedPrefixSize_3085_);
lean_dec(v_recFnName_3084_);
return v___x_3131_;
}
}
}
}
v___jp_3095_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3102_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3103_ = lean_st_mk_ref(v___x_3102_);
v___x_3104_ = lean_st_mk_ref(v___x_3102_);
v___x_3105_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3084_, v_fixedPrefixSize_3085_, v_F_3086_, v_e_3087_, v___x_3104_, v___x_3103_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3115_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3110_ = lean_st_ref_get(v___x_3104_);
lean_dec(v___x_3104_);
lean_dec(v___x_3110_);
v___x_3111_ = lean_st_ref_get(v___x_3103_);
lean_dec(v___x_3103_);
lean_dec(v___x_3111_);
if (v_isShared_3109_ == 0)
{
v___x_3113_ = v___x_3108_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3106_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
lean_dec(v___x_3104_);
lean_dec(v___x_3103_);
return v___x_3105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3163_, lean_object* v_fixedPrefixSize_3164_, lean_object* v_F_3165_, lean_object* v_e_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3163_, v_fixedPrefixSize_3164_, v_F_3165_, v_e_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3175_, lean_object* v_msg_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3175_, v_msg_3176_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3185_, lean_object* v_msg_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3185_, v_msg_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v_b_3198_, lean_object* v_c_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
lean_inc(v___y_3203_);
lean_inc_ref(v___y_3202_);
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3200_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
v___x_3205_ = lean_apply_9(v_k_3195_, v_b_3198_, v_c_3199_, v___y_3196_, v___y_3197_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, lean_box(0));
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v_b_3209_, lean_object* v_c_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3206_, v___y_3207_, v___y_3208_, v_b_3209_, v_c_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3217_, lean_object* v_k_3218_, uint8_t v_cleanupAnnotations_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___f_3227_; uint8_t v___x_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_inc(v___y_3221_);
lean_inc_ref(v___y_3220_);
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3227_, 0, v_k_3218_);
lean_closure_set(v___f_3227_, 1, v___y_3220_);
lean_closure_set(v___f_3227_, 2, v___y_3221_);
v___x_3228_ = 1;
v___x_3229_ = 0;
v___x_3230_ = lean_box(0);
v___x_3231_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3217_, v___x_3228_, v___x_3229_, v___x_3228_, v___x_3229_, v___x_3230_, v___f_3227_, v_cleanupAnnotations_3219_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3231_) == 0)
{
return v___x_3231_;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3240_, lean_object* v_k_3241_, lean_object* v_cleanupAnnotations_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3250_; lean_object* v_res_3251_; 
v_cleanupAnnotations_boxed_3250_ = lean_unbox(v_cleanupAnnotations_3242_);
v_res_3251_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3240_, v_k_3241_, v_cleanupAnnotations_boxed_3250_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3252_, lean_object* v_e_3253_, lean_object* v_k_3254_, uint8_t v_cleanupAnnotations_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3253_, v_k_3254_, v_cleanupAnnotations_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3264_, lean_object* v_e_3265_, lean_object* v_k_3266_, lean_object* v_cleanupAnnotations_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3275_; lean_object* v_res_3276_; 
v_cleanupAnnotations_boxed_3275_ = lean_unbox(v_cleanupAnnotations_3267_);
v_res_3276_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3264_, v_e_3265_, v_k_3266_, v_cleanupAnnotations_boxed_3275_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3277_, lean_object* v_maxFVars_3278_, lean_object* v_k_3279_, uint8_t v_cleanupAnnotations_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___f_3288_; uint8_t v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3281_);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3288_, 0, v_k_3279_);
lean_closure_set(v___f_3288_, 1, v___y_3281_);
lean_closure_set(v___f_3288_, 2, v___y_3282_);
v___x_3289_ = 1;
v___x_3290_ = 0;
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_maxFVars_3278_);
v___x_3292_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3277_, v___x_3289_, v___x_3290_, v___x_3289_, v___x_3290_, v___x_3291_, v___f_3288_, v_cleanupAnnotations_3280_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec_ref_known(v___x_3291_, 1);
if (lean_obj_tag(v___x_3292_) == 0)
{
return v___x_3292_;
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3301_, lean_object* v_maxFVars_3302_, lean_object* v_k_3303_, lean_object* v_cleanupAnnotations_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3312_; lean_object* v_res_3313_; 
v_cleanupAnnotations_boxed_3312_ = lean_unbox(v_cleanupAnnotations_3304_);
v_res_3313_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3301_, v_maxFVars_3302_, v_k_3303_, v_cleanupAnnotations_boxed_3312_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3314_, lean_object* v_e_3315_, lean_object* v_maxFVars_3316_, lean_object* v_k_3317_, uint8_t v_cleanupAnnotations_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3315_, v_maxFVars_3316_, v_k_3317_, v_cleanupAnnotations_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3327_, lean_object* v_e_3328_, lean_object* v_maxFVars_3329_, lean_object* v_k_3330_, lean_object* v_cleanupAnnotations_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3339_; lean_object* v_res_3340_; 
v_cleanupAnnotations_boxed_3339_ = lean_unbox(v_cleanupAnnotations_3331_);
v_res_3340_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3327_, v_e_3328_, v_maxFVars_3329_, v_k_3330_, v_cleanupAnnotations_boxed_3339_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v_x_3344_, uint8_t v___x_3345_, lean_object* v_xs_3346_, lean_object* v_type_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3355_ = l_Lean_LocalDecl_type(v_a_3341_);
v___x_3356_ = lean_array_get_borrowed(v___x_3342_, v_xs_3346_, v___x_3343_);
v___x_3357_ = l_Lean_Expr_replaceFVar(v___x_3355_, v_x_3344_, v___x_3356_);
lean_dec_ref(v___x_3355_);
v___x_3358_ = l_Lean_mkArrow(v___x_3357_, v_type_3347_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; uint8_t v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_n(v_a_3359_, 2);
lean_dec_ref_known(v___x_3358_, 1);
v___x_3360_ = 0;
v___x_3361_ = 1;
v___x_3362_ = l_Lean_Meta_mkLambdaFVars(v_xs_3346_, v_a_3359_, v___x_3360_, v___x_3345_, v___x_3360_, v___x_3345_, v___x_3361_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = l_Lean_Meta_getLevel(v_a_3359_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3373_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v_a_3363_);
lean_ctor_set(v___x_3369_, 1, v_a_3365_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3369_);
v___x_3371_ = v___x_3367_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_a_3363_);
v_a_3374_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3364_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3364_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_a_3359_);
v_a_3382_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3362_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3362_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
v_a_3390_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3358_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3358_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3398_, lean_object* v___x_3399_, lean_object* v___x_3400_, lean_object* v_x_3401_, lean_object* v___x_3402_, lean_object* v_xs_3403_, lean_object* v_type_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
uint8_t v___x_6703__boxed_3412_; lean_object* v_res_3413_; 
v___x_6703__boxed_3412_ = lean_unbox(v___x_3402_);
v_res_3413_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3398_, v___x_3399_, v___x_3400_, v_x_3401_, v___x_6703__boxed_3412_, v_xs_3403_, v_type_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_xs_3403_);
lean_dec(v___x_3400_);
lean_dec_ref(v___x_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v_b_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
lean_inc(v___y_3421_);
lean_inc_ref(v___y_3420_);
lean_inc(v___y_3419_);
lean_inc_ref(v___y_3418_);
lean_inc(v___y_3416_);
lean_inc_ref(v___y_3415_);
v___x_3423_ = lean_apply_8(v_k_3414_, v_b_3417_, v___y_3415_, v___y_3416_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, lean_box(0));
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v_b_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3424_, v___y_3425_, v___y_3426_, v_b_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3434_, uint8_t v_bi_3435_, lean_object* v_type_3436_, lean_object* v_k_3437_, uint8_t v_kind_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___f_3446_; lean_object* v___x_3447_; 
lean_inc(v___y_3440_);
lean_inc_ref(v___y_3439_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3446_, 0, v_k_3437_);
lean_closure_set(v___f_3446_, 1, v___y_3439_);
lean_closure_set(v___f_3446_, 2, v___y_3440_);
v___x_3447_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3434_, v_bi_3435_, v_type_3436_, v___f_3446_, v_kind_3438_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
return v___x_3447_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3456_, lean_object* v_bi_3457_, lean_object* v_type_3458_, lean_object* v_k_3459_, lean_object* v_kind_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_bi_boxed_3468_; uint8_t v_kind_boxed_3469_; lean_object* v_res_3470_; 
v_bi_boxed_3468_ = lean_unbox(v_bi_3457_);
v_kind_boxed_3469_ = lean_unbox(v_kind_3460_);
v_res_3470_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3456_, v_bi_boxed_3468_, v_type_3458_, v_k_3459_, v_kind_boxed_3469_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3471_, lean_object* v_type_3472_, lean_object* v_k_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = 0;
v___x_3482_ = 0;
v___x_3483_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3471_, v___x_3481_, v_type_3472_, v_k_3473_, v___x_3482_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3484_, lean_object* v_type_3485_, lean_object* v_k_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3484_, v_type_3485_, v_k_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3508_, lean_object* v_F_3509_, lean_object* v_val_3510_, lean_object* v_k_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
uint8_t v___y_3520_; uint8_t v___x_3635_; 
v___x_3635_ = l_Lean_Expr_isFVar(v_x_3508_);
if (v___x_3635_ == 0)
{
v___y_3520_ = v___x_3635_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3637_ = lean_unsigned_to_nat(6u);
v___x_3638_ = l_Lean_Expr_isAppOfArity(v_val_3510_, v___x_3636_, v___x_3637_);
v___y_3520_ = v___x_3638_;
goto v___jp_3519_;
}
v___jp_3519_:
{
if (v___y_3520_ == 0)
{
lean_object* v___x_3521_; 
lean_inc(v_a_3517_);
lean_inc_ref(v_a_3516_);
lean_inc(v_a_3515_);
lean_inc_ref(v_a_3514_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
v___x_3521_ = lean_apply_10(v_k_3511_, v_x_3508_, v_F_3509_, v_val_3510_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, lean_box(0));
return v___x_3521_;
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3522_ = lean_unsigned_to_nat(3u);
v___x_3523_ = l_Lean_Expr_getAppNumArgs(v_val_3510_);
v___x_3524_ = lean_nat_sub(v___x_3523_, v___x_3522_);
v___x_3525_ = lean_unsigned_to_nat(1u);
v___x_3526_ = lean_nat_sub(v___x_3524_, v___x_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = l_Lean_Expr_getRevArg_x21(v_val_3510_, v___x_3526_);
v___x_3528_ = lean_expr_eqv(v___x_3527_, v_x_3508_);
lean_dec_ref(v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
lean_dec(v___x_3523_);
lean_inc(v_a_3517_);
lean_inc_ref(v_a_3516_);
lean_inc(v_a_3515_);
lean_inc_ref(v_a_3514_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
v___x_3529_ = lean_apply_10(v_k_3511_, v_x_3508_, v_F_3509_, v_val_3510_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, lean_box(0));
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3530_ = lean_unsigned_to_nat(4u);
v___x_3531_ = lean_nat_sub(v___x_3523_, v___x_3530_);
v___x_3532_ = lean_nat_sub(v___x_3531_, v___x_3525_);
lean_dec(v___x_3531_);
v___x_3533_ = l_Lean_Expr_getRevArg_x21(v_val_3510_, v___x_3532_);
v___x_3534_ = l_Lean_Expr_isLambda(v___x_3533_);
lean_dec_ref(v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; 
lean_dec(v___x_3523_);
lean_inc(v_a_3517_);
lean_inc_ref(v_a_3516_);
lean_inc(v_a_3515_);
lean_inc_ref(v_a_3514_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
v___x_3535_ = lean_apply_10(v_k_3511_, v_x_3508_, v_F_3509_, v_val_3510_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, lean_box(0));
return v___x_3535_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3536_ = lean_unsigned_to_nat(5u);
v___x_3537_ = lean_nat_sub(v___x_3523_, v___x_3536_);
v___x_3538_ = lean_nat_sub(v___x_3537_, v___x_3525_);
lean_dec(v___x_3537_);
v___x_3539_ = l_Lean_Expr_getRevArg_x21(v_val_3510_, v___x_3538_);
v___x_3540_ = l_Lean_Expr_isLambda(v___x_3539_);
lean_dec_ref(v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec(v___x_3523_);
lean_inc(v_a_3517_);
lean_inc_ref(v_a_3516_);
lean_inc(v_a_3515_);
lean_inc_ref(v_a_3514_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
v___x_3541_ = lean_apply_10(v_k_3511_, v_x_3508_, v_F_3509_, v_val_3510_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, lean_box(0));
return v___x_3541_;
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = l_Lean_Expr_fvarId_x21(v_F_3509_);
v___x_3543_ = l_Lean_FVarId_getDecl___redArg(v___x_3542_, v_a_3514_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v_dummy_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_args_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc_n(v_a_3544_, 2);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_instInhabitedExpr;
v_dummy_3546_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3523_);
v___x_3547_ = lean_mk_array(v___x_3523_, v_dummy_3546_);
v___x_3548_ = lean_nat_sub(v___x_3523_, v___x_3525_);
lean_dec(v___x_3523_);
v_args_3549_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3510_, v___x_3547_, v___x_3548_);
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_box(v___x_3534_);
lean_inc_ref(v_x_3508_);
v___f_3552_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3552_, 0, v_a_3544_);
lean_closure_set(v___f_3552_, 1, v___x_3545_);
lean_closure_set(v___f_3552_, 2, v___x_3550_);
lean_closure_set(v___f_3552_, 3, v_x_3508_);
lean_closure_set(v___f_3552_, 4, v___x_3551_);
v___x_3553_ = lean_unsigned_to_nat(2u);
v___x_3554_ = lean_array_get(v___x_3545_, v_args_3549_, v___x_3553_);
v___x_3555_ = 0;
v___x_3556_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3554_, v___f_3552_, v___x_3555_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v_fst_3558_; lean_object* v_snd_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3618_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v_fst_3558_ = lean_ctor_get(v_a_3557_, 0);
v_snd_3559_ = lean_ctor_get(v_a_3557_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_a_3557_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3561_ = v_a_3557_;
v_isShared_3562_ = v_isSharedCheck_3618_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_snd_3559_);
lean_inc(v_fst_3558_);
lean_dec(v_a_3557_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3618_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_00_u03b1_3563_; lean_object* v_00_u03b2_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_00_u03b1_3563_ = lean_array_get(v___x_3545_, v_args_3549_, v___x_3550_);
v_00_u03b2_3564_ = lean_array_get(v___x_3545_, v_args_3549_, v___x_3525_);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3566_ = lean_array_get(v___x_3545_, v_args_3549_, v___x_3530_);
lean_inc_ref(v_x_3508_);
lean_inc(v_a_3544_);
lean_inc_ref(v_k_3511_);
lean_inc(v_00_u03b2_3564_);
lean_inc(v_00_u03b1_3563_);
v___x_3567_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3545_, v___x_3550_, v_00_u03b1_3563_, v_00_u03b2_3564_, v___x_3522_, v_k_3511_, v___x_3553_, v___x_3555_, v___x_3534_, v_a_3544_, v_x_3508_, v___x_3525_, v___x_3565_, v___x_3566_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3570_ = lean_array_get(v___x_3545_, v_args_3549_, v___x_3536_);
lean_dec_ref(v_args_3549_);
lean_inc_ref(v_x_3508_);
lean_inc(v_00_u03b2_3564_);
lean_inc(v_00_u03b1_3563_);
v___x_3571_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3545_, v___x_3550_, v_00_u03b1_3563_, v_00_u03b2_3564_, v___x_3522_, v_k_3511_, v___x_3553_, v___x_3555_, v___x_3534_, v_a_3544_, v_x_3508_, v___x_3525_, v___x_3569_, v___x_3570_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3571_, 1);
lean_inc(v_00_u03b1_3563_);
v___x_3573_ = l_Lean_Meta_getLevel(v_00_u03b1_3563_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
lean_inc(v_00_u03b2_3564_);
v___x_3575_ = l_Lean_Meta_getLevel(v_00_u03b2_3564_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3601_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3601_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3601_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3581_ = lean_box(0);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 1);
lean_ctor_set(v___x_3561_, 1, v___x_3581_);
lean_ctor_set(v___x_3561_, 0, v_a_3576_);
v___x_3583_ = v___x_3561_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3576_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_a_3574_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_snd_3559_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Lean_mkConst(v___x_3580_, v___x_3585_);
v___x_3587_ = lean_unsigned_to_nat(7u);
v___x_3588_ = lean_mk_empty_array_with_capacity(v___x_3587_);
v___x_3589_ = lean_array_push(v___x_3588_, v_00_u03b1_3563_);
v___x_3590_ = lean_array_push(v___x_3589_, v_00_u03b2_3564_);
v___x_3591_ = lean_array_push(v___x_3590_, v_fst_3558_);
v___x_3592_ = lean_array_push(v___x_3591_, v_x_3508_);
v___x_3593_ = lean_array_push(v___x_3592_, v_a_3568_);
v___x_3594_ = lean_array_push(v___x_3593_, v_a_3572_);
v___x_3595_ = lean_array_push(v___x_3594_, v_F_3509_);
v___x_3596_ = l_Lean_mkAppN(v___x_3586_, v___x_3595_);
lean_dec_ref(v___x_3595_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3596_);
v___x_3598_ = v___x_3578_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_a_3574_);
lean_dec(v_a_3572_);
lean_dec(v_a_3568_);
lean_dec(v_00_u03b2_3564_);
lean_dec(v_00_u03b1_3563_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
v_a_3602_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3575_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3575_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_a_3572_);
lean_dec(v_a_3568_);
lean_dec(v_00_u03b2_3564_);
lean_dec(v_00_u03b1_3563_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
v_a_3610_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3573_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3573_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_dec(v_a_3568_);
lean_dec(v_00_u03b2_3564_);
lean_dec(v_00_u03b1_3563_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
return v___x_3571_;
}
}
else
{
lean_dec(v_00_u03b2_3564_);
lean_dec(v_00_u03b1_3563_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
lean_dec_ref(v_args_3549_);
lean_dec(v_a_3544_);
lean_dec_ref(v_k_3511_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
return v___x_3567_;
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v_args_3549_);
lean_dec(v_a_3544_);
lean_dec_ref(v_k_3511_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
v_a_3619_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3556_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3556_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v___x_3523_);
lean_dec_ref(v_k_3511_);
lean_dec_ref(v_val_3510_);
lean_dec_ref(v_F_3509_);
lean_dec_ref(v_x_3508_);
v_a_3627_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3543_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3543_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3639_, lean_object* v_body_3640_, lean_object* v_k_3641_, lean_object* v___x_3642_, uint8_t v___x_3643_, uint8_t v___x_3644_, lean_object* v_FNew_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
lean_inc_ref(v_FNew_3645_);
lean_inc_ref(v___x_3639_);
v___x_3653_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3639_, v_FNew_3645_, v_body_3640_, v_k_3641_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = lean_mk_empty_array_with_capacity(v___x_3642_);
v___x_3656_ = lean_array_push(v___x_3655_, v___x_3639_);
v___x_3657_ = lean_array_push(v___x_3656_, v_FNew_3645_);
v___x_3658_ = 1;
v___x_3659_ = l_Lean_Meta_mkLambdaFVars(v___x_3657_, v_a_3654_, v___x_3643_, v___x_3644_, v___x_3643_, v___x_3644_, v___x_3658_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec_ref(v___x_3657_);
return v___x_3659_;
}
else
{
lean_dec_ref(v_FNew_3645_);
lean_dec_ref(v___x_3639_);
return v___x_3653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3660_, lean_object* v_body_3661_, lean_object* v_k_3662_, lean_object* v___x_3663_, lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v_FNew_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v___x_6949__boxed_3674_; uint8_t v___x_6950__boxed_3675_; lean_object* v_res_3676_; 
v___x_6949__boxed_3674_ = lean_unbox(v___x_3664_);
v___x_6950__boxed_3675_ = lean_unbox(v___x_3665_);
v_res_3676_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3660_, v_body_3661_, v_k_3662_, v___x_3663_, v___x_6949__boxed_3674_, v___x_6950__boxed_3675_, v_FNew_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___x_3663_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3677_, lean_object* v___x_3678_, lean_object* v_00_u03b1_3679_, lean_object* v_00_u03b2_3680_, lean_object* v___x_3681_, lean_object* v_ctorName_3682_, lean_object* v_k_3683_, lean_object* v___x_3684_, uint8_t v___x_3685_, uint8_t v___x_3686_, lean_object* v_a_3687_, lean_object* v_x_3688_, lean_object* v_xs_3689_, lean_object* v_body_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3698_ = lean_array_get_borrowed(v___x_3677_, v_xs_3689_, v___x_3678_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v_00_u03b1_3679_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_00_u03b2_3680_);
lean_inc(v___x_3698_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3698_);
v___x_3702_ = lean_mk_empty_array_with_capacity(v___x_3681_);
v___x_3703_ = lean_array_push(v___x_3702_, v___x_3699_);
v___x_3704_ = lean_array_push(v___x_3703_, v___x_3700_);
v___x_3705_ = lean_array_push(v___x_3704_, v___x_3701_);
v___x_3706_ = l_Lean_Meta_mkAppOptM(v_ctorName_3682_, v___x_3705_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___f_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = lean_box(v___x_3685_);
v___x_3709_ = lean_box(v___x_3686_);
lean_inc(v___x_3698_);
v___f_3710_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3710_, 0, v___x_3698_);
lean_closure_set(v___f_3710_, 1, v_body_3690_);
lean_closure_set(v___f_3710_, 2, v_k_3683_);
lean_closure_set(v___f_3710_, 3, v___x_3684_);
lean_closure_set(v___f_3710_, 4, v___x_3708_);
lean_closure_set(v___f_3710_, 5, v___x_3709_);
v___x_3711_ = l_Lean_LocalDecl_type(v_a_3687_);
v___x_3712_ = l_Lean_Expr_replaceFVar(v___x_3711_, v_x_3688_, v_a_3707_);
lean_dec(v_a_3707_);
lean_dec_ref(v___x_3711_);
v___x_3713_ = l_Lean_LocalDecl_userName(v_a_3687_);
v___x_3714_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3713_, v___x_3712_, v___f_3710_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3714_;
}
else
{
lean_dec_ref(v_body_3690_);
lean_dec_ref(v_x_3688_);
lean_dec(v___x_3684_);
lean_dec_ref(v_k_3683_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3715_ = _args[0];
lean_object* v___x_3716_ = _args[1];
lean_object* v_00_u03b1_3717_ = _args[2];
lean_object* v_00_u03b2_3718_ = _args[3];
lean_object* v___x_3719_ = _args[4];
lean_object* v_ctorName_3720_ = _args[5];
lean_object* v_k_3721_ = _args[6];
lean_object* v___x_3722_ = _args[7];
lean_object* v___x_3723_ = _args[8];
lean_object* v___x_3724_ = _args[9];
lean_object* v_a_3725_ = _args[10];
lean_object* v_x_3726_ = _args[11];
lean_object* v_xs_3727_ = _args[12];
lean_object* v_body_3728_ = _args[13];
lean_object* v___y_3729_ = _args[14];
lean_object* v___y_3730_ = _args[15];
lean_object* v___y_3731_ = _args[16];
lean_object* v___y_3732_ = _args[17];
lean_object* v___y_3733_ = _args[18];
lean_object* v___y_3734_ = _args[19];
lean_object* v___y_3735_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3736_; uint8_t v___x_6971__boxed_3737_; lean_object* v_res_3738_; 
v___x_6970__boxed_3736_ = lean_unbox(v___x_3723_);
v___x_6971__boxed_3737_ = lean_unbox(v___x_3724_);
v_res_3738_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3715_, v___x_3716_, v_00_u03b1_3717_, v_00_u03b2_3718_, v___x_3719_, v_ctorName_3720_, v_k_3721_, v___x_3722_, v___x_6970__boxed_3736_, v___x_6971__boxed_3737_, v_a_3725_, v_x_3726_, v_xs_3727_, v_body_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec_ref(v_xs_3727_);
lean_dec_ref(v_a_3725_);
lean_dec(v___x_3719_);
lean_dec(v___x_3716_);
lean_dec_ref(v___x_3715_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3739_, lean_object* v___x_3740_, lean_object* v_00_u03b1_3741_, lean_object* v_00_u03b2_3742_, lean_object* v___x_3743_, lean_object* v_k_3744_, lean_object* v___x_3745_, uint8_t v___x_3746_, uint8_t v___x_3747_, lean_object* v_a_3748_, lean_object* v_x_3749_, lean_object* v___x_3750_, lean_object* v_ctorName_3751_, lean_object* v_minor_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; 
v___x_3760_ = lean_box(v___x_3746_);
v___x_3761_ = lean_box(v___x_3747_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3762_, 0, v___x_3739_);
lean_closure_set(v___f_3762_, 1, v___x_3740_);
lean_closure_set(v___f_3762_, 2, v_00_u03b1_3741_);
lean_closure_set(v___f_3762_, 3, v_00_u03b2_3742_);
lean_closure_set(v___f_3762_, 4, v___x_3743_);
lean_closure_set(v___f_3762_, 5, v_ctorName_3751_);
lean_closure_set(v___f_3762_, 6, v_k_3744_);
lean_closure_set(v___f_3762_, 7, v___x_3745_);
lean_closure_set(v___f_3762_, 8, v___x_3760_);
lean_closure_set(v___f_3762_, 9, v___x_3761_);
lean_closure_set(v___f_3762_, 10, v_a_3748_);
lean_closure_set(v___f_3762_, 11, v_x_3749_);
v___x_3763_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3752_, v___x_3750_, v___f_3762_, v___x_3746_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3764_ = _args[0];
lean_object* v___x_3765_ = _args[1];
lean_object* v_00_u03b1_3766_ = _args[2];
lean_object* v_00_u03b2_3767_ = _args[3];
lean_object* v___x_3768_ = _args[4];
lean_object* v_k_3769_ = _args[5];
lean_object* v___x_3770_ = _args[6];
lean_object* v___x_3771_ = _args[7];
lean_object* v___x_3772_ = _args[8];
lean_object* v_a_3773_ = _args[9];
lean_object* v_x_3774_ = _args[10];
lean_object* v___x_3775_ = _args[11];
lean_object* v_ctorName_3776_ = _args[12];
lean_object* v_minor_3777_ = _args[13];
lean_object* v___y_3778_ = _args[14];
lean_object* v___y_3779_ = _args[15];
lean_object* v___y_3780_ = _args[16];
lean_object* v___y_3781_ = _args[17];
lean_object* v___y_3782_ = _args[18];
lean_object* v___y_3783_ = _args[19];
lean_object* v___y_3784_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3785_; uint8_t v___x_6935__boxed_3786_; lean_object* v_res_3787_; 
v___x_6934__boxed_3785_ = lean_unbox(v___x_3771_);
v___x_6935__boxed_3786_ = lean_unbox(v___x_3772_);
v_res_3787_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3764_, v___x_3765_, v_00_u03b1_3766_, v_00_u03b2_3767_, v___x_3768_, v_k_3769_, v___x_3770_, v___x_6934__boxed_3785_, v___x_6935__boxed_3786_, v_a_3773_, v_x_3774_, v___x_3775_, v_ctorName_3776_, v_minor_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3788_, lean_object* v_F_3789_, lean_object* v_val_3790_, lean_object* v_k_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3788_, v_F_3789_, v_val_3790_, v_k_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3800_, lean_object* v_name_3801_, uint8_t v_bi_3802_, lean_object* v_type_3803_, lean_object* v_k_3804_, uint8_t v_kind_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3801_, v_bi_3802_, v_type_3803_, v_k_3804_, v_kind_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3814_, lean_object* v_name_3815_, lean_object* v_bi_3816_, lean_object* v_type_3817_, lean_object* v_k_3818_, lean_object* v_kind_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v_bi_boxed_3827_; uint8_t v_kind_boxed_3828_; lean_object* v_res_3829_; 
v_bi_boxed_3827_ = lean_unbox(v_bi_3816_);
v_kind_boxed_3828_ = lean_unbox(v_kind_3819_);
v_res_3829_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3814_, v_name_3815_, v_bi_boxed_3827_, v_type_3817_, v_k_3818_, v_kind_boxed_3828_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3830_, lean_object* v_name_3831_, lean_object* v_type_3832_, lean_object* v_k_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3831_, v_type_3832_, v_k_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3842_, lean_object* v_name_3843_, lean_object* v_type_3844_, lean_object* v_k_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3842_, v_name_3843_, v_type_3844_, v_k_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3853_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3874__overap_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3864_ = lean_panic_fn_borrowed(v___x_3863_, v_msg_3855_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
v___x_3865_ = lean_apply_7(v___x_3874__overap_3864_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, lean_box(0));
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3874_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3879_ = lean_unsigned_to_nat(49u);
v___x_3880_ = lean_unsigned_to_nat(186u);
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3883_ = l_mkPanicMessageWithDecl(v___x_3882_, v___x_3881_, v___x_3880_, v___x_3879_, v___x_3878_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3889_, lean_object* v_a_3890_, lean_object* v_k_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v_FNew_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
uint8_t v___x_4042__boxed_3905_; uint8_t v___x_4043__boxed_3906_; uint8_t v___x_4044__boxed_3907_; lean_object* v_res_3908_; 
v___x_4042__boxed_3905_ = lean_unbox(v___x_3894_);
v___x_4043__boxed_3906_ = lean_unbox(v___x_3895_);
v___x_4044__boxed_3907_ = lean_unbox(v___x_3896_);
v_res_3908_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3889_, v_a_3890_, v_k_3891_, v___x_3892_, v___x_3893_, v___x_4042__boxed_3905_, v___x_4043__boxed_3906_, v___x_4044__boxed_3907_, v_FNew_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___x_3892_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3909_, lean_object* v___x_3910_, lean_object* v___x_3911_, lean_object* v___x_3912_, uint8_t v___x_3913_, uint8_t v___x_3914_, lean_object* v_00_u03b1_3915_, lean_object* v_00_u03b2_3916_, lean_object* v___x_3917_, lean_object* v_k_3918_, lean_object* v___x_3919_, lean_object* v_a_3920_, lean_object* v_x_3921_, lean_object* v_xs_3922_, lean_object* v_body_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; lean_object* v___x_3937_; 
v___x_3931_ = lean_array_get(v___x_3909_, v_xs_3922_, v___x_3910_);
v___x_3932_ = lean_array_get(v___x_3909_, v_xs_3922_, v___x_3911_);
v___x_3933_ = lean_array_get_size(v_xs_3922_);
v___x_3934_ = l_Array_toSubarray___redArg(v_xs_3922_, v___x_3912_, v___x_3933_);
v___x_3935_ = l_Subarray_copy___redArg(v___x_3934_);
v___x_3936_ = 1;
v___x_3937_ = l_Lean_Meta_mkLambdaFVars(v___x_3935_, v_body_3923_, v___x_3913_, v___x_3914_, v___x_3913_, v___x_3914_, v___x_3936_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec_ref(v___x_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3964_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3964_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3964_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3941_ == 0)
{
lean_ctor_set_tag(v___x_3940_, 1);
lean_ctor_set(v___x_3940_, 0, v_00_u03b1_3915_);
v___x_3944_ = v___x_3940_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_00_u03b1_3915_);
v___x_3944_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_00_u03b2_3916_);
lean_inc(v___x_3931_);
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3931_);
lean_inc(v___x_3932_);
v___x_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3932_);
v___x_3948_ = lean_mk_empty_array_with_capacity(v___x_3917_);
v___x_3949_ = lean_array_push(v___x_3948_, v___x_3944_);
v___x_3950_ = lean_array_push(v___x_3949_, v___x_3945_);
v___x_3951_ = lean_array_push(v___x_3950_, v___x_3946_);
v___x_3952_ = lean_array_push(v___x_3951_, v___x_3947_);
v___x_3953_ = l_Lean_Meta_mkAppOptM(v___x_3942_, v___x_3952_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_box(v___x_3913_);
v___x_3956_ = lean_box(v___x_3914_);
v___x_3957_ = lean_box(v___x_3936_);
v___f_3958_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3958_, 0, v___x_3932_);
lean_closure_set(v___f_3958_, 1, v_a_3938_);
lean_closure_set(v___f_3958_, 2, v_k_3918_);
lean_closure_set(v___f_3958_, 3, v___x_3919_);
lean_closure_set(v___f_3958_, 4, v___x_3931_);
lean_closure_set(v___f_3958_, 5, v___x_3955_);
lean_closure_set(v___f_3958_, 6, v___x_3956_);
lean_closure_set(v___f_3958_, 7, v___x_3957_);
v___x_3959_ = l_Lean_LocalDecl_type(v_a_3920_);
v___x_3960_ = l_Lean_Expr_replaceFVar(v___x_3959_, v_x_3921_, v_a_3954_);
lean_dec(v_a_3954_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = l_Lean_LocalDecl_userName(v_a_3920_);
v___x_3962_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3961_, v___x_3960_, v___f_3958_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
return v___x_3962_;
}
else
{
lean_dec(v_a_3938_);
lean_dec(v___x_3932_);
lean_dec(v___x_3931_);
lean_dec_ref(v_x_3921_);
lean_dec(v___x_3919_);
lean_dec_ref(v_k_3918_);
return v___x_3953_;
}
}
}
}
else
{
lean_dec(v___x_3932_);
lean_dec(v___x_3931_);
lean_dec_ref(v_x_3921_);
lean_dec(v___x_3919_);
lean_dec_ref(v_k_3918_);
lean_dec_ref(v_00_u03b2_3916_);
lean_dec_ref(v_00_u03b1_3915_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3965_ = _args[0];
lean_object* v___x_3966_ = _args[1];
lean_object* v___x_3967_ = _args[2];
lean_object* v___x_3968_ = _args[3];
lean_object* v___x_3969_ = _args[4];
lean_object* v___x_3970_ = _args[5];
lean_object* v_00_u03b1_3971_ = _args[6];
lean_object* v_00_u03b2_3972_ = _args[7];
lean_object* v___x_3973_ = _args[8];
lean_object* v_k_3974_ = _args[9];
lean_object* v___x_3975_ = _args[10];
lean_object* v_a_3976_ = _args[11];
lean_object* v_x_3977_ = _args[12];
lean_object* v_xs_3978_ = _args[13];
lean_object* v_body_3979_ = _args[14];
lean_object* v___y_3980_ = _args[15];
lean_object* v___y_3981_ = _args[16];
lean_object* v___y_3982_ = _args[17];
lean_object* v___y_3983_ = _args[18];
lean_object* v___y_3984_ = _args[19];
lean_object* v___y_3985_ = _args[20];
lean_object* v___y_3986_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_3987_; uint8_t v___x_4070__boxed_3988_; lean_object* v_res_3989_; 
v___x_4069__boxed_3987_ = lean_unbox(v___x_3969_);
v___x_4070__boxed_3988_ = lean_unbox(v___x_3970_);
v_res_3989_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3965_, v___x_3966_, v___x_3967_, v___x_3968_, v___x_4069__boxed_3987_, v___x_4070__boxed_3988_, v_00_u03b1_3971_, v_00_u03b2_3972_, v___x_3973_, v_k_3974_, v___x_3975_, v_a_3976_, v_x_3977_, v_xs_3978_, v_body_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v_a_3976_);
lean_dec(v___x_3973_);
lean_dec(v___x_3967_);
lean_dec(v___x_3966_);
lean_dec_ref(v___x_3965_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3993_, lean_object* v_F_3994_, lean_object* v_val_3995_, lean_object* v_k_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___y_4014_; uint8_t v___x_4106_; 
v___x_4106_ = l_Lean_Expr_isFVar(v_x_3993_);
if (v___x_4106_ == 0)
{
v___y_4014_ = v___x_4106_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4108_ = lean_unsigned_to_nat(5u);
v___x_4109_ = l_Lean_Expr_isAppOfArity(v_val_3995_, v___x_4107_, v___x_4108_);
v___y_4014_ = v___x_4109_;
goto v___jp_4013_;
}
v___jp_4004_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4012_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4011_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
v___jp_4013_:
{
if (v___y_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec_ref(v_x_3993_);
lean_inc(v_a_4002_);
lean_inc_ref(v_a_4001_);
lean_inc(v_a_4000_);
lean_inc_ref(v_a_3999_);
lean_inc(v_a_3998_);
lean_inc_ref(v_a_3997_);
v___x_4015_ = lean_apply_9(v_k_3996_, v_F_3994_, v_val_3995_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, lean_box(0));
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4016_ = lean_unsigned_to_nat(3u);
v___x_4017_ = l_Lean_Expr_getAppNumArgs(v_val_3995_);
v___x_4018_ = lean_nat_sub(v___x_4017_, v___x_4016_);
v___x_4019_ = lean_unsigned_to_nat(1u);
v___x_4020_ = lean_nat_sub(v___x_4018_, v___x_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = l_Lean_Expr_getRevArg_x21(v_val_3995_, v___x_4020_);
v___x_4022_ = lean_expr_eqv(v___x_4021_, v_x_3993_);
lean_dec_ref(v___x_4021_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
lean_dec(v___x_4017_);
lean_dec_ref(v_x_3993_);
lean_inc(v_a_4002_);
lean_inc_ref(v_a_4001_);
lean_inc(v_a_4000_);
lean_inc_ref(v_a_3999_);
lean_inc(v_a_3998_);
lean_inc_ref(v_a_3997_);
v___x_4023_ = lean_apply_9(v_k_3996_, v_F_3994_, v_val_3995_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, lean_box(0));
return v___x_4023_;
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4024_ = lean_unsigned_to_nat(4u);
v___x_4025_ = lean_nat_sub(v___x_4017_, v___x_4024_);
v___x_4026_ = lean_nat_sub(v___x_4025_, v___x_4019_);
lean_dec(v___x_4025_);
v___x_4027_ = l_Lean_Expr_getRevArg_x21(v_val_3995_, v___x_4026_);
v___x_4028_ = l_Lean_Expr_isLambda(v___x_4027_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; 
lean_dec_ref(v___x_4027_);
lean_dec(v___x_4017_);
lean_dec_ref(v_x_3993_);
lean_inc(v_a_4002_);
lean_inc_ref(v_a_4001_);
lean_inc(v_a_4000_);
lean_inc_ref(v_a_3999_);
lean_inc(v_a_3998_);
lean_inc_ref(v_a_3997_);
v___x_4029_ = lean_apply_9(v_k_3996_, v_F_3994_, v_val_3995_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, lean_box(0));
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4030_ = l_Lean_Expr_bindingBody_x21(v___x_4027_);
lean_dec_ref(v___x_4027_);
v___x_4031_ = l_Lean_Expr_isLambda(v___x_4030_);
lean_dec_ref(v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; 
lean_dec(v___x_4017_);
lean_dec_ref(v_x_3993_);
lean_inc(v_a_4002_);
lean_inc_ref(v_a_4001_);
lean_inc(v_a_4000_);
lean_inc_ref(v_a_3999_);
lean_inc(v_a_3998_);
lean_inc_ref(v_a_3997_);
v___x_4032_ = lean_apply_9(v_k_3996_, v_F_3994_, v_val_3995_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, lean_box(0));
return v___x_4032_;
}
else
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = l_Lean_Expr_getAppFn(v_val_3995_);
v___x_4034_ = l_Lean_Expr_constLevels_x21(v___x_4033_);
lean_dec_ref(v___x_4033_);
if (lean_obj_tag(v___x_4034_) == 1)
{
lean_object* v_tail_4035_; 
v_tail_4035_ = lean_ctor_get(v___x_4034_, 1);
lean_inc(v_tail_4035_);
lean_dec_ref_known(v___x_4034_, 2);
if (lean_obj_tag(v_tail_4035_) == 1)
{
lean_object* v_tail_4036_; 
v_tail_4036_ = lean_ctor_get(v_tail_4035_, 1);
lean_inc(v_tail_4036_);
if (lean_obj_tag(v_tail_4036_) == 1)
{
lean_object* v_tail_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4104_; 
v_tail_4037_ = lean_ctor_get(v_tail_4036_, 1);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_tail_4036_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; 
v_unused_4105_ = lean_ctor_get(v_tail_4036_, 0);
lean_dec(v_unused_4105_);
v___x_4039_ = v_tail_4036_;
v_isShared_4040_ = v_isSharedCheck_4104_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_tail_4037_);
lean_dec(v_tail_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4104_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_tail_4037_) == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = l_Lean_Expr_fvarId_x21(v_F_3994_);
v___x_4042_ = l_Lean_FVarId_getDecl___redArg(v___x_4041_, v_a_3999_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4044_; lean_object* v_dummy_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v_args_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___f_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc_n(v_a_4043_, 2);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = l_Lean_instInhabitedExpr;
v_dummy_4045_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_4017_);
v___x_4046_ = lean_mk_array(v___x_4017_, v_dummy_4045_);
v___x_4047_ = lean_nat_sub(v___x_4017_, v___x_4019_);
lean_dec(v___x_4017_);
v_args_4048_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3995_, v___x_4046_, v___x_4047_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_box(v___x_4028_);
lean_inc_ref(v_x_3993_);
v___f_4051_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4051_, 0, v_a_4043_);
lean_closure_set(v___f_4051_, 1, v___x_4044_);
lean_closure_set(v___f_4051_, 2, v___x_4049_);
lean_closure_set(v___f_4051_, 3, v_x_3993_);
lean_closure_set(v___f_4051_, 4, v___x_4050_);
v___x_4052_ = lean_unsigned_to_nat(2u);
v___x_4053_ = lean_array_get(v___x_4044_, v_args_4048_, v___x_4052_);
v___x_4054_ = 0;
v___x_4055_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4053_, v___f_4051_, v___x_4054_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v_fst_4057_; lean_object* v_snd_4058_; lean_object* v_00_u03b1_4059_; lean_object* v_00_u03b2_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v_fst_4057_ = lean_ctor_get(v_a_4056_, 0);
lean_inc(v_fst_4057_);
v_snd_4058_ = lean_ctor_get(v_a_4056_, 1);
lean_inc(v_snd_4058_);
lean_dec(v_a_4056_);
v_00_u03b1_4059_ = lean_array_get(v___x_4044_, v_args_4048_, v___x_4049_);
v_00_u03b2_4060_ = lean_array_get(v___x_4044_, v_args_4048_, v___x_4019_);
v___x_4061_ = lean_box(v___x_4054_);
v___x_4062_ = lean_box(v___x_4028_);
lean_inc_ref(v_x_3993_);
lean_inc(v_00_u03b2_4060_);
lean_inc(v_00_u03b1_4059_);
v___f_4063_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4063_, 0, v___x_4044_);
lean_closure_set(v___f_4063_, 1, v___x_4049_);
lean_closure_set(v___f_4063_, 2, v___x_4019_);
lean_closure_set(v___f_4063_, 3, v___x_4052_);
lean_closure_set(v___f_4063_, 4, v___x_4061_);
lean_closure_set(v___f_4063_, 5, v___x_4062_);
lean_closure_set(v___f_4063_, 6, v_00_u03b1_4059_);
lean_closure_set(v___f_4063_, 7, v_00_u03b2_4060_);
lean_closure_set(v___f_4063_, 8, v___x_4024_);
lean_closure_set(v___f_4063_, 9, v_k_3996_);
lean_closure_set(v___f_4063_, 10, v___x_4016_);
lean_closure_set(v___f_4063_, 11, v_a_4043_);
lean_closure_set(v___f_4063_, 12, v_x_3993_);
v___x_4064_ = lean_array_get(v___x_4044_, v_args_4048_, v___x_4024_);
lean_dec_ref(v_args_4048_);
v___x_4065_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4064_, v___f_4063_, v___x_4054_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4087_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4087_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4087_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v_tail_4035_);
lean_ctor_set(v___x_4039_, 0, v_snd_4058_);
v___x_4072_ = v___x_4039_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_snd_4058_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_tail_4035_);
v___x_4072_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4073_ = l_Lean_mkConst(v___x_4070_, v___x_4072_);
v___x_4074_ = lean_unsigned_to_nat(6u);
v___x_4075_ = lean_mk_empty_array_with_capacity(v___x_4074_);
v___x_4076_ = lean_array_push(v___x_4075_, v_00_u03b1_4059_);
v___x_4077_ = lean_array_push(v___x_4076_, v_00_u03b2_4060_);
v___x_4078_ = lean_array_push(v___x_4077_, v_fst_4057_);
v___x_4079_ = lean_array_push(v___x_4078_, v_x_3993_);
v___x_4080_ = lean_array_push(v___x_4079_, v_a_4066_);
v___x_4081_ = lean_array_push(v___x_4080_, v_F_3994_);
v___x_4082_ = l_Lean_mkAppN(v___x_4073_, v___x_4081_);
lean_dec_ref(v___x_4081_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4082_);
v___x_4084_ = v___x_4068_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4060_);
lean_dec(v_00_u03b1_4059_);
lean_dec(v_snd_4058_);
lean_dec(v_fst_4057_);
lean_del_object(v___x_4039_);
lean_dec_ref_known(v_tail_4035_, 2);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
return v___x_4065_;
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v_args_4048_);
lean_dec(v_a_4043_);
lean_del_object(v___x_4039_);
lean_dec_ref_known(v_tail_4035_, 2);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v_a_4088_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4055_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4055_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_del_object(v___x_4039_);
lean_dec_ref_known(v_tail_4035_, 2);
lean_dec(v___x_4017_);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_val_3995_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v_a_4096_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4042_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4042_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_del_object(v___x_4039_);
lean_dec(v_tail_4037_);
lean_dec_ref_known(v_tail_4035_, 2);
lean_dec(v___x_4017_);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_val_3995_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
goto v___jp_4004_;
}
}
}
else
{
lean_dec_ref_known(v_tail_4035_, 2);
lean_dec(v_tail_4036_);
lean_dec(v___x_4017_);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_val_3995_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
goto v___jp_4004_;
}
}
else
{
lean_dec(v_tail_4035_);
lean_dec(v___x_4017_);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_val_3995_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
goto v___jp_4004_;
}
}
else
{
lean_dec(v___x_4034_);
lean_dec(v___x_4017_);
lean_dec_ref(v_k_3996_);
lean_dec_ref(v_val_3995_);
lean_dec_ref(v_F_3994_);
lean_dec_ref(v_x_3993_);
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
goto v___jp_4004_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4110_, lean_object* v_a_4111_, lean_object* v_k_4112_, lean_object* v___x_4113_, lean_object* v___x_4114_, uint8_t v___x_4115_, uint8_t v___x_4116_, uint8_t v___x_4117_, lean_object* v_FNew_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; 
lean_inc_ref(v_FNew_4118_);
lean_inc_ref(v___x_4110_);
v___x_4126_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4110_, v_FNew_4118_, v_a_4111_, v_k_4112_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = lean_mk_empty_array_with_capacity(v___x_4113_);
v___x_4129_ = lean_array_push(v___x_4128_, v___x_4114_);
v___x_4130_ = lean_array_push(v___x_4129_, v___x_4110_);
v___x_4131_ = lean_array_push(v___x_4130_, v_FNew_4118_);
v___x_4132_ = l_Lean_Meta_mkLambdaFVars(v___x_4131_, v_a_4127_, v___x_4115_, v___x_4116_, v___x_4115_, v___x_4116_, v___x_4117_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec_ref(v___x_4131_);
return v___x_4132_;
}
else
{
lean_dec_ref(v_FNew_4118_);
lean_dec_ref(v___x_4114_);
lean_dec_ref(v___x_4110_);
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4133_, lean_object* v_F_4134_, lean_object* v_val_4135_, lean_object* v_k_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4133_, v_F_4134_, v_val_4135_, v_k_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_ref_4159_; uint8_t v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref_known(v___x_4158_, 1);
v_ref_4159_ = lean_ctor_get(v___y_4155_, 5);
v___x_4160_ = 0;
v___x_4161_ = l_Lean_SourceInfo_fromRef(v_ref_4159_, v___x_4160_);
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4161_);
v___x_4164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4161_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_Syntax_node1(v___x_4161_, v___x_4162_, v___x_4164_);
v___x_4166_ = l_Lean_Elab_Tactic_evalTactic(v___x_4165_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4166_;
}
else
{
return v___x_4158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___f_4186_; lean_object* v___x_4187_; 
v___f_4186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4187_ = l_Lean_Elab_Tactic_run(v_mvarId_4178_, v___f_4186_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4198_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
uint8_t v___x_4192_; 
v___x_4192_ = l_List_isEmpty___redArg(v_a_4188_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
lean_del_object(v___x_4190_);
v___x_4193_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4188_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
return v___x_4193_;
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
lean_dec(v_a_4188_);
v___x_4194_ = lean_box(0);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4194_);
v___x_4196_ = v___x_4190_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4187_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4187_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4216_, lean_object* v_x_4217_, lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
lean_object* v_ks_4220_; lean_object* v_vs_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4245_; 
v_ks_4220_ = lean_ctor_get(v_x_4216_, 0);
v_vs_4221_ = lean_ctor_get(v_x_4216_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_x_4216_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4223_ = v_x_4216_;
v_isShared_4224_ = v_isSharedCheck_4245_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_vs_4221_);
lean_inc(v_ks_4220_);
lean_dec(v_x_4216_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4245_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4225_ = lean_array_get_size(v_ks_4220_);
v___x_4226_ = lean_nat_dec_lt(v_x_4217_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
lean_dec(v_x_4217_);
v___x_4227_ = lean_array_push(v_ks_4220_, v_x_4218_);
v___x_4228_ = lean_array_push(v_vs_4221_, v_x_4219_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 1, v___x_4228_);
lean_ctor_set(v___x_4223_, 0, v___x_4227_);
v___x_4230_ = v___x_4223_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
else
{
lean_object* v_k_x27_4232_; uint8_t v___x_4233_; 
v_k_x27_4232_ = lean_array_fget_borrowed(v_ks_4220_, v_x_4217_);
v___x_4233_ = l_Lean_instBEqMVarId_beq(v_x_4218_, v_k_x27_4232_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4235_; 
if (v_isShared_4224_ == 0)
{
v___x_4235_ = v___x_4223_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_ks_4220_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_vs_4221_);
v___x_4235_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_unsigned_to_nat(1u);
v___x_4237_ = lean_nat_add(v_x_4217_, v___x_4236_);
lean_dec(v_x_4217_);
v_x_4216_ = v___x_4235_;
v_x_4217_ = v___x_4237_;
goto _start;
}
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4240_ = lean_array_fset(v_ks_4220_, v_x_4217_, v_x_4218_);
v___x_4241_ = lean_array_fset(v_vs_4221_, v_x_4217_, v_x_4219_);
lean_dec(v_x_4217_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 1, v___x_4241_);
lean_ctor_set(v___x_4223_, 0, v___x_4240_);
v___x_4243_ = v___x_4223_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4246_, lean_object* v_k_4247_, lean_object* v_v_4248_){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4246_, v___x_4249_, v_k_4247_, v_v_4248_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4252_, size_t v_x_4253_, size_t v_x_4254_, lean_object* v_x_4255_, lean_object* v_x_4256_){
_start:
{
if (lean_obj_tag(v_x_4252_) == 0)
{
lean_object* v_es_4257_; size_t v___x_4258_; size_t v___x_4259_; lean_object* v_j_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_es_4257_ = lean_ctor_get(v_x_4252_, 0);
v___x_4258_ = ((size_t)31ULL);
v___x_4259_ = lean_usize_land(v_x_4253_, v___x_4258_);
v_j_4260_ = lean_usize_to_nat(v___x_4259_);
v___x_4261_ = lean_array_get_size(v_es_4257_);
v___x_4262_ = lean_nat_dec_lt(v_j_4260_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_dec(v_j_4260_);
lean_dec(v_x_4256_);
lean_dec(v_x_4255_);
return v_x_4252_;
}
else
{
lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4301_; 
lean_inc_ref(v_es_4257_);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_x_4252_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; 
v_unused_4302_ = lean_ctor_get(v_x_4252_, 0);
lean_dec(v_unused_4302_);
v___x_4264_ = v_x_4252_;
v_isShared_4265_ = v_isSharedCheck_4301_;
goto v_resetjp_4263_;
}
else
{
lean_dec(v_x_4252_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4301_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v_v_4266_; lean_object* v___x_4267_; lean_object* v_xs_x27_4268_; lean_object* v___y_4270_; 
v_v_4266_ = lean_array_fget(v_es_4257_, v_j_4260_);
v___x_4267_ = lean_box(0);
v_xs_x27_4268_ = lean_array_fset(v_es_4257_, v_j_4260_, v___x_4267_);
switch(lean_obj_tag(v_v_4266_))
{
case 0:
{
lean_object* v_key_4275_; lean_object* v_val_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4286_; 
v_key_4275_ = lean_ctor_get(v_v_4266_, 0);
v_val_4276_ = lean_ctor_get(v_v_4266_, 1);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_v_4266_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4278_ = v_v_4266_;
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_val_4276_);
lean_inc(v_key_4275_);
lean_dec(v_v_4266_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
uint8_t v___x_4280_; 
v___x_4280_ = l_Lean_instBEqMVarId_beq(v_x_4255_, v_key_4275_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_del_object(v___x_4278_);
v___x_4281_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4275_, v_val_4276_, v_x_4255_, v_x_4256_);
v___x_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v___y_4270_ = v___x_4282_;
goto v___jp_4269_;
}
else
{
lean_object* v___x_4284_; 
lean_dec(v_val_4276_);
lean_dec(v_key_4275_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 1, v_x_4256_);
lean_ctor_set(v___x_4278_, 0, v_x_4255_);
v___x_4284_ = v___x_4278_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_x_4255_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_x_4256_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4270_ = v___x_4284_;
goto v___jp_4269_;
}
}
}
}
case 1:
{
lean_object* v_node_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4299_; 
v_node_4287_ = lean_ctor_get(v_v_4266_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_v_4266_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4289_ = v_v_4266_;
v_isShared_4290_ = v_isSharedCheck_4299_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_node_4287_);
lean_dec(v_v_4266_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4299_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
size_t v___x_4291_; size_t v___x_4292_; size_t v___x_4293_; size_t v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4291_ = ((size_t)5ULL);
v___x_4292_ = lean_usize_shift_right(v_x_4253_, v___x_4291_);
v___x_4293_ = ((size_t)1ULL);
v___x_4294_ = lean_usize_add(v_x_4254_, v___x_4293_);
v___x_4295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4287_, v___x_4292_, v___x_4294_, v_x_4255_, v_x_4256_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 0, v___x_4295_);
v___x_4297_ = v___x_4289_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
v___y_4270_ = v___x_4297_;
goto v___jp_4269_;
}
}
}
default: 
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4300_, 0, v_x_4255_);
lean_ctor_set(v___x_4300_, 1, v_x_4256_);
v___y_4270_ = v___x_4300_;
goto v___jp_4269_;
}
}
v___jp_4269_:
{
lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4271_ = lean_array_fset(v_xs_x27_4268_, v_j_4260_, v___y_4270_);
lean_dec(v_j_4260_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4271_);
v___x_4273_ = v___x_4264_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_object* v_ks_4303_; lean_object* v_vs_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4324_; 
v_ks_4303_ = lean_ctor_get(v_x_4252_, 0);
v_vs_4304_ = lean_ctor_get(v_x_4252_, 1);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_x_4252_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4306_ = v_x_4252_;
v_isShared_4307_ = v_isSharedCheck_4324_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_vs_4304_);
lean_inc(v_ks_4303_);
lean_dec(v_x_4252_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4324_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_ks_4303_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_vs_4304_);
v___x_4309_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v_newNode_4310_; uint8_t v___y_4312_; size_t v___x_4318_; uint8_t v___x_4319_; 
v_newNode_4310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4309_, v_x_4255_, v_x_4256_);
v___x_4318_ = ((size_t)7ULL);
v___x_4319_ = lean_usize_dec_le(v___x_4318_, v_x_4254_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4320_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4310_);
v___x_4321_ = lean_unsigned_to_nat(4u);
v___x_4322_ = lean_nat_dec_lt(v___x_4320_, v___x_4321_);
lean_dec(v___x_4320_);
v___y_4312_ = v___x_4322_;
goto v___jp_4311_;
}
else
{
v___y_4312_ = v___x_4319_;
goto v___jp_4311_;
}
v___jp_4311_:
{
if (v___y_4312_ == 0)
{
lean_object* v_ks_4313_; lean_object* v_vs_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_ks_4313_ = lean_ctor_get(v_newNode_4310_, 0);
lean_inc_ref(v_ks_4313_);
v_vs_4314_ = lean_ctor_get(v_newNode_4310_, 1);
lean_inc_ref(v_vs_4314_);
lean_dec_ref(v_newNode_4310_);
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4317_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4254_, v_ks_4313_, v_vs_4314_, v___x_4315_, v___x_4316_);
lean_dec_ref(v_vs_4314_);
lean_dec_ref(v_ks_4313_);
return v___x_4317_;
}
else
{
return v_newNode_4310_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4325_, lean_object* v_keys_4326_, lean_object* v_vals_4327_, lean_object* v_i_4328_, lean_object* v_entries_4329_){
_start:
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = lean_array_get_size(v_keys_4326_);
v___x_4331_ = lean_nat_dec_lt(v_i_4328_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_dec(v_i_4328_);
return v_entries_4329_;
}
else
{
lean_object* v_k_4332_; lean_object* v_v_4333_; uint64_t v___x_4334_; size_t v_h_4335_; size_t v___x_4336_; lean_object* v___x_4337_; size_t v___x_4338_; size_t v___x_4339_; size_t v___x_4340_; size_t v_h_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v_k_4332_ = lean_array_fget_borrowed(v_keys_4326_, v_i_4328_);
v_v_4333_ = lean_array_fget_borrowed(v_vals_4327_, v_i_4328_);
v___x_4334_ = l_Lean_instHashableMVarId_hash(v_k_4332_);
v_h_4335_ = lean_uint64_to_usize(v___x_4334_);
v___x_4336_ = ((size_t)5ULL);
v___x_4337_ = lean_unsigned_to_nat(1u);
v___x_4338_ = ((size_t)1ULL);
v___x_4339_ = lean_usize_sub(v_depth_4325_, v___x_4338_);
v___x_4340_ = lean_usize_mul(v___x_4336_, v___x_4339_);
v_h_4341_ = lean_usize_shift_right(v_h_4335_, v___x_4340_);
v___x_4342_ = lean_nat_add(v_i_4328_, v___x_4337_);
lean_dec(v_i_4328_);
lean_inc(v_v_4333_);
lean_inc(v_k_4332_);
v___x_4343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4329_, v_h_4341_, v_depth_4325_, v_k_4332_, v_v_4333_);
v_i_4328_ = v___x_4342_;
v_entries_4329_ = v___x_4343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4345_, lean_object* v_keys_4346_, lean_object* v_vals_4347_, lean_object* v_i_4348_, lean_object* v_entries_4349_){
_start:
{
size_t v_depth_boxed_4350_; lean_object* v_res_4351_; 
v_depth_boxed_4350_ = lean_unbox_usize(v_depth_4345_);
lean_dec(v_depth_4345_);
v_res_4351_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4350_, v_keys_4346_, v_vals_4347_, v_i_4348_, v_entries_4349_);
lean_dec_ref(v_vals_4347_);
lean_dec_ref(v_keys_4346_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4352_, lean_object* v_x_4353_, lean_object* v_x_4354_, lean_object* v_x_4355_, lean_object* v_x_4356_){
_start:
{
size_t v_x_4249__boxed_4357_; size_t v_x_4250__boxed_4358_; lean_object* v_res_4359_; 
v_x_4249__boxed_4357_ = lean_unbox_usize(v_x_4353_);
lean_dec(v_x_4353_);
v_x_4250__boxed_4358_ = lean_unbox_usize(v_x_4354_);
lean_dec(v_x_4354_);
v_res_4359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4352_, v_x_4249__boxed_4357_, v_x_4250__boxed_4358_, v_x_4355_, v_x_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4360_, lean_object* v_x_4361_, lean_object* v_x_4362_){
_start:
{
uint64_t v___x_4363_; size_t v___x_4364_; size_t v___x_4365_; lean_object* v___x_4366_; 
v___x_4363_ = l_Lean_instHashableMVarId_hash(v_x_4361_);
v___x_4364_ = lean_uint64_to_usize(v___x_4363_);
v___x_4365_ = ((size_t)1ULL);
v___x_4366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4360_, v___x_4364_, v___x_4365_, v_x_4361_, v_x_4362_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4367_, lean_object* v_val_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___x_4371_; lean_object* v_mctx_4372_; lean_object* v_cache_4373_; lean_object* v_zetaDeltaFVarIds_4374_; lean_object* v_postponed_4375_; lean_object* v_diag_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4404_; 
v___x_4371_ = lean_st_ref_take(v___y_4369_);
v_mctx_4372_ = lean_ctor_get(v___x_4371_, 0);
v_cache_4373_ = lean_ctor_get(v___x_4371_, 1);
v_zetaDeltaFVarIds_4374_ = lean_ctor_get(v___x_4371_, 2);
v_postponed_4375_ = lean_ctor_get(v___x_4371_, 3);
v_diag_4376_ = lean_ctor_get(v___x_4371_, 4);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4378_ = v___x_4371_;
v_isShared_4379_ = v_isSharedCheck_4404_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_diag_4376_);
lean_inc(v_postponed_4375_);
lean_inc(v_zetaDeltaFVarIds_4374_);
lean_inc(v_cache_4373_);
lean_inc(v_mctx_4372_);
lean_dec(v___x_4371_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4404_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v_depth_4380_; lean_object* v_levelAssignDepth_4381_; lean_object* v_lmvarCounter_4382_; lean_object* v_mvarCounter_4383_; lean_object* v_lDecls_4384_; lean_object* v_decls_4385_; lean_object* v_userNames_4386_; lean_object* v_lAssignment_4387_; lean_object* v_eAssignment_4388_; lean_object* v_dAssignment_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4403_; 
v_depth_4380_ = lean_ctor_get(v_mctx_4372_, 0);
v_levelAssignDepth_4381_ = lean_ctor_get(v_mctx_4372_, 1);
v_lmvarCounter_4382_ = lean_ctor_get(v_mctx_4372_, 2);
v_mvarCounter_4383_ = lean_ctor_get(v_mctx_4372_, 3);
v_lDecls_4384_ = lean_ctor_get(v_mctx_4372_, 4);
v_decls_4385_ = lean_ctor_get(v_mctx_4372_, 5);
v_userNames_4386_ = lean_ctor_get(v_mctx_4372_, 6);
v_lAssignment_4387_ = lean_ctor_get(v_mctx_4372_, 7);
v_eAssignment_4388_ = lean_ctor_get(v_mctx_4372_, 8);
v_dAssignment_4389_ = lean_ctor_get(v_mctx_4372_, 9);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_mctx_4372_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4391_ = v_mctx_4372_;
v_isShared_4392_ = v_isSharedCheck_4403_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_dAssignment_4389_);
lean_inc(v_eAssignment_4388_);
lean_inc(v_lAssignment_4387_);
lean_inc(v_userNames_4386_);
lean_inc(v_decls_4385_);
lean_inc(v_lDecls_4384_);
lean_inc(v_mvarCounter_4383_);
lean_inc(v_lmvarCounter_4382_);
lean_inc(v_levelAssignDepth_4381_);
lean_inc(v_depth_4380_);
lean_dec(v_mctx_4372_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4403_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4393_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4388_, v_mvarId_4367_, v_val_4368_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 8, v___x_4393_);
v___x_4395_ = v___x_4391_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_depth_4380_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_levelAssignDepth_4381_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_lmvarCounter_4382_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v_mvarCounter_4383_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v_lDecls_4384_);
lean_ctor_set(v_reuseFailAlloc_4402_, 5, v_decls_4385_);
lean_ctor_set(v_reuseFailAlloc_4402_, 6, v_userNames_4386_);
lean_ctor_set(v_reuseFailAlloc_4402_, 7, v_lAssignment_4387_);
lean_ctor_set(v_reuseFailAlloc_4402_, 8, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4402_, 9, v_dAssignment_4389_);
v___x_4395_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4397_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4395_);
v___x_4397_ = v___x_4378_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_cache_4373_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_zetaDeltaFVarIds_4374_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v_postponed_4375_);
lean_ctor_set(v_reuseFailAlloc_4401_, 4, v_diag_4376_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_st_ref_set(v___y_4369_, v___x_4397_);
v___x_4399_ = lean_box(0);
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4405_, lean_object* v_val_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4405_, v_val_4406_, v___y_4407_);
lean_dec(v___y_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4414_, lean_object* v_mv_u2082_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4424_; 
lean_inc(v_mv_u2081_4414_);
v___x_4424_ = l_Lean_MVarId_getDecl(v_mv_u2081_4414_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
lean_inc(v_mv_u2082_4415_);
v___x_4426_ = l_Lean_MVarId_getDecl(v_mv_u2082_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v_lctx_4428_; lean_object* v_type_4429_; lean_object* v_lctx_4430_; lean_object* v_type_4431_; uint8_t v___x_4432_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v_lctx_4428_ = lean_ctor_get(v_a_4425_, 1);
lean_inc_ref(v_lctx_4428_);
v_type_4429_ = lean_ctor_get(v_a_4425_, 2);
lean_inc_ref(v_type_4429_);
lean_dec(v_a_4425_);
v_lctx_4430_ = lean_ctor_get(v_a_4427_, 1);
lean_inc_ref(v_lctx_4430_);
v_type_4431_ = lean_ctor_get(v_a_4427_, 2);
lean_inc_ref(v_type_4431_);
lean_dec(v_a_4427_);
v___x_4432_ = lean_expr_eqv(v_type_4429_, v_type_4431_);
lean_dec_ref(v_type_4431_);
lean_dec_ref(v_type_4429_);
if (v___x_4432_ == 0)
{
lean_dec_ref(v_lctx_4430_);
lean_dec_ref(v_lctx_4428_);
lean_dec(v_mv_u2082_4415_);
lean_dec(v_mv_u2081_4414_);
goto v___jp_4421_;
}
else
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4434_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4428_, v_lctx_4430_, v___x_4433_);
if (v___x_4434_ == 0)
{
uint8_t v___x_4435_; 
v___x_4435_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4430_, v_lctx_4428_, v___x_4433_);
lean_dec_ref(v_lctx_4428_);
lean_dec_ref(v_lctx_4430_);
if (v___x_4435_ == 0)
{
lean_dec(v_mv_u2082_4415_);
lean_dec(v_mv_u2081_4414_);
goto v___jp_4421_;
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4447_; 
v___x_4436_ = l_Lean_Expr_mvar___override(v_mv_u2082_4415_);
v___x_4437_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4414_, v___x_4436_, v___y_4417_);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v___x_4437_, 0);
lean_dec(v_unused_4448_);
v___x_4439_ = v___x_4437_;
v_isShared_4440_ = v_isSharedCheck_4447_;
goto v_resetjp_4438_;
}
else
{
lean_dec(v___x_4437_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4447_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4441_ = lean_box(v___x_4434_);
v___x_4442_ = lean_box(v___x_4432_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4441_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4443_);
v___x_4445_ = v___x_4439_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4461_; 
lean_dec_ref(v_lctx_4430_);
lean_dec_ref(v_lctx_4428_);
v___x_4449_ = l_Lean_Expr_mvar___override(v_mv_u2081_4414_);
v___x_4450_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4415_, v___x_4449_, v___y_4417_);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v___x_4450_, 0);
lean_dec(v_unused_4462_);
v___x_4452_ = v___x_4450_;
v_isShared_4453_ = v_isSharedCheck_4461_;
goto v_resetjp_4451_;
}
else
{
lean_dec(v___x_4450_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4461_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
uint8_t v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4454_ = 0;
v___x_4455_ = lean_box(v___x_4432_);
v___x_4456_ = lean_box(v___x_4454_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4455_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v___x_4457_);
v___x_4459_ = v___x_4452_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_a_4425_);
lean_dec(v_mv_u2082_4415_);
lean_dec(v_mv_u2081_4414_);
v_a_4463_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4426_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4426_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_mv_u2082_4415_);
lean_dec(v_mv_u2081_4414_);
v_a_4471_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4424_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4424_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
v___jp_4421_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
return v___x_4423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4479_, lean_object* v_mv_u2082_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4479_, v_mv_u2082_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4487_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4501_, lean_object* v___x_4502_, lean_object* v___x_4503_, lean_object* v___x_4504_, lean_object* v_a_4505_, uint8_t v___x_4506_, lean_object* v_snd_4507_, lean_object* v_fst_4508_, lean_object* v_next_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = lean_apply_7(v_f_4501_, v___x_4502_, v___x_4503_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, lean_box(0));
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4551_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4518_ = v___x_4515_;
v_isShared_4519_ = v_isSharedCheck_4551_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4515_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4551_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v_fst_4520_; lean_object* v_snd_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4550_; 
v_fst_4520_ = lean_ctor_get(v_a_4516_, 0);
v_snd_4521_ = lean_ctor_get(v_a_4516_, 1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_a_4516_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4523_ = v_a_4516_;
v_isShared_4524_ = v_isSharedCheck_4550_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_snd_4521_);
lean_inc(v_fst_4520_);
lean_dec(v_a_4516_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4550_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_removed_4526_; lean_object* v_numRemoved_4527_; uint8_t v___x_4546_; 
v___x_4546_ = lean_unbox(v_fst_4520_);
lean_dec(v_fst_4520_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = lean_nat_add(v_snd_4507_, v___x_4504_);
lean_dec(v_snd_4507_);
v___x_4548_ = lean_box(v___x_4506_);
v___x_4549_ = lean_array_set(v_fst_4508_, v_next_4509_, v___x_4548_);
v_removed_4526_ = v___x_4549_;
v_numRemoved_4527_ = v___x_4547_;
goto v___jp_4525_;
}
else
{
v_removed_4526_ = v_fst_4508_;
v_numRemoved_4527_ = v_snd_4507_;
goto v___jp_4525_;
}
v___jp_4525_:
{
uint8_t v___x_4528_; 
v___x_4528_ = lean_unbox(v_snd_4521_);
lean_dec(v_snd_4521_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4529_ = lean_nat_add(v_numRemoved_4527_, v___x_4504_);
lean_dec(v_numRemoved_4527_);
v___x_4530_ = lean_box(v___x_4506_);
v___x_4531_ = lean_array_set(v_removed_4526_, v_a_4505_, v___x_4530_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 1, v___x_4529_);
lean_ctor_set(v___x_4523_, 0, v___x_4531_);
v___x_4533_ = v___x_4523_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___x_4529_);
v___x_4533_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4536_; 
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v___x_4534_);
v___x_4536_ = v___x_4518_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
else
{
lean_object* v___x_4540_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 1, v_numRemoved_4527_);
lean_ctor_set(v___x_4523_, 0, v_removed_4526_);
v___x_4540_ = v___x_4523_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_removed_4526_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v_numRemoved_4527_);
v___x_4540_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v___x_4541_);
v___x_4543_ = v___x_4518_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_fst_4508_);
lean_dec(v_snd_4507_);
v_a_4552_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4515_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4515_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4560_, lean_object* v___x_4561_, lean_object* v___x_4562_, lean_object* v___x_4563_, lean_object* v_a_4564_, lean_object* v___x_4565_, lean_object* v_snd_4566_, lean_object* v_fst_4567_, lean_object* v_next_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v___x_4626__boxed_4574_; lean_object* v_res_4575_; 
v___x_4626__boxed_4574_ = lean_unbox(v___x_4565_);
v_res_4575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4560_, v___x_4561_, v___x_4562_, v___x_4563_, v_a_4564_, v___x_4626__boxed_4574_, v_snd_4566_, v_fst_4567_, v_next_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v_next_4568_);
lean_dec(v_a_4564_);
lean_dec(v___x_4563_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4576_, lean_object* v_a_4577_, lean_object* v_next_4578_, lean_object* v_f_4579_, lean_object* v_a_4580_, lean_object* v_b_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
uint8_t v___x_4587_; 
v___x_4587_ = lean_nat_dec_lt(v_a_4580_, v_upperBound_4576_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; 
lean_dec(v_a_4580_);
lean_dec_ref(v_f_4579_);
lean_dec(v_next_4578_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v_b_4581_);
return v___x_4588_;
}
else
{
lean_object* v_fst_4589_; lean_object* v_snd_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4637_; 
v_fst_4589_ = lean_ctor_get(v_b_4581_, 0);
v_snd_4590_ = lean_ctor_get(v_b_4581_, 1);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_b_4581_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4592_ = v_b_4581_;
v_isShared_4593_ = v_isSharedCheck_4637_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_snd_4590_);
lean_inc(v_fst_4589_);
lean_dec(v_b_4581_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4637_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___y_4596_; uint8_t v___y_4619_; uint8_t v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4594_ = lean_unsigned_to_nat(1u);
v___x_4629_ = 0;
v___x_4630_ = lean_box(v___x_4629_);
v___x_4631_ = lean_array_get(v___x_4630_, v_fst_4589_, v_next_4578_);
lean_dec(v___x_4630_);
v___x_4632_ = lean_unbox(v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; 
lean_dec(v___x_4631_);
v___x_4633_ = lean_box(v___x_4629_);
v___x_4634_ = lean_array_get(v___x_4633_, v_fst_4589_, v_a_4580_);
lean_dec(v___x_4633_);
v___x_4635_ = lean_unbox(v___x_4634_);
lean_dec(v___x_4634_);
v___y_4619_ = v___x_4635_;
goto v___jp_4618_;
}
else
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_unbox(v___x_4631_);
lean_dec(v___x_4631_);
v___y_4619_ = v___x_4636_;
goto v___jp_4618_;
}
v___jp_4595_:
{
lean_object* v___x_4597_; 
lean_inc(v___y_4585_);
lean_inc_ref(v___y_4584_);
lean_inc(v___y_4583_);
lean_inc_ref(v___y_4582_);
v___x_4597_ = lean_apply_5(v___y_4596_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, lean_box(0));
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4609_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
if (lean_obj_tag(v_a_4598_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4604_; 
lean_dec(v_a_4580_);
lean_dec_ref(v_f_4579_);
lean_dec(v_next_4578_);
v_a_4602_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v_a_4598_, 1);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_a_4602_);
v___x_4604_ = v___x_4600_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4607_; 
lean_del_object(v___x_4600_);
v_a_4606_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v_a_4598_, 1);
v___x_4607_ = lean_nat_add(v_a_4580_, v___x_4594_);
lean_dec(v_a_4580_);
v_a_4580_ = v___x_4607_;
v_b_4581_ = v_a_4606_;
goto _start;
}
}
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec(v_a_4580_);
lean_dec_ref(v_f_4579_);
lean_dec(v_next_4578_);
v_a_4610_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4597_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4597_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
v___jp_4618_:
{
if (v___y_4619_ == 0)
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___f_4623_; 
lean_del_object(v___x_4592_);
v___x_4620_ = lean_array_fget_borrowed(v_a_4577_, v_next_4578_);
v___x_4621_ = lean_array_fget_borrowed(v_a_4577_, v_a_4580_);
v___x_4622_ = lean_box(v___x_4587_);
lean_inc(v_next_4578_);
lean_inc(v_a_4580_);
lean_inc(v___x_4621_);
lean_inc(v___x_4620_);
lean_inc_ref(v_f_4579_);
v___f_4623_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4623_, 0, v_f_4579_);
lean_closure_set(v___f_4623_, 1, v___x_4620_);
lean_closure_set(v___f_4623_, 2, v___x_4621_);
lean_closure_set(v___f_4623_, 3, v___x_4594_);
lean_closure_set(v___f_4623_, 4, v_a_4580_);
lean_closure_set(v___f_4623_, 5, v___x_4622_);
lean_closure_set(v___f_4623_, 6, v_snd_4590_);
lean_closure_set(v___f_4623_, 7, v_fst_4589_);
lean_closure_set(v___f_4623_, 8, v_next_4578_);
v___y_4596_ = v___f_4623_;
goto v___jp_4595_;
}
else
{
lean_object* v___x_4625_; 
if (v_isShared_4593_ == 0)
{
v___x_4625_ = v___x_4592_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_fst_4589_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_snd_4590_);
v___x_4625_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; lean_object* v___f_4627_; 
v___x_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
v___f_4627_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4627_, 0, v___x_4626_);
v___y_4596_ = v___f_4627_;
goto v___jp_4595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4638_, lean_object* v_a_4639_, lean_object* v_next_4640_, lean_object* v_f_4641_, lean_object* v_a_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4638_, v_a_4639_, v_next_4640_, v_f_4641_, v_a_4642_, v_b_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec_ref(v_a_4639_);
lean_dec(v_upperBound_4638_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4650_, lean_object* v___x_4651_, lean_object* v_a_4652_, lean_object* v_f_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_nat_dec_lt(v_a_4654_, v_upperBound_4650_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
lean_dec(v_a_4654_);
lean_dec_ref(v_f_4653_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_b_4655_);
return v___x_4662_;
}
else
{
lean_object* v_fst_4663_; lean_object* v_snd_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4685_; 
v_fst_4663_ = lean_ctor_get(v_b_4655_, 0);
v_snd_4664_ = lean_ctor_get(v_b_4655_, 1);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_b_4655_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4666_ = v_b_4655_;
v_isShared_4667_ = v_isSharedCheck_4685_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_snd_4664_);
lean_inc(v_fst_4663_);
lean_dec(v_b_4655_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4685_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4668_ = lean_unsigned_to_nat(1u);
v___x_4669_ = lean_nat_add(v_a_4654_, v___x_4668_);
if (v_isShared_4667_ == 0)
{
v___x_4671_ = v___x_4666_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_fst_4663_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v_snd_4664_);
v___x_4671_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; 
lean_inc(v___x_4669_);
lean_inc_ref(v_f_4653_);
v___x_4672_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4651_, v_a_4652_, v_a_4654_, v_f_4653_, v___x_4669_, v___x_4671_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v_fst_4674_; lean_object* v_snd_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4683_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v_fst_4674_ = lean_ctor_get(v_a_4673_, 0);
v_snd_4675_ = lean_ctor_get(v_a_4673_, 1);
v_isSharedCheck_4683_ = !lean_is_exclusive(v_a_4673_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4677_ = v_a_4673_;
v_isShared_4678_ = v_isSharedCheck_4683_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_snd_4675_);
lean_inc(v_fst_4674_);
lean_dec(v_a_4673_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4683_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_fst_4674_);
lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_snd_4675_);
v___x_4680_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
v_a_4654_ = v___x_4669_;
v_b_4655_ = v___x_4680_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4669_);
lean_dec_ref(v_f_4653_);
return v___x_4672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4686_, lean_object* v___x_4687_, lean_object* v_a_4688_, lean_object* v_f_4689_, lean_object* v_a_4690_, lean_object* v_b_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4686_, v___x_4687_, v_a_4688_, v_f_4689_, v_a_4690_, v_b_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v_a_4688_);
lean_dec(v___x_4687_);
lean_dec(v_upperBound_4686_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4698_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4712_, lean_object* v_removed_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___y_4723_; uint8_t v___x_4746_; 
v___x_4746_ = lean_nat_dec_lt(v_a_4715_, v_upperBound_4712_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; 
lean_dec(v_a_4715_);
v___x_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4747_, 0, v_b_4716_);
return v___x_4747_;
}
else
{
uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4748_ = 0;
v___x_4749_ = lean_box(v___x_4748_);
v___x_4750_ = lean_array_get(v___x_4749_, v_removed_4713_, v_a_4715_);
lean_dec(v___x_4749_);
v___x_4751_ = lean_unbox(v___x_4750_);
lean_dec(v___x_4750_);
if (v___x_4751_ == 0)
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___f_4755_; 
v___x_4752_ = lean_array_fget_borrowed(v_a_4714_, v_a_4715_);
lean_inc(v___x_4752_);
v___x_4753_ = lean_array_push(v_b_4716_, v___x_4752_);
v___x_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
v___f_4755_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4755_, 0, v___x_4754_);
v___y_4723_ = v___f_4755_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4756_; lean_object* v___f_4757_; 
v___x_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4756_, 0, v_b_4716_);
v___f_4757_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4757_, 0, v___x_4756_);
v___y_4723_ = v___f_4757_;
goto v___jp_4722_;
}
}
v___jp_4722_:
{
lean_object* v___x_4724_; 
lean_inc(v___y_4720_);
lean_inc_ref(v___y_4719_);
lean_inc(v___y_4718_);
lean_inc_ref(v___y_4717_);
v___x_4724_ = lean_apply_5(v___y_4723_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, lean_box(0));
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4737_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4737_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4737_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_a_4725_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; 
lean_dec(v_a_4715_);
v_a_4729_ = lean_ctor_get(v_a_4725_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v_a_4725_, 1);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v_a_4729_);
v___x_4731_ = v___x_4727_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4729_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
lean_del_object(v___x_4727_);
v_a_4733_ = lean_ctor_get(v_a_4725_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v_a_4725_, 1);
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = lean_nat_add(v_a_4715_, v___x_4734_);
lean_dec(v_a_4715_);
v_a_4715_ = v___x_4735_;
v_b_4716_ = v_a_4733_;
goto _start;
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec(v_a_4715_);
v_a_4738_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4724_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4724_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4758_, lean_object* v_removed_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_b_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4758_, v_removed_4759_, v_a_4760_, v_a_4761_, v_b_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec_ref(v_a_4760_);
lean_dec_ref(v_removed_4759_);
lean_dec(v_upperBound_4758_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4769_, lean_object* v_f_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v_removed_4779_; lean_object* v_numRemoved_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4776_ = lean_array_get_size(v_a_4769_);
v___x_4777_ = 0;
v___x_4778_ = lean_box(v___x_4777_);
v_removed_4779_ = lean_mk_array(v___x_4776_, v___x_4778_);
v_numRemoved_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4781_, 0, v_removed_4779_);
lean_ctor_set(v___x_4781_, 1, v_numRemoved_4780_);
v___x_4782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4776_, v___x_4776_, v_a_4769_, v_f_4770_, v_numRemoved_4780_, v___x_4781_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v_fst_4784_; lean_object* v_snd_4785_; lean_object* v_a_x27_4786_; lean_object* v___x_4787_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref_known(v___x_4782_, 1);
v_fst_4784_ = lean_ctor_get(v_a_4783_, 0);
lean_inc(v_fst_4784_);
v_snd_4785_ = lean_ctor_get(v_a_4783_, 1);
lean_inc(v_snd_4785_);
lean_dec(v_a_4783_);
v_a_x27_4786_ = lean_mk_empty_array_with_capacity(v_snd_4785_);
lean_dec(v_snd_4785_);
v___x_4787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4776_, v_fst_4784_, v_a_4769_, v_numRemoved_4780_, v_a_x27_4786_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v_fst_4784_);
return v___x_4787_;
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
v_a_4788_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4782_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4782_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4796_, lean_object* v_f_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4796_, v_f_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec_ref(v_a_4796_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v___f_4811_; lean_object* v___x_4812_; 
v___f_4811_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4812_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4805_, v___f_4811_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec_ref(v_mvars_4813_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4820_, lean_object* v_val_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4820_, v_val_4821_, v___y_4823_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4828_, lean_object* v_val_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4828_, v_val_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4836_, lean_object* v_a_4837_, lean_object* v_f_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4837_, v_f_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_a_4846_, lean_object* v_f_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4845_, v_a_4846_, v_f_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec_ref(v_a_4846_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4854_, lean_object* v_x_4855_, lean_object* v_x_4856_, lean_object* v_x_4857_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4855_, v_x_4856_, v_x_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4859_, lean_object* v_00_u03b1_4860_, lean_object* v_a_4861_, lean_object* v_next_4862_, lean_object* v_f_4863_, lean_object* v_inst_4864_, lean_object* v_R_4865_, lean_object* v_a_4866_, lean_object* v_b_4867_, lean_object* v_c_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v___x_4874_; 
v___x_4874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4859_, v_a_4861_, v_next_4862_, v_f_4863_, v_a_4866_, v_b_4867_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4875_, lean_object* v_00_u03b1_4876_, lean_object* v_a_4877_, lean_object* v_next_4878_, lean_object* v_f_4879_, lean_object* v_inst_4880_, lean_object* v_R_4881_, lean_object* v_a_4882_, lean_object* v_b_4883_, lean_object* v_c_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4875_, v_00_u03b1_4876_, v_a_4877_, v_next_4878_, v_f_4879_, v_inst_4880_, v_R_4881_, v_a_4882_, v_b_4883_, v_c_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec_ref(v_a_4877_);
lean_dec(v_upperBound_4875_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4891_, lean_object* v_upperBound_4892_, lean_object* v_removed_4893_, lean_object* v_a_4894_, lean_object* v_inst_4895_, lean_object* v_R_4896_, lean_object* v_a_4897_, lean_object* v_b_4898_, lean_object* v_c_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4892_, v_removed_4893_, v_a_4894_, v_a_4897_, v_b_4898_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4906_, lean_object* v_upperBound_4907_, lean_object* v_removed_4908_, lean_object* v_a_4909_, lean_object* v_inst_4910_, lean_object* v_R_4911_, lean_object* v_a_4912_, lean_object* v_b_4913_, lean_object* v_c_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4906_, v_upperBound_4907_, v_removed_4908_, v_a_4909_, v_inst_4910_, v_R_4911_, v_a_4912_, v_b_4913_, v_c_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
lean_dec_ref(v_a_4909_);
lean_dec_ref(v_removed_4908_);
lean_dec(v_upperBound_4907_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4921_, lean_object* v___x_4922_, lean_object* v_00_u03b1_4923_, lean_object* v_a_4924_, lean_object* v_f_4925_, lean_object* v_inst_4926_, lean_object* v_R_4927_, lean_object* v_a_4928_, lean_object* v_b_4929_, lean_object* v_c_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4921_, v___x_4922_, v_a_4924_, v_f_4925_, v_a_4928_, v_b_4929_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4937_, lean_object* v___x_4938_, lean_object* v_00_u03b1_4939_, lean_object* v_a_4940_, lean_object* v_f_4941_, lean_object* v_inst_4942_, lean_object* v_R_4943_, lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v_c_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4937_, v___x_4938_, v_00_u03b1_4939_, v_a_4940_, v_f_4941_, v_inst_4942_, v_R_4943_, v_a_4944_, v_b_4945_, v_c_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec_ref(v_a_4940_);
lean_dec(v___x_4938_);
lean_dec(v_upperBound_4937_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4953_, lean_object* v_x_4954_, size_t v_x_4955_, size_t v_x_4956_, lean_object* v_x_4957_, lean_object* v_x_4958_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4954_, v_x_4955_, v_x_4956_, v_x_4957_, v_x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4960_, lean_object* v_x_4961_, lean_object* v_x_4962_, lean_object* v_x_4963_, lean_object* v_x_4964_, lean_object* v_x_4965_){
_start:
{
size_t v_x_5196__boxed_4966_; size_t v_x_5197__boxed_4967_; lean_object* v_res_4968_; 
v_x_5196__boxed_4966_ = lean_unbox_usize(v_x_4962_);
lean_dec(v_x_4962_);
v_x_5197__boxed_4967_ = lean_unbox_usize(v_x_4963_);
lean_dec(v_x_4963_);
v_res_4968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4960_, v_x_4961_, v_x_5196__boxed_4966_, v_x_5197__boxed_4967_, v_x_4964_, v_x_4965_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4969_, lean_object* v_n_4970_, lean_object* v_k_4971_, lean_object* v_v_4972_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4970_, v_k_4971_, v_v_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4974_, size_t v_depth_4975_, lean_object* v_keys_4976_, lean_object* v_vals_4977_, lean_object* v_heq_4978_, lean_object* v_i_4979_, lean_object* v_entries_4980_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4975_, v_keys_4976_, v_vals_4977_, v_i_4979_, v_entries_4980_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4982_, lean_object* v_depth_4983_, lean_object* v_keys_4984_, lean_object* v_vals_4985_, lean_object* v_heq_4986_, lean_object* v_i_4987_, lean_object* v_entries_4988_){
_start:
{
size_t v_depth_boxed_4989_; lean_object* v_res_4990_; 
v_depth_boxed_4989_ = lean_unbox_usize(v_depth_4983_);
lean_dec(v_depth_4983_);
v_res_4990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4982_, v_depth_boxed_4989_, v_keys_4984_, v_vals_4985_, v_heq_4986_, v_i_4987_, v_entries_4988_);
lean_dec_ref(v_vals_4985_);
lean_dec_ref(v_keys_4984_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4991_, lean_object* v_x_4992_, lean_object* v_x_4993_, lean_object* v_x_4994_, lean_object* v_x_4995_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4992_, v_x_4993_, v_x_4994_, v_x_4995_);
return v___x_4996_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4999_ = l_Lean_stringToMessageData(v___x_4998_);
return v___x_4999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5003_, lean_object* v_as_5004_, size_t v_sz_5005_, size_t v_i_5006_, lean_object* v_b_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v_a_5014_; uint8_t v___x_5018_; 
v___x_5018_ = lean_usize_dec_lt(v_i_5006_, v_sz_5005_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v_b_5007_);
return v___x_5019_;
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5021_; 
v_a_5020_ = lean_array_uget_borrowed(v_as_5004_, v_i_5006_);
lean_inc(v_a_5020_);
v___x_5021_ = l_Lean_MVarId_getType(v_a_5020_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; lean_object* v___y_5027_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref_known(v___x_5021_, 1);
if (lean_obj_tag(v_a_5022_) == 10)
{
lean_object* v_expr_5040_; 
v_expr_5040_ = lean_ctor_get(v_a_5022_, 1);
if (lean_obj_tag(v_expr_5040_) == 5)
{
lean_object* v_arg_5041_; lean_object* v___x_5042_; 
lean_inc_ref(v_expr_5040_);
lean_dec_ref_known(v_a_5022_, 2);
v_arg_5041_ = lean_ctor_get(v_expr_5040_, 1);
lean_inc_ref_n(v_arg_5041_, 2);
lean_dec_ref_known(v_expr_5040_, 2);
v___x_5042_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5003_, v_arg_5041_);
if (lean_obj_tag(v___x_5042_) == 1)
{
lean_object* v_val_5043_; lean_object* v_fst_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
lean_dec_ref(v_arg_5041_);
v_val_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_val_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v_fst_5044_ = lean_ctor_get(v_val_5043_, 0);
lean_inc(v_fst_5044_);
lean_dec(v_val_5043_);
v___x_5045_ = lean_array_get_size(v_b_5007_);
v___x_5046_ = lean_nat_dec_lt(v_fst_5044_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_dec(v_fst_5044_);
v_a_5014_ = v_b_5007_;
goto v___jp_5013_;
}
else
{
lean_object* v_v_5047_; lean_object* v___x_5048_; lean_object* v_xs_x27_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v_v_5047_ = lean_array_fget(v_b_5007_, v_fst_5044_);
v___x_5048_ = lean_box(0);
v_xs_x27_5049_ = lean_array_fset(v_b_5007_, v_fst_5044_, v___x_5048_);
lean_inc(v_a_5020_);
v___x_5050_ = lean_array_push(v_v_5047_, v_a_5020_);
v___x_5051_ = lean_array_fset(v_xs_x27_5049_, v_fst_5044_, v___x_5050_);
lean_dec(v_fst_5044_);
v_a_5014_ = v___x_5051_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_dec(v___x_5042_);
v___x_5052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5053_ = l_Lean_indentExpr(v_arg_5041_);
v___x_5054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
v___x_5055_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5054_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_dec_ref_known(v___x_5055_, 1);
v_a_5014_ = v_b_5007_;
goto v___jp_5013_;
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec_ref(v_b_5007_);
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5055_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5055_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
else
{
v___y_5024_ = v___y_5008_;
v___y_5025_ = v___y_5009_;
v___y_5026_ = v___y_5010_;
v___y_5027_ = v___y_5011_;
goto v___jp_5023_;
}
}
else
{
v___y_5024_ = v___y_5008_;
v___y_5025_ = v___y_5009_;
v___y_5026_ = v___y_5010_;
v___y_5027_ = v___y_5011_;
goto v___jp_5023_;
}
v___jp_5023_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5029_ = l_Lean_indentExpr(v_a_5022_);
v___x_5030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5028_);
lean_ctor_set(v___x_5030_, 1, v___x_5029_);
v___x_5031_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5030_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_dec_ref_known(v___x_5031_, 1);
v_a_5014_ = v_b_5007_;
goto v___jp_5013_;
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec_ref(v_b_5007_);
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
lean_dec_ref(v_b_5007_);
v_a_5064_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5021_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5021_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
v___jp_5013_:
{
size_t v___x_5015_; size_t v___x_5016_; 
v___x_5015_ = ((size_t)1ULL);
v___x_5016_ = lean_usize_add(v_i_5006_, v___x_5015_);
v_i_5006_ = v___x_5016_;
v_b_5007_ = v_a_5014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5072_, lean_object* v_as_5073_, lean_object* v_sz_5074_, lean_object* v_i_5075_, lean_object* v_b_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
size_t v_sz_boxed_5082_; size_t v_i_boxed_5083_; lean_object* v_res_5084_; 
v_sz_boxed_5082_ = lean_unbox_usize(v_sz_5074_);
lean_dec(v_sz_5074_);
v_i_boxed_5083_ = lean_unbox_usize(v_i_5075_);
lean_dec(v_i_5075_);
v_res_5084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5072_, v_as_5073_, v_sz_boxed_5082_, v_i_boxed_5083_, v_b_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec_ref(v_as_5073_);
lean_dec_ref(v_argsPacker_5072_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5085_, lean_object* v_numFuncs_5086_, lean_object* v_goals_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_){
_start:
{
lean_object* v___x_5093_; lean_object* v_r_5094_; size_t v_sz_5095_; size_t v___x_5096_; lean_object* v___x_5097_; 
v___x_5093_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5094_ = lean_mk_array(v_numFuncs_5086_, v___x_5093_);
v_sz_5095_ = lean_array_size(v_goals_5087_);
v___x_5096_ = ((size_t)0ULL);
v___x_5097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5085_, v_goals_5087_, v_sz_5095_, v___x_5096_, v_r_5094_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5098_, lean_object* v_numFuncs_5099_, lean_object* v_goals_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5098_, v_numFuncs_5099_, v_goals_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
lean_dec(v_a_5104_);
lean_dec_ref(v_a_5103_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec_ref(v_goals_5100_);
lean_dec_ref(v_argsPacker_5098_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v___x_5110_; lean_object* v_infoState_5111_; uint8_t v_enabled_5112_; 
v___x_5110_ = lean_st_ref_get(v___y_5108_);
v_infoState_5111_ = lean_ctor_get(v___x_5110_, 7);
lean_inc_ref(v_infoState_5111_);
lean_dec(v___x_5110_);
v_enabled_5112_ = lean_ctor_get_uint8(v_infoState_5111_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5111_);
if (v_enabled_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
lean_dec_ref(v_t_5107_);
v___x_5113_ = lean_box(0);
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; lean_object* v_infoState_5116_; lean_object* v_env_5117_; lean_object* v_nextMacroScope_5118_; lean_object* v_ngen_5119_; lean_object* v_auxDeclNGen_5120_; lean_object* v_traceState_5121_; lean_object* v_cache_5122_; lean_object* v_messages_5123_; lean_object* v_snapshotTasks_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5146_; 
v___x_5115_ = lean_st_ref_take(v___y_5108_);
v_infoState_5116_ = lean_ctor_get(v___x_5115_, 7);
v_env_5117_ = lean_ctor_get(v___x_5115_, 0);
v_nextMacroScope_5118_ = lean_ctor_get(v___x_5115_, 1);
v_ngen_5119_ = lean_ctor_get(v___x_5115_, 2);
v_auxDeclNGen_5120_ = lean_ctor_get(v___x_5115_, 3);
v_traceState_5121_ = lean_ctor_get(v___x_5115_, 4);
v_cache_5122_ = lean_ctor_get(v___x_5115_, 5);
v_messages_5123_ = lean_ctor_get(v___x_5115_, 6);
v_snapshotTasks_5124_ = lean_ctor_get(v___x_5115_, 8);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5126_ = v___x_5115_;
v_isShared_5127_ = v_isSharedCheck_5146_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_snapshotTasks_5124_);
lean_inc(v_infoState_5116_);
lean_inc(v_messages_5123_);
lean_inc(v_cache_5122_);
lean_inc(v_traceState_5121_);
lean_inc(v_auxDeclNGen_5120_);
lean_inc(v_ngen_5119_);
lean_inc(v_nextMacroScope_5118_);
lean_inc(v_env_5117_);
lean_dec(v___x_5115_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5146_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
uint8_t v_enabled_5128_; lean_object* v_assignment_5129_; lean_object* v_lazyAssignment_5130_; lean_object* v_trees_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5145_; 
v_enabled_5128_ = lean_ctor_get_uint8(v_infoState_5116_, sizeof(void*)*3);
v_assignment_5129_ = lean_ctor_get(v_infoState_5116_, 0);
v_lazyAssignment_5130_ = lean_ctor_get(v_infoState_5116_, 1);
v_trees_5131_ = lean_ctor_get(v_infoState_5116_, 2);
v_isSharedCheck_5145_ = !lean_is_exclusive(v_infoState_5116_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5133_ = v_infoState_5116_;
v_isShared_5134_ = v_isSharedCheck_5145_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_trees_5131_);
lean_inc(v_lazyAssignment_5130_);
lean_inc(v_assignment_5129_);
lean_dec(v_infoState_5116_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5145_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; lean_object* v___x_5137_; 
v___x_5135_ = l_Lean_PersistentArray_push___redArg(v_trees_5131_, v_t_5107_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 2, v___x_5135_);
v___x_5137_ = v___x_5133_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_assignment_5129_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_lazyAssignment_5130_);
lean_ctor_set(v_reuseFailAlloc_5144_, 2, v___x_5135_);
lean_ctor_set_uint8(v_reuseFailAlloc_5144_, sizeof(void*)*3, v_enabled_5128_);
v___x_5137_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5139_; 
if (v_isShared_5127_ == 0)
{
lean_ctor_set(v___x_5126_, 7, v___x_5137_);
v___x_5139_ = v___x_5126_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_env_5117_);
lean_ctor_set(v_reuseFailAlloc_5143_, 1, v_nextMacroScope_5118_);
lean_ctor_set(v_reuseFailAlloc_5143_, 2, v_ngen_5119_);
lean_ctor_set(v_reuseFailAlloc_5143_, 3, v_auxDeclNGen_5120_);
lean_ctor_set(v_reuseFailAlloc_5143_, 4, v_traceState_5121_);
lean_ctor_set(v_reuseFailAlloc_5143_, 5, v_cache_5122_);
lean_ctor_set(v_reuseFailAlloc_5143_, 6, v_messages_5123_);
lean_ctor_set(v_reuseFailAlloc_5143_, 7, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5143_, 8, v_snapshotTasks_5124_);
v___x_5139_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5140_ = lean_st_ref_set(v___y_5108_, v___x_5139_);
v___x_5141_ = lean_box(0);
v___x_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
return v___x_5142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5147_, v___y_5148_);
lean_dec(v___y_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5151_, v___y_5157_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5169_, lean_object* v___y_5170_){
_start:
{
uint8_t v___x_5172_; uint8_t v___x_5173_; 
v___x_5172_ = l_Lean_Expr_hasMVar(v_e_5169_);
v___x_5173_ = lean_bool_not(v___x_5172_);
if (v___x_5173_ == 0)
{
lean_object* v___x_5174_; lean_object* v_mctx_5175_; lean_object* v___x_5176_; lean_object* v_fst_5177_; lean_object* v_snd_5178_; lean_object* v___x_5179_; lean_object* v_cache_5180_; lean_object* v_zetaDeltaFVarIds_5181_; lean_object* v_postponed_5182_; lean_object* v_diag_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5192_; 
v___x_5174_ = lean_st_ref_get(v___y_5170_);
v_mctx_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc_ref(v_mctx_5175_);
lean_dec(v___x_5174_);
v___x_5176_ = l_Lean_instantiateMVarsCore(v_mctx_5175_, v_e_5169_);
v_fst_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_fst_5177_);
v_snd_5178_ = lean_ctor_get(v___x_5176_, 1);
lean_inc(v_snd_5178_);
lean_dec_ref(v___x_5176_);
v___x_5179_ = lean_st_ref_take(v___y_5170_);
v_cache_5180_ = lean_ctor_get(v___x_5179_, 1);
v_zetaDeltaFVarIds_5181_ = lean_ctor_get(v___x_5179_, 2);
v_postponed_5182_ = lean_ctor_get(v___x_5179_, 3);
v_diag_5183_ = lean_ctor_get(v___x_5179_, 4);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5192_ == 0)
{
lean_object* v_unused_5193_; 
v_unused_5193_ = lean_ctor_get(v___x_5179_, 0);
lean_dec(v_unused_5193_);
v___x_5185_ = v___x_5179_;
v_isShared_5186_ = v_isSharedCheck_5192_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_diag_5183_);
lean_inc(v_postponed_5182_);
lean_inc(v_zetaDeltaFVarIds_5181_);
lean_inc(v_cache_5180_);
lean_dec(v___x_5179_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5192_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v_snd_5178_);
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_snd_5178_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_cache_5180_);
lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_zetaDeltaFVarIds_5181_);
lean_ctor_set(v_reuseFailAlloc_5191_, 3, v_postponed_5182_);
lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_diag_5183_);
v___x_5188_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5189_ = lean_st_ref_set(v___y_5170_, v___x_5188_);
v___x_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5190_, 0, v_fst_5177_);
return v___x_5190_;
}
}
}
else
{
lean_object* v___x_5194_; 
v___x_5194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5194_, 0, v_e_5169_);
return v___x_5194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5195_, v___y_5196_);
lean_dec(v___y_5196_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v___x_5205_; 
v___x_5205_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5199_, v___y_5201_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5213_, size_t v_i_5214_, size_t v_stop_5215_, lean_object* v_b_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
uint8_t v___x_5224_; 
v___x_5224_ = lean_usize_dec_eq(v_i_5214_, v_stop_5215_);
if (v___x_5224_ == 0)
{
lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v___x_5225_ = lean_array_uget_borrowed(v_as_5213_, v_i_5214_);
lean_inc(v___x_5225_);
v___x_5226_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5225_);
v___x_5227_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5226_, v___y_5222_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; size_t v___x_5229_; size_t v___x_5230_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
v___x_5229_ = ((size_t)1ULL);
v___x_5230_ = lean_usize_add(v_i_5214_, v___x_5229_);
v_i_5214_ = v___x_5230_;
v_b_5216_ = v_a_5228_;
goto _start;
}
else
{
return v___x_5227_;
}
}
else
{
lean_object* v___x_5232_; 
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v_b_5216_);
return v___x_5232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5233_, lean_object* v_i_5234_, lean_object* v_stop_5235_, lean_object* v_b_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
size_t v_i_boxed_5244_; size_t v_stop_boxed_5245_; lean_object* v_res_5246_; 
v_i_boxed_5244_ = lean_unbox_usize(v_i_5234_);
lean_dec(v_i_5234_);
v_stop_boxed_5245_ = lean_unbox_usize(v_stop_5235_);
lean_dec(v_stop_5235_);
v_res_5246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5233_, v_i_boxed_5244_, v_stop_boxed_5245_, v_b_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec_ref(v_as_5233_);
return v_res_5246_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5247_ = lean_unsigned_to_nat(32u);
v___x_5248_ = lean_mk_empty_array_with_capacity(v___x_5247_);
v___x_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
return v___x_5249_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5250_ = ((size_t)5ULL);
v___x_5251_ = lean_unsigned_to_nat(0u);
v___x_5252_ = lean_unsigned_to_nat(32u);
v___x_5253_ = lean_mk_empty_array_with_capacity(v___x_5252_);
v___x_5254_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5255_, 0, v___x_5254_);
lean_ctor_set(v___x_5255_, 1, v___x_5253_);
lean_ctor_set(v___x_5255_, 2, v___x_5251_);
lean_ctor_set(v___x_5255_, 3, v___x_5251_);
lean_ctor_set_usize(v___x_5255_, 4, v___x_5250_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5256_){
_start:
{
lean_object* v___x_5258_; lean_object* v_infoState_5259_; lean_object* v_trees_5260_; lean_object* v___x_5261_; lean_object* v_infoState_5262_; lean_object* v_env_5263_; lean_object* v_nextMacroScope_5264_; lean_object* v_ngen_5265_; lean_object* v_auxDeclNGen_5266_; lean_object* v_traceState_5267_; lean_object* v_cache_5268_; lean_object* v_messages_5269_; lean_object* v_snapshotTasks_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5291_; 
v___x_5258_ = lean_st_ref_get(v___y_5256_);
v_infoState_5259_ = lean_ctor_get(v___x_5258_, 7);
lean_inc_ref(v_infoState_5259_);
lean_dec(v___x_5258_);
v_trees_5260_ = lean_ctor_get(v_infoState_5259_, 2);
lean_inc_ref(v_trees_5260_);
lean_dec_ref(v_infoState_5259_);
v___x_5261_ = lean_st_ref_take(v___y_5256_);
v_infoState_5262_ = lean_ctor_get(v___x_5261_, 7);
v_env_5263_ = lean_ctor_get(v___x_5261_, 0);
v_nextMacroScope_5264_ = lean_ctor_get(v___x_5261_, 1);
v_ngen_5265_ = lean_ctor_get(v___x_5261_, 2);
v_auxDeclNGen_5266_ = lean_ctor_get(v___x_5261_, 3);
v_traceState_5267_ = lean_ctor_get(v___x_5261_, 4);
v_cache_5268_ = lean_ctor_get(v___x_5261_, 5);
v_messages_5269_ = lean_ctor_get(v___x_5261_, 6);
v_snapshotTasks_5270_ = lean_ctor_get(v___x_5261_, 8);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5272_ = v___x_5261_;
v_isShared_5273_ = v_isSharedCheck_5291_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_snapshotTasks_5270_);
lean_inc(v_infoState_5262_);
lean_inc(v_messages_5269_);
lean_inc(v_cache_5268_);
lean_inc(v_traceState_5267_);
lean_inc(v_auxDeclNGen_5266_);
lean_inc(v_ngen_5265_);
lean_inc(v_nextMacroScope_5264_);
lean_inc(v_env_5263_);
lean_dec(v___x_5261_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5291_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
uint8_t v_enabled_5274_; lean_object* v_assignment_5275_; lean_object* v_lazyAssignment_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5289_; 
v_enabled_5274_ = lean_ctor_get_uint8(v_infoState_5262_, sizeof(void*)*3);
v_assignment_5275_ = lean_ctor_get(v_infoState_5262_, 0);
v_lazyAssignment_5276_ = lean_ctor_get(v_infoState_5262_, 1);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_infoState_5262_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; 
v_unused_5290_ = lean_ctor_get(v_infoState_5262_, 2);
lean_dec(v_unused_5290_);
v___x_5278_ = v_infoState_5262_;
v_isShared_5279_ = v_isSharedCheck_5289_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_lazyAssignment_5276_);
lean_inc(v_assignment_5275_);
lean_dec(v_infoState_5262_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5289_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; lean_object* v___x_5282_; 
v___x_5280_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 2, v___x_5280_);
v___x_5282_ = v___x_5278_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_assignment_5275_);
lean_ctor_set(v_reuseFailAlloc_5288_, 1, v_lazyAssignment_5276_);
lean_ctor_set(v_reuseFailAlloc_5288_, 2, v___x_5280_);
lean_ctor_set_uint8(v_reuseFailAlloc_5288_, sizeof(void*)*3, v_enabled_5274_);
v___x_5282_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
lean_object* v___x_5284_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 7, v___x_5282_);
v___x_5284_ = v___x_5272_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_env_5263_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_nextMacroScope_5264_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v_ngen_5265_);
lean_ctor_set(v_reuseFailAlloc_5287_, 3, v_auxDeclNGen_5266_);
lean_ctor_set(v_reuseFailAlloc_5287_, 4, v_traceState_5267_);
lean_ctor_set(v_reuseFailAlloc_5287_, 5, v_cache_5268_);
lean_ctor_set(v_reuseFailAlloc_5287_, 6, v_messages_5269_);
lean_ctor_set(v_reuseFailAlloc_5287_, 7, v___x_5282_);
lean_ctor_set(v_reuseFailAlloc_5287_, 8, v_snapshotTasks_5270_);
v___x_5284_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5285_ = lean_st_ref_set(v___y_5256_, v___x_5284_);
v___x_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5286_, 0, v_trees_5260_);
return v___x_5286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5292_);
lean_dec(v___y_5292_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5295_, lean_object* v_mkInfoTree_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v_a_5304_, lean_object* v_a_x3f_5305_){
_start:
{
lean_object* v___x_5307_; lean_object* v_infoState_5308_; lean_object* v_trees_5309_; lean_object* v___x_5310_; 
v___x_5307_ = lean_st_ref_get(v___y_5295_);
v_infoState_5308_ = lean_ctor_get(v___x_5307_, 7);
lean_inc_ref(v_infoState_5308_);
lean_dec(v___x_5307_);
v_trees_5309_ = lean_ctor_get(v_infoState_5308_, 2);
lean_inc_ref(v_trees_5309_);
lean_dec_ref(v_infoState_5308_);
lean_inc(v___y_5295_);
lean_inc_ref(v___y_5303_);
lean_inc(v___y_5302_);
lean_inc_ref(v___y_5301_);
lean_inc(v___y_5300_);
lean_inc_ref(v___y_5299_);
lean_inc(v___y_5298_);
lean_inc_ref(v___y_5297_);
v___x_5310_ = lean_apply_10(v_mkInfoTree_5296_, v_trees_5309_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5295_, lean_box(0));
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5349_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5349_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5349_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5315_; lean_object* v_infoState_5316_; lean_object* v_env_5317_; lean_object* v_nextMacroScope_5318_; lean_object* v_ngen_5319_; lean_object* v_auxDeclNGen_5320_; lean_object* v_traceState_5321_; lean_object* v_cache_5322_; lean_object* v_messages_5323_; lean_object* v_snapshotTasks_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5348_; 
v___x_5315_ = lean_st_ref_take(v___y_5295_);
v_infoState_5316_ = lean_ctor_get(v___x_5315_, 7);
v_env_5317_ = lean_ctor_get(v___x_5315_, 0);
v_nextMacroScope_5318_ = lean_ctor_get(v___x_5315_, 1);
v_ngen_5319_ = lean_ctor_get(v___x_5315_, 2);
v_auxDeclNGen_5320_ = lean_ctor_get(v___x_5315_, 3);
v_traceState_5321_ = lean_ctor_get(v___x_5315_, 4);
v_cache_5322_ = lean_ctor_get(v___x_5315_, 5);
v_messages_5323_ = lean_ctor_get(v___x_5315_, 6);
v_snapshotTasks_5324_ = lean_ctor_get(v___x_5315_, 8);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5326_ = v___x_5315_;
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_snapshotTasks_5324_);
lean_inc(v_infoState_5316_);
lean_inc(v_messages_5323_);
lean_inc(v_cache_5322_);
lean_inc(v_traceState_5321_);
lean_inc(v_auxDeclNGen_5320_);
lean_inc(v_ngen_5319_);
lean_inc(v_nextMacroScope_5318_);
lean_inc(v_env_5317_);
lean_dec(v___x_5315_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
uint8_t v_enabled_5328_; lean_object* v_assignment_5329_; lean_object* v_lazyAssignment_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5346_; 
v_enabled_5328_ = lean_ctor_get_uint8(v_infoState_5316_, sizeof(void*)*3);
v_assignment_5329_ = lean_ctor_get(v_infoState_5316_, 0);
v_lazyAssignment_5330_ = lean_ctor_get(v_infoState_5316_, 1);
v_isSharedCheck_5346_ = !lean_is_exclusive(v_infoState_5316_);
if (v_isSharedCheck_5346_ == 0)
{
lean_object* v_unused_5347_; 
v_unused_5347_ = lean_ctor_get(v_infoState_5316_, 2);
lean_dec(v_unused_5347_);
v___x_5332_ = v_infoState_5316_;
v_isShared_5333_ = v_isSharedCheck_5346_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_lazyAssignment_5330_);
lean_inc(v_assignment_5329_);
lean_dec(v_infoState_5316_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5346_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5334_; lean_object* v___x_5336_; 
v___x_5334_ = l_Lean_PersistentArray_push___redArg(v_a_5304_, v_a_5311_);
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 2, v___x_5334_);
v___x_5336_ = v___x_5332_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_assignment_5329_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_lazyAssignment_5330_);
lean_ctor_set(v_reuseFailAlloc_5345_, 2, v___x_5334_);
lean_ctor_set_uint8(v_reuseFailAlloc_5345_, sizeof(void*)*3, v_enabled_5328_);
v___x_5336_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
lean_object* v___x_5338_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 7, v___x_5336_);
v___x_5338_ = v___x_5326_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_env_5317_);
lean_ctor_set(v_reuseFailAlloc_5344_, 1, v_nextMacroScope_5318_);
lean_ctor_set(v_reuseFailAlloc_5344_, 2, v_ngen_5319_);
lean_ctor_set(v_reuseFailAlloc_5344_, 3, v_auxDeclNGen_5320_);
lean_ctor_set(v_reuseFailAlloc_5344_, 4, v_traceState_5321_);
lean_ctor_set(v_reuseFailAlloc_5344_, 5, v_cache_5322_);
lean_ctor_set(v_reuseFailAlloc_5344_, 6, v_messages_5323_);
lean_ctor_set(v_reuseFailAlloc_5344_, 7, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5344_, 8, v_snapshotTasks_5324_);
v___x_5338_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5342_; 
v___x_5339_ = lean_st_ref_set(v___y_5295_, v___x_5338_);
v___x_5340_ = lean_box(0);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5340_);
v___x_5342_ = v___x_5313_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v___x_5340_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec_ref(v_a_5304_);
v_a_5350_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5310_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5310_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5358_, lean_object* v_mkInfoTree_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v_a_5367_, lean_object* v_a_x3f_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5358_, v_mkInfoTree_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v_a_5367_, v_a_x3f_5368_);
lean_dec(v_a_x3f_5368_);
lean_dec_ref(v___y_5366_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5358_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5371_, lean_object* v_mkInfoTree_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v___x_5382_; lean_object* v_infoState_5383_; uint8_t v_enabled_5384_; 
v___x_5382_ = lean_st_ref_get(v___y_5380_);
v_infoState_5383_ = lean_ctor_get(v___x_5382_, 7);
lean_inc_ref(v_infoState_5383_);
lean_dec(v___x_5382_);
v_enabled_5384_ = lean_ctor_get_uint8(v_infoState_5383_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5383_);
if (v_enabled_5384_ == 0)
{
lean_object* v___x_5385_; 
lean_dec_ref(v_mkInfoTree_5372_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
lean_inc(v___y_5378_);
lean_inc_ref(v___y_5377_);
lean_inc(v___y_5376_);
lean_inc_ref(v___y_5375_);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
v___x_5385_ = lean_apply_9(v_x_5371_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, lean_box(0));
return v___x_5385_;
}
else
{
lean_object* v___x_5386_; lean_object* v_a_5387_; lean_object* v_r_5388_; 
v___x_5386_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5380_);
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref(v___x_5386_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
lean_inc(v___y_5378_);
lean_inc_ref(v___y_5377_);
lean_inc(v___y_5376_);
lean_inc_ref(v___y_5375_);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
v_r_5388_ = lean_apply_9(v_x_5371_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, lean_box(0));
if (lean_obj_tag(v_r_5388_) == 0)
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5413_; 
v_a_5389_ = lean_ctor_get(v_r_5388_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v_r_5388_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5391_ = v_r_5388_;
v_isShared_5392_ = v_isSharedCheck_5413_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v_r_5388_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5413_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
lean_inc(v_a_5389_);
if (v_isShared_5392_ == 0)
{
lean_ctor_set_tag(v___x_5391_, 1);
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5380_, v_mkInfoTree_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v_a_5387_, v___x_5394_);
lean_dec_ref(v___x_5394_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5402_ == 0)
{
lean_object* v_unused_5403_; 
v_unused_5403_ = lean_ctor_get(v___x_5395_, 0);
lean_dec(v_unused_5403_);
v___x_5397_ = v___x_5395_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_dec(v___x_5395_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 0, v_a_5389_);
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5389_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v_a_5389_);
v_a_5404_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5395_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5395_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
}
else
{
lean_object* v_a_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v_a_5414_ = lean_ctor_get(v_r_5388_, 0);
lean_inc(v_a_5414_);
lean_dec_ref_known(v_r_5388_, 1);
v___x_5415_ = lean_box(0);
v___x_5416_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5380_, v_mkInfoTree_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v_a_5387_, v___x_5415_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5423_ == 0)
{
lean_object* v_unused_5424_; 
v_unused_5424_ = lean_ctor_get(v___x_5416_, 0);
lean_dec(v_unused_5424_);
v___x_5418_ = v___x_5416_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_dec(v___x_5416_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set_tag(v___x_5418_, 1);
lean_ctor_set(v___x_5418_, 0, v_a_5414_);
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5414_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec(v_a_5414_);
v_a_5425_ = lean_ctor_get(v___x_5416_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5416_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5416_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5433_, lean_object* v_mkInfoTree_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5433_, v_mkInfoTree_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5445_, lean_object* v_trees_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v___x_5456_; 
lean_inc(v___y_5454_);
lean_inc_ref(v___y_5453_);
lean_inc(v___y_5452_);
lean_inc_ref(v___y_5451_);
lean_inc(v___y_5450_);
lean_inc_ref(v___y_5449_);
lean_inc(v___y_5448_);
lean_inc_ref(v___y_5447_);
v___x_5456_ = lean_apply_9(v_a_5445_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, lean_box(0));
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5465_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5459_ = v___x_5456_;
v_isShared_5460_ = v_isSharedCheck_5465_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5456_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5465_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5461_; lean_object* v___x_5463_; 
v___x_5461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5461_, 0, v_a_5457_);
lean_ctor_set(v___x_5461_, 1, v_trees_5446_);
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 0, v___x_5461_);
v___x_5463_ = v___x_5459_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5461_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
else
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_dec_ref(v_trees_5446_);
v_a_5466_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5456_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5456_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5474_, lean_object* v_trees_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5474_, v_trees_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5486_, lean_object* v_ref_5487_, lean_object* v_tactic_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
lean_object* v___x_5498_; 
v___x_5498_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5486_, v___y_5490_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v___x_5499_; 
lean_dec_ref_known(v___x_5498_, 1);
v___x_5499_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5499_) == 0)
{
lean_object* v___x_5500_; 
lean_dec_ref_known(v___x_5499_, 1);
v___x_5500_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5487_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___f_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref_known(v___x_5500_, 1);
v___f_5502_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5502_, 0, v_a_5501_);
v___x_5503_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5503_, 0, v_tactic_5488_);
v___x_5504_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5503_, v___f_5502_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
return v___x_5504_;
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec(v_tactic_5488_);
v_a_5505_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5500_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5500_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_dec(v_tactic_5488_);
lean_dec(v_ref_5487_);
return v___x_5499_;
}
}
else
{
lean_dec(v_tactic_5488_);
lean_dec(v_ref_5487_);
return v___x_5498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5513_, lean_object* v_ref_5514_, lean_object* v_tactic_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v_res_5525_; 
v_res_5525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5513_, v_ref_5514_, v_tactic_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v_res_5525_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5526_ = lean_box(1);
v___x_5527_ = l_Lean_MessageData_ofFormat(v___x_5526_);
return v___x_5527_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5531_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5532_ = l_Lean_MessageData_ofFormat(v___x_5531_);
return v___x_5532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5533_, lean_object* v_x_5534_){
_start:
{
if (lean_obj_tag(v_x_5534_) == 0)
{
return v_x_5533_;
}
else
{
lean_object* v_head_5535_; lean_object* v_tail_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5558_; 
v_head_5535_ = lean_ctor_get(v_x_5534_, 0);
v_tail_5536_ = lean_ctor_get(v_x_5534_, 1);
v_isSharedCheck_5558_ = !lean_is_exclusive(v_x_5534_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5538_ = v_x_5534_;
v_isShared_5539_ = v_isSharedCheck_5558_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_tail_5536_);
lean_inc(v_head_5535_);
lean_dec(v_x_5534_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5558_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v_before_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5556_; 
v_before_5540_ = lean_ctor_get(v_head_5535_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v_head_5535_);
if (v_isSharedCheck_5556_ == 0)
{
lean_object* v_unused_5557_; 
v_unused_5557_ = lean_ctor_get(v_head_5535_, 1);
lean_dec(v_unused_5557_);
v___x_5542_ = v_head_5535_;
v_isShared_5543_ = v_isSharedCheck_5556_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_before_5540_);
lean_dec(v_head_5535_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5556_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5544_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5543_ == 0)
{
lean_ctor_set_tag(v___x_5542_, 7);
lean_ctor_set(v___x_5542_, 1, v___x_5544_);
lean_ctor_set(v___x_5542_, 0, v_x_5533_);
v___x_5546_ = v___x_5542_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_x_5533_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v___x_5544_);
v___x_5546_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5547_; lean_object* v___x_5549_; 
v___x_5547_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 7);
lean_ctor_set(v___x_5538_, 1, v___x_5547_);
lean_ctor_set(v___x_5538_, 0, v___x_5546_);
v___x_5549_ = v___x_5538_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v___x_5547_);
v___x_5549_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5550_ = l_Lean_MessageData_ofSyntax(v_before_5540_);
v___x_5551_ = l_Lean_indentD(v___x_5550_);
v___x_5552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5552_, 0, v___x_5549_);
lean_ctor_set(v___x_5552_, 1, v___x_5551_);
v_x_5533_ = v___x_5552_;
v_x_5534_ = v_tail_5536_;
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
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5563_ = l_Lean_MessageData_ofFormat(v___x_5562_);
return v___x_5563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5564_, lean_object* v_macroStack_5565_, lean_object* v___y_5566_){
_start:
{
lean_object* v_options_5568_; lean_object* v___x_5569_; uint8_t v___x_5570_; uint8_t v___x_5571_; 
v_options_5568_ = lean_ctor_get(v___y_5566_, 2);
v___x_5569_ = l_Lean_Elab_pp_macroStack;
v___x_5570_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5568_, v___x_5569_);
v___x_5571_ = lean_bool_not(v___x_5570_);
if (v___x_5571_ == 0)
{
if (lean_obj_tag(v_macroStack_5565_) == 0)
{
lean_object* v___x_5572_; 
v___x_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5572_, 0, v_msgData_5564_);
return v___x_5572_;
}
else
{
lean_object* v_head_5573_; lean_object* v_after_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5589_; 
v_head_5573_ = lean_ctor_get(v_macroStack_5565_, 0);
lean_inc(v_head_5573_);
v_after_5574_ = lean_ctor_get(v_head_5573_, 1);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_head_5573_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; 
v_unused_5590_ = lean_ctor_get(v_head_5573_, 0);
lean_dec(v_unused_5590_);
v___x_5576_ = v_head_5573_;
v_isShared_5577_ = v_isSharedCheck_5589_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_after_5574_);
lean_dec(v_head_5573_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5589_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5578_; lean_object* v___x_5580_; 
v___x_5578_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5577_ == 0)
{
lean_ctor_set_tag(v___x_5576_, 7);
lean_ctor_set(v___x_5576_, 1, v___x_5578_);
lean_ctor_set(v___x_5576_, 0, v_msgData_5564_);
v___x_5580_ = v___x_5576_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_msgData_5564_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v_msgData_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5581_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5580_);
lean_ctor_set(v___x_5582_, 1, v___x_5581_);
v___x_5583_ = l_Lean_MessageData_ofSyntax(v_after_5574_);
v___x_5584_ = l_Lean_indentD(v___x_5583_);
v_msgData_5585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5585_, 0, v___x_5582_);
lean_ctor_set(v_msgData_5585_, 1, v___x_5584_);
v___x_5586_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5585_, v_macroStack_5565_);
v___x_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
return v___x_5587_;
}
}
}
}
else
{
lean_object* v___x_5591_; 
lean_dec(v_macroStack_5565_);
v___x_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5591_, 0, v_msgData_5564_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5592_, lean_object* v_macroStack_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5592_, v_macroStack_5593_, v___y_5594_);
lean_dec_ref(v___y_5594_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_ref_5605_; lean_object* v___x_5606_; lean_object* v_a_5607_; lean_object* v_macroStack_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5619_; 
v_ref_5605_ = lean_ctor_get(v___y_5602_, 5);
v___x_5606_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5597_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
v_a_5607_ = lean_ctor_get(v___x_5606_, 0);
lean_inc(v_a_5607_);
lean_dec_ref(v___x_5606_);
v_macroStack_5608_ = lean_ctor_get(v___y_5598_, 1);
v___x_5609_ = l_Lean_Elab_getBetterRef(v_ref_5605_, v_macroStack_5608_);
lean_inc(v_macroStack_5608_);
v___x_5610_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5607_, v_macroStack_5608_, v___y_5602_);
v_a_5611_ = lean_ctor_get(v___x_5610_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5610_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5613_ = v___x_5610_;
v_isShared_5614_ = v_isSharedCheck_5619_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5610_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5619_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5615_; lean_object* v___x_5617_; 
v___x_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5609_);
lean_ctor_set(v___x_5615_, 1, v_a_5611_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set_tag(v___x_5613_, 1);
lean_ctor_set(v___x_5613_, 0, v___x_5615_);
v___x_5617_ = v___x_5613_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v_res_5628_; 
v_res_5628_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
return v_res_5628_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5631_ = l_Lean_stringToMessageData(v___x_5630_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5632_, size_t v_sz_5633_, size_t v_i_5634_, lean_object* v_b_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v_a_5644_; uint8_t v___x_5648_; 
v___x_5648_ = lean_usize_dec_lt(v_i_5634_, v_sz_5633_);
if (v___x_5648_ == 0)
{
lean_object* v___x_5649_; 
v___x_5649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5649_, 0, v_b_5635_);
return v___x_5649_;
}
else
{
lean_object* v_a_5650_; lean_object* v___x_5651_; 
v_a_5650_ = lean_array_uget_borrowed(v_as_5632_, v_i_5634_);
lean_inc(v_a_5650_);
v___x_5651_ = l_Lean_MVarId_getType(v_a_5650_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; lean_object* v___x_5653_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref_known(v___x_5651_, 1);
lean_inc(v_a_5650_);
v___x_5653_ = l_Lean_MVarId_getType(v_a_5650_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_a_5654_);
lean_dec_ref_known(v___x_5653_, 1);
v___x_5655_ = lean_box(0);
v___x_5656_ = l_Lean_getRecAppSyntax_x3f(v_a_5654_);
lean_dec(v_a_5654_);
if (lean_obj_tag(v___x_5656_) == 1)
{
lean_object* v_val_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v_val_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_val_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = l_Lean_Expr_mdataExpr_x21(v_a_5652_);
lean_dec(v_a_5652_);
lean_inc(v_a_5650_);
v___x_5659_ = l_Lean_MVarId_setType___redArg(v_a_5650_, v___x_5658_, v___y_5639_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_fileName_5660_; lean_object* v_fileMap_5661_; lean_object* v_options_5662_; lean_object* v_currRecDepth_5663_; lean_object* v_maxRecDepth_5664_; lean_object* v_ref_5665_; lean_object* v_currNamespace_5666_; lean_object* v_openDecls_5667_; lean_object* v_initHeartbeats_5668_; lean_object* v_maxHeartbeats_5669_; lean_object* v_quotContext_5670_; lean_object* v_currMacroScope_5671_; uint8_t v_diag_5672_; lean_object* v_cancelTk_x3f_5673_; uint8_t v_suppressElabErrors_5674_; lean_object* v_inheritedTraceOptions_5675_; lean_object* v_ref_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; 
lean_dec_ref_known(v___x_5659_, 1);
v_fileName_5660_ = lean_ctor_get(v___y_5640_, 0);
v_fileMap_5661_ = lean_ctor_get(v___y_5640_, 1);
v_options_5662_ = lean_ctor_get(v___y_5640_, 2);
v_currRecDepth_5663_ = lean_ctor_get(v___y_5640_, 3);
v_maxRecDepth_5664_ = lean_ctor_get(v___y_5640_, 4);
v_ref_5665_ = lean_ctor_get(v___y_5640_, 5);
v_currNamespace_5666_ = lean_ctor_get(v___y_5640_, 6);
v_openDecls_5667_ = lean_ctor_get(v___y_5640_, 7);
v_initHeartbeats_5668_ = lean_ctor_get(v___y_5640_, 8);
v_maxHeartbeats_5669_ = lean_ctor_get(v___y_5640_, 9);
v_quotContext_5670_ = lean_ctor_get(v___y_5640_, 10);
v_currMacroScope_5671_ = lean_ctor_get(v___y_5640_, 11);
v_diag_5672_ = lean_ctor_get_uint8(v___y_5640_, sizeof(void*)*14);
v_cancelTk_x3f_5673_ = lean_ctor_get(v___y_5640_, 12);
v_suppressElabErrors_5674_ = lean_ctor_get_uint8(v___y_5640_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5675_ = lean_ctor_get(v___y_5640_, 13);
v_ref_5676_ = l_Lean_replaceRef(v_val_5657_, v_ref_5665_);
lean_dec(v_val_5657_);
lean_inc_ref(v_inheritedTraceOptions_5675_);
lean_inc(v_cancelTk_x3f_5673_);
lean_inc(v_currMacroScope_5671_);
lean_inc(v_quotContext_5670_);
lean_inc(v_maxHeartbeats_5669_);
lean_inc(v_initHeartbeats_5668_);
lean_inc(v_openDecls_5667_);
lean_inc(v_currNamespace_5666_);
lean_inc(v_maxRecDepth_5664_);
lean_inc(v_currRecDepth_5663_);
lean_inc_ref(v_options_5662_);
lean_inc_ref(v_fileMap_5661_);
lean_inc_ref(v_fileName_5660_);
v___x_5677_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5677_, 0, v_fileName_5660_);
lean_ctor_set(v___x_5677_, 1, v_fileMap_5661_);
lean_ctor_set(v___x_5677_, 2, v_options_5662_);
lean_ctor_set(v___x_5677_, 3, v_currRecDepth_5663_);
lean_ctor_set(v___x_5677_, 4, v_maxRecDepth_5664_);
lean_ctor_set(v___x_5677_, 5, v_ref_5676_);
lean_ctor_set(v___x_5677_, 6, v_currNamespace_5666_);
lean_ctor_set(v___x_5677_, 7, v_openDecls_5667_);
lean_ctor_set(v___x_5677_, 8, v_initHeartbeats_5668_);
lean_ctor_set(v___x_5677_, 9, v_maxHeartbeats_5669_);
lean_ctor_set(v___x_5677_, 10, v_quotContext_5670_);
lean_ctor_set(v___x_5677_, 11, v_currMacroScope_5671_);
lean_ctor_set(v___x_5677_, 12, v_cancelTk_x3f_5673_);
lean_ctor_set(v___x_5677_, 13, v_inheritedTraceOptions_5675_);
lean_ctor_set_uint8(v___x_5677_, sizeof(void*)*14, v_diag_5672_);
lean_ctor_set_uint8(v___x_5677_, sizeof(void*)*14 + 1, v_suppressElabErrors_5674_);
lean_inc(v_a_5650_);
v___x_5678_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5650_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___x_5677_, v___y_5641_);
lean_dec_ref_known(v___x_5677_, 14);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_dec_ref_known(v___x_5678_, 1);
v_a_5644_ = v___x_5655_;
goto v___jp_5643_;
}
else
{
return v___x_5678_;
}
}
else
{
lean_dec(v_val_5657_);
return v___x_5659_;
}
}
else
{
lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; 
lean_dec(v___x_5656_);
v___x_5679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5680_ = l_Lean_indentExpr(v_a_5652_);
v___x_5681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5679_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5681_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_dec_ref_known(v___x_5682_, 1);
v_a_5644_ = v___x_5655_;
goto v___jp_5643_;
}
else
{
return v___x_5682_;
}
}
}
else
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
lean_dec(v_a_5652_);
v_a_5683_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5653_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5653_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
v_a_5691_ = lean_ctor_get(v___x_5651_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5651_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5693_ = v___x_5651_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5651_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
}
v___jp_5643_:
{
size_t v___x_5645_; size_t v___x_5646_; 
v___x_5645_ = ((size_t)1ULL);
v___x_5646_ = lean_usize_add(v_i_5634_, v___x_5645_);
v_i_5634_ = v___x_5646_;
v_b_5635_ = v_a_5644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5699_, lean_object* v_sz_5700_, lean_object* v_i_5701_, lean_object* v_b_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
size_t v_sz_boxed_5710_; size_t v_i_boxed_5711_; lean_object* v_res_5712_; 
v_sz_boxed_5710_ = lean_unbox_usize(v_sz_5700_);
lean_dec(v_sz_5700_);
v_i_boxed_5711_ = lean_unbox_usize(v_i_5701_);
lean_dec(v_i_5701_);
v_res_5712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5699_, v_sz_boxed_5710_, v_i_boxed_5711_, v_b_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
lean_dec(v___y_5704_);
lean_dec_ref(v___y_5703_);
lean_dec_ref(v_as_5699_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5713_, size_t v_i_5714_, size_t v_stop_5715_, lean_object* v_b_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
uint8_t v___x_5722_; 
v___x_5722_ = lean_usize_dec_eq(v_i_5714_, v_stop_5715_);
if (v___x_5722_ == 0)
{
lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5723_ = lean_array_uget_borrowed(v_as_5713_, v_i_5714_);
lean_inc(v___x_5723_);
v___x_5724_ = l_Lean_MVarId_getType(v___x_5723_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_a_5725_);
lean_dec_ref_known(v___x_5724_, 1);
v___x_5726_ = l_Lean_Expr_mdataExpr_x21(v_a_5725_);
lean_dec(v_a_5725_);
lean_inc(v___x_5723_);
v___x_5727_ = l_Lean_MVarId_setType___redArg(v___x_5723_, v___x_5726_, v___y_5718_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_object* v_a_5728_; size_t v___x_5729_; size_t v___x_5730_; 
v_a_5728_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_a_5728_);
lean_dec_ref_known(v___x_5727_, 1);
v___x_5729_ = ((size_t)1ULL);
v___x_5730_ = lean_usize_add(v_i_5714_, v___x_5729_);
v_i_5714_ = v___x_5730_;
v_b_5716_ = v_a_5728_;
goto _start;
}
else
{
return v___x_5727_;
}
}
else
{
lean_object* v_a_5732_; lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5739_; 
v_a_5732_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5739_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5739_ == 0)
{
v___x_5734_ = v___x_5724_;
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
else
{
lean_inc(v_a_5732_);
lean_dec(v___x_5724_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v___x_5737_; 
if (v_isShared_5735_ == 0)
{
v___x_5737_ = v___x_5734_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v_a_5732_);
v___x_5737_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
return v___x_5737_;
}
}
}
}
else
{
lean_object* v___x_5740_; 
v___x_5740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5740_, 0, v_b_5716_);
return v___x_5740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5741_, lean_object* v_i_5742_, lean_object* v_stop_5743_, lean_object* v_b_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_){
_start:
{
size_t v_i_boxed_5750_; size_t v_stop_boxed_5751_; lean_object* v_res_5752_; 
v_i_boxed_5750_ = lean_unbox_usize(v_i_5742_);
lean_dec(v_i_5742_);
v_stop_boxed_5751_ = lean_unbox_usize(v_stop_5743_);
lean_dec(v_stop_5743_);
v_res_5752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5741_, v_i_boxed_5750_, v_stop_boxed_5751_, v_b_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
lean_dec(v___y_5748_);
lean_dec_ref(v___y_5747_);
lean_dec(v___y_5746_);
lean_dec_ref(v___y_5745_);
lean_dec_ref(v_as_5741_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5753_, lean_object* v___x_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
if (lean_obj_tag(v___x_5753_) == 0)
{
lean_object* v___x_5762_; size_t v_sz_5763_; size_t v___x_5764_; lean_object* v___x_5765_; 
v___x_5762_ = lean_box(0);
v_sz_5763_ = lean_array_size(v___x_5754_);
v___x_5764_ = ((size_t)0ULL);
v___x_5765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5754_, v_sz_5763_, v___x_5764_, v___x_5762_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec_ref(v___x_5754_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5772_ == 0)
{
lean_object* v_unused_5773_; 
v_unused_5773_ = lean_ctor_get(v___x_5765_, 0);
lean_dec(v_unused_5773_);
v___x_5767_ = v___x_5765_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_dec(v___x_5765_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 0, v___x_5762_);
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5762_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
else
{
return v___x_5765_;
}
}
else
{
lean_object* v_val_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5853_; 
v_val_5774_ = lean_ctor_get(v___x_5753_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5776_ = v___x_5753_;
v_isShared_5777_ = v_isSharedCheck_5853_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_val_5774_);
lean_dec(v___x_5753_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5853_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v_ref_5778_; lean_object* v_tactic_5779_; lean_object* v_fileName_5780_; lean_object* v_fileMap_5781_; lean_object* v_options_5782_; lean_object* v_currRecDepth_5783_; lean_object* v_maxRecDepth_5784_; lean_object* v_ref_5785_; lean_object* v_currNamespace_5786_; lean_object* v_openDecls_5787_; lean_object* v_initHeartbeats_5788_; lean_object* v_maxHeartbeats_5789_; lean_object* v_quotContext_5790_; lean_object* v_currMacroScope_5791_; uint8_t v_diag_5792_; lean_object* v_cancelTk_x3f_5793_; uint8_t v_suppressElabErrors_5794_; lean_object* v_inheritedTraceOptions_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v_ref_5798_; lean_object* v___x_5799_; lean_object* v___y_5826_; lean_object* v___y_5843_; uint8_t v___x_5844_; 
v_ref_5778_ = lean_ctor_get(v_val_5774_, 0);
lean_inc(v_ref_5778_);
v_tactic_5779_ = lean_ctor_get(v_val_5774_, 1);
lean_inc(v_tactic_5779_);
lean_dec(v_val_5774_);
v_fileName_5780_ = lean_ctor_get(v___y_5759_, 0);
v_fileMap_5781_ = lean_ctor_get(v___y_5759_, 1);
v_options_5782_ = lean_ctor_get(v___y_5759_, 2);
v_currRecDepth_5783_ = lean_ctor_get(v___y_5759_, 3);
v_maxRecDepth_5784_ = lean_ctor_get(v___y_5759_, 4);
v_ref_5785_ = lean_ctor_get(v___y_5759_, 5);
v_currNamespace_5786_ = lean_ctor_get(v___y_5759_, 6);
v_openDecls_5787_ = lean_ctor_get(v___y_5759_, 7);
v_initHeartbeats_5788_ = lean_ctor_get(v___y_5759_, 8);
v_maxHeartbeats_5789_ = lean_ctor_get(v___y_5759_, 9);
v_quotContext_5790_ = lean_ctor_get(v___y_5759_, 10);
v_currMacroScope_5791_ = lean_ctor_get(v___y_5759_, 11);
v_diag_5792_ = lean_ctor_get_uint8(v___y_5759_, sizeof(void*)*14);
v_cancelTk_x3f_5793_ = lean_ctor_get(v___y_5759_, 12);
v_suppressElabErrors_5794_ = lean_ctor_get_uint8(v___y_5759_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5795_ = lean_ctor_get(v___y_5759_, 13);
v___x_5796_ = lean_unsigned_to_nat(0u);
v___x_5797_ = lean_array_get_size(v___x_5754_);
v_ref_5798_ = l_Lean_replaceRef(v_ref_5778_, v_ref_5785_);
lean_inc_ref(v_inheritedTraceOptions_5795_);
lean_inc(v_cancelTk_x3f_5793_);
lean_inc(v_currMacroScope_5791_);
lean_inc(v_quotContext_5790_);
lean_inc(v_maxHeartbeats_5789_);
lean_inc(v_initHeartbeats_5788_);
lean_inc(v_openDecls_5787_);
lean_inc(v_currNamespace_5786_);
lean_inc(v_maxRecDepth_5784_);
lean_inc(v_currRecDepth_5783_);
lean_inc_ref(v_options_5782_);
lean_inc_ref(v_fileMap_5781_);
lean_inc_ref(v_fileName_5780_);
v___x_5799_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5799_, 0, v_fileName_5780_);
lean_ctor_set(v___x_5799_, 1, v_fileMap_5781_);
lean_ctor_set(v___x_5799_, 2, v_options_5782_);
lean_ctor_set(v___x_5799_, 3, v_currRecDepth_5783_);
lean_ctor_set(v___x_5799_, 4, v_maxRecDepth_5784_);
lean_ctor_set(v___x_5799_, 5, v_ref_5798_);
lean_ctor_set(v___x_5799_, 6, v_currNamespace_5786_);
lean_ctor_set(v___x_5799_, 7, v_openDecls_5787_);
lean_ctor_set(v___x_5799_, 8, v_initHeartbeats_5788_);
lean_ctor_set(v___x_5799_, 9, v_maxHeartbeats_5789_);
lean_ctor_set(v___x_5799_, 10, v_quotContext_5790_);
lean_ctor_set(v___x_5799_, 11, v_currMacroScope_5791_);
lean_ctor_set(v___x_5799_, 12, v_cancelTk_x3f_5793_);
lean_ctor_set(v___x_5799_, 13, v_inheritedTraceOptions_5795_);
lean_ctor_set_uint8(v___x_5799_, sizeof(void*)*14, v_diag_5792_);
lean_ctor_set_uint8(v___x_5799_, sizeof(void*)*14 + 1, v_suppressElabErrors_5794_);
v___x_5844_ = lean_nat_dec_lt(v___x_5796_, v___x_5797_);
if (v___x_5844_ == 0)
{
goto v___jp_5827_;
}
else
{
lean_object* v___x_5845_; uint8_t v___x_5846_; 
v___x_5845_ = lean_box(0);
v___x_5846_ = lean_nat_dec_le(v___x_5797_, v___x_5797_);
if (v___x_5846_ == 0)
{
if (v___x_5844_ == 0)
{
goto v___jp_5827_;
}
else
{
size_t v___x_5847_; size_t v___x_5848_; lean_object* v___x_5849_; 
v___x_5847_ = ((size_t)0ULL);
v___x_5848_ = lean_usize_of_nat(v___x_5797_);
v___x_5849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5754_, v___x_5847_, v___x_5848_, v___x_5845_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
v___y_5843_ = v___x_5849_;
goto v___jp_5842_;
}
}
else
{
size_t v___x_5850_; size_t v___x_5851_; lean_object* v___x_5852_; 
v___x_5850_ = ((size_t)0ULL);
v___x_5851_ = lean_usize_of_nat(v___x_5797_);
v___x_5852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5754_, v___x_5850_, v___x_5851_, v___x_5845_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
v___y_5843_ = v___x_5852_;
goto v___jp_5842_;
}
}
v___jp_5800_:
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___f_5804_; lean_object* v___x_5805_; 
v___x_5801_ = lean_box(0);
v___x_5802_ = lean_array_get(v___x_5801_, v___x_5754_, v___x_5796_);
v___x_5803_ = lean_array_to_list(v___x_5754_);
v___f_5804_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5804_, 0, v___x_5803_);
lean_closure_set(v___f_5804_, 1, v_ref_5778_);
lean_closure_set(v___f_5804_, 2, v_tactic_5779_);
v___x_5805_ = l_Lean_Elab_Tactic_run(v___x_5802_, v___f_5804_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
if (lean_obj_tag(v___x_5805_) == 0)
{
lean_object* v_a_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5816_; 
v_a_5806_ = lean_ctor_get(v___x_5805_, 0);
v_isSharedCheck_5816_ = !lean_is_exclusive(v___x_5805_);
if (v_isSharedCheck_5816_ == 0)
{
v___x_5808_ = v___x_5805_;
v_isShared_5809_ = v_isSharedCheck_5816_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_a_5806_);
lean_dec(v___x_5805_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5816_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
uint8_t v___x_5810_; 
v___x_5810_ = l_List_isEmpty___redArg(v_a_5806_);
if (v___x_5810_ == 0)
{
lean_object* v___x_5811_; 
lean_del_object(v___x_5808_);
v___x_5811_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5806_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
lean_dec_ref_known(v___x_5799_, 14);
return v___x_5811_;
}
else
{
lean_object* v___x_5812_; lean_object* v___x_5814_; 
lean_dec(v_a_5806_);
lean_dec_ref_known(v___x_5799_, 14);
v___x_5812_ = lean_box(0);
if (v_isShared_5809_ == 0)
{
lean_ctor_set(v___x_5808_, 0, v___x_5812_);
v___x_5814_ = v___x_5808_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v___x_5812_);
v___x_5814_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
return v___x_5814_;
}
}
}
}
else
{
lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5824_; 
lean_dec_ref_known(v___x_5799_, 14);
v_a_5817_ = lean_ctor_get(v___x_5805_, 0);
v_isSharedCheck_5824_ = !lean_is_exclusive(v___x_5805_);
if (v_isSharedCheck_5824_ == 0)
{
v___x_5819_ = v___x_5805_;
v_isShared_5820_ = v_isSharedCheck_5824_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5805_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5824_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5822_; 
if (v_isShared_5820_ == 0)
{
v___x_5822_ = v___x_5819_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_a_5817_);
v___x_5822_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
return v___x_5822_;
}
}
}
}
v___jp_5825_:
{
if (lean_obj_tag(v___y_5826_) == 0)
{
lean_dec_ref_known(v___y_5826_, 1);
goto v___jp_5800_;
}
else
{
lean_dec_ref_known(v___x_5799_, 14);
lean_dec(v_tactic_5779_);
lean_dec(v_ref_5778_);
lean_dec_ref(v___x_5754_);
return v___y_5826_;
}
}
v___jp_5827_:
{
uint8_t v___x_5828_; 
v___x_5828_ = lean_nat_dec_eq(v___x_5797_, v___x_5796_);
if (v___x_5828_ == 0)
{
uint8_t v___x_5829_; 
lean_del_object(v___x_5776_);
v___x_5829_ = lean_nat_dec_lt(v___x_5796_, v___x_5797_);
if (v___x_5829_ == 0)
{
goto v___jp_5800_;
}
else
{
lean_object* v___x_5830_; uint8_t v___x_5831_; 
v___x_5830_ = lean_box(0);
v___x_5831_ = lean_nat_dec_le(v___x_5797_, v___x_5797_);
if (v___x_5831_ == 0)
{
if (v___x_5829_ == 0)
{
goto v___jp_5800_;
}
else
{
size_t v___x_5832_; size_t v___x_5833_; lean_object* v___x_5834_; 
v___x_5832_ = ((size_t)0ULL);
v___x_5833_ = lean_usize_of_nat(v___x_5797_);
v___x_5834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5754_, v___x_5832_, v___x_5833_, v___x_5830_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
v___y_5826_ = v___x_5834_;
goto v___jp_5825_;
}
}
else
{
size_t v___x_5835_; size_t v___x_5836_; lean_object* v___x_5837_; 
v___x_5835_ = ((size_t)0ULL);
v___x_5836_ = lean_usize_of_nat(v___x_5797_);
v___x_5837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5754_, v___x_5835_, v___x_5836_, v___x_5830_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___x_5799_, v___y_5760_);
v___y_5826_ = v___x_5837_;
goto v___jp_5825_;
}
}
}
else
{
lean_object* v___x_5838_; lean_object* v___x_5840_; 
lean_dec_ref_known(v___x_5799_, 14);
lean_dec(v_tactic_5779_);
lean_dec(v_ref_5778_);
lean_dec_ref(v___x_5754_);
v___x_5838_ = lean_box(0);
if (v_isShared_5777_ == 0)
{
lean_ctor_set_tag(v___x_5776_, 0);
lean_ctor_set(v___x_5776_, 0, v___x_5838_);
v___x_5840_ = v___x_5776_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5838_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
v___jp_5842_:
{
if (lean_obj_tag(v___y_5843_) == 0)
{
lean_dec_ref_known(v___y_5843_, 1);
goto v___jp_5827_;
}
else
{
lean_dec_ref_known(v___x_5799_, 14);
lean_dec(v_tactic_5779_);
lean_dec(v_ref_5778_);
lean_del_object(v___x_5776_);
lean_dec_ref(v___x_5754_);
return v___y_5843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5854_, lean_object* v___x_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_){
_start:
{
lean_object* v_res_5863_; 
v_res_5863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5854_, v___x_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec_ref(v___y_5856_);
return v_res_5863_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5864_){
_start:
{
uint8_t v___x_5865_; 
v___x_5865_ = 0;
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5866_){
_start:
{
uint8_t v_res_5867_; lean_object* v_r_5868_; 
v_res_5867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5866_);
lean_dec(v_x_5866_);
v_r_5868_ = lean_box(v_res_5867_);
return v_r_5868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5875_, size_t v_sz_5876_, size_t v_i_5877_, lean_object* v_b_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_){
_start:
{
uint8_t v___x_5884_; 
v___x_5884_ = lean_usize_dec_lt(v_i_5877_, v_sz_5876_);
if (v___x_5884_ == 0)
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5885_, 0, v_b_5878_);
return v___x_5885_;
}
else
{
lean_object* v_snd_5886_; lean_object* v_fst_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5958_; 
v_snd_5886_ = lean_ctor_get(v_b_5878_, 1);
v_fst_5887_ = lean_ctor_get(v_b_5878_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v_b_5878_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5889_ = v_b_5878_;
v_isShared_5890_ = v_isSharedCheck_5958_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_snd_5886_);
lean_inc(v_fst_5887_);
lean_dec(v_b_5878_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5958_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v_array_5891_; lean_object* v_start_5892_; lean_object* v_stop_5893_; uint8_t v___x_5894_; 
v_array_5891_ = lean_ctor_get(v_snd_5886_, 0);
v_start_5892_ = lean_ctor_get(v_snd_5886_, 1);
v_stop_5893_ = lean_ctor_get(v_snd_5886_, 2);
v___x_5894_ = lean_nat_dec_lt(v_start_5892_, v_stop_5893_);
if (v___x_5894_ == 0)
{
lean_object* v___x_5896_; 
if (v_isShared_5890_ == 0)
{
v___x_5896_ = v___x_5889_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_fst_5887_);
lean_ctor_set(v_reuseFailAlloc_5898_, 1, v_snd_5886_);
v___x_5896_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
lean_object* v___x_5897_; 
v___x_5897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5896_);
return v___x_5897_;
}
}
else
{
lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5954_; 
lean_inc(v_stop_5893_);
lean_inc(v_start_5892_);
lean_inc_ref(v_array_5891_);
v_isSharedCheck_5954_ = !lean_is_exclusive(v_snd_5886_);
if (v_isSharedCheck_5954_ == 0)
{
lean_object* v_unused_5955_; lean_object* v_unused_5956_; lean_object* v_unused_5957_; 
v_unused_5955_ = lean_ctor_get(v_snd_5886_, 2);
lean_dec(v_unused_5955_);
v_unused_5956_ = lean_ctor_get(v_snd_5886_, 1);
lean_dec(v_unused_5956_);
v_unused_5957_ = lean_ctor_get(v_snd_5886_, 0);
lean_dec(v_unused_5957_);
v___x_5900_ = v_snd_5886_;
v_isShared_5901_ = v_isSharedCheck_5954_;
goto v_resetjp_5899_;
}
else
{
lean_dec(v_snd_5886_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5954_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v_array_5902_; lean_object* v_start_5903_; lean_object* v_stop_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5909_; 
v_array_5902_ = lean_ctor_get(v_fst_5887_, 0);
v_start_5903_ = lean_ctor_get(v_fst_5887_, 1);
v_stop_5904_ = lean_ctor_get(v_fst_5887_, 2);
v___x_5905_ = lean_array_fget(v_array_5891_, v_start_5892_);
v___x_5906_ = lean_unsigned_to_nat(1u);
v___x_5907_ = lean_nat_add(v_start_5892_, v___x_5906_);
lean_dec(v_start_5892_);
if (v_isShared_5901_ == 0)
{
lean_ctor_set(v___x_5900_, 1, v___x_5907_);
v___x_5909_ = v___x_5900_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_array_5891_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v___x_5907_);
lean_ctor_set(v_reuseFailAlloc_5953_, 2, v_stop_5893_);
v___x_5909_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
uint8_t v___x_5910_; 
v___x_5910_ = lean_nat_dec_lt(v_start_5903_, v_stop_5904_);
if (v___x_5910_ == 0)
{
lean_object* v___x_5912_; 
lean_dec(v___x_5905_);
if (v_isShared_5890_ == 0)
{
lean_ctor_set(v___x_5889_, 1, v___x_5909_);
v___x_5912_ = v___x_5889_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_fst_5887_);
lean_ctor_set(v_reuseFailAlloc_5914_, 1, v___x_5909_);
v___x_5912_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
lean_object* v___x_5913_; 
v___x_5913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
return v___x_5913_;
}
}
else
{
lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5949_; 
lean_inc(v_stop_5904_);
lean_inc(v_start_5903_);
lean_inc_ref(v_array_5902_);
v_isSharedCheck_5949_ = !lean_is_exclusive(v_fst_5887_);
if (v_isSharedCheck_5949_ == 0)
{
lean_object* v_unused_5950_; lean_object* v_unused_5951_; lean_object* v_unused_5952_; 
v_unused_5950_ = lean_ctor_get(v_fst_5887_, 2);
lean_dec(v_unused_5950_);
v_unused_5951_ = lean_ctor_get(v_fst_5887_, 1);
lean_dec(v_unused_5951_);
v_unused_5952_ = lean_ctor_get(v_fst_5887_, 0);
lean_dec(v_unused_5952_);
v___x_5916_ = v_fst_5887_;
v_isShared_5917_ = v_isSharedCheck_5949_;
goto v_resetjp_5915_;
}
else
{
lean_dec(v_fst_5887_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5949_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v___f_5918_; lean_object* v_a_5919_; lean_object* v___x_5920_; lean_object* v___y_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; uint8_t v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___f_5918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5919_ = lean_array_uget_borrowed(v_as_5875_, v_i_5877_);
v___x_5920_ = lean_array_fget_borrowed(v_array_5902_, v_start_5903_);
lean_inc(v___x_5920_);
v___y_5921_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5921_, 0, v___x_5905_);
lean_closure_set(v___y_5921_, 1, v___x_5920_);
lean_inc(v_a_5919_);
v___x_5922_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5922_, 0, lean_box(0));
lean_closure_set(v___x_5922_, 1, v_a_5919_);
lean_closure_set(v___x_5922_, 2, v___y_5921_);
v___x_5923_ = lean_box(0);
v___x_5924_ = lean_box(0);
v___x_5925_ = lean_box(1);
v___x_5926_ = 0;
v___x_5927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5928_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5928_, 0, v___x_5923_);
lean_ctor_set(v___x_5928_, 1, v___x_5924_);
lean_ctor_set(v___x_5928_, 2, v___x_5923_);
lean_ctor_set(v___x_5928_, 3, v___f_5918_);
lean_ctor_set(v___x_5928_, 4, v___x_5925_);
lean_ctor_set(v___x_5928_, 5, v___x_5925_);
lean_ctor_set(v___x_5928_, 6, v___x_5923_);
lean_ctor_set(v___x_5928_, 7, v___x_5927_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8, v___x_5910_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 1, v___x_5910_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 2, v___x_5910_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 3, v___x_5910_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 4, v___x_5926_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 5, v___x_5926_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 6, v___x_5926_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 7, v___x_5926_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 8, v___x_5910_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 9, v___x_5926_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*8 + 10, v___x_5910_);
v___x_5929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5930_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5922_, v___x_5928_, v___x_5929_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
if (lean_obj_tag(v___x_5930_) == 0)
{
lean_object* v___x_5931_; lean_object* v___x_5933_; 
lean_dec_ref_known(v___x_5930_, 1);
v___x_5931_ = lean_nat_add(v_start_5903_, v___x_5906_);
lean_dec(v_start_5903_);
if (v_isShared_5917_ == 0)
{
lean_ctor_set(v___x_5916_, 1, v___x_5931_);
v___x_5933_ = v___x_5916_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_array_5902_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v___x_5931_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_stop_5904_);
v___x_5933_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_object* v___x_5935_; 
if (v_isShared_5890_ == 0)
{
lean_ctor_set(v___x_5889_, 1, v___x_5909_);
lean_ctor_set(v___x_5889_, 0, v___x_5933_);
v___x_5935_ = v___x_5889_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v___x_5933_);
lean_ctor_set(v_reuseFailAlloc_5939_, 1, v___x_5909_);
v___x_5935_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
size_t v___x_5936_; size_t v___x_5937_; 
v___x_5936_ = ((size_t)1ULL);
v___x_5937_ = lean_usize_add(v_i_5877_, v___x_5936_);
v_i_5877_ = v___x_5937_;
v_b_5878_ = v___x_5935_;
goto _start;
}
}
}
else
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5948_; 
lean_del_object(v___x_5916_);
lean_dec_ref(v___x_5909_);
lean_dec(v_stop_5904_);
lean_dec(v_start_5903_);
lean_dec_ref(v_array_5902_);
lean_del_object(v___x_5889_);
v_a_5941_ = lean_ctor_get(v___x_5930_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v___x_5930_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5943_ = v___x_5930_;
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5930_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5946_; 
if (v_isShared_5944_ == 0)
{
v___x_5946_ = v___x_5943_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5959_, lean_object* v_sz_5960_, lean_object* v_i_5961_, lean_object* v_b_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_){
_start:
{
size_t v_sz_boxed_5968_; size_t v_i_boxed_5969_; lean_object* v_res_5970_; 
v_sz_boxed_5968_ = lean_unbox_usize(v_sz_5960_);
lean_dec(v_sz_5960_);
v_i_boxed_5969_ = lean_unbox_usize(v_i_5961_);
lean_dec(v_i_5961_);
v_res_5970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5959_, v_sz_boxed_5968_, v_i_boxed_5969_, v_b_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v___y_5966_);
lean_dec_ref(v___y_5965_);
lean_dec(v___y_5964_);
lean_dec_ref(v___y_5963_);
lean_dec_ref(v_as_5959_);
return v_res_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5971_, lean_object* v_decrTactics_5972_, lean_object* v_argsPacker_5973_, lean_object* v_funNames_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_){
_start:
{
lean_object* v___x_5980_; 
lean_inc_ref(v_value_5971_);
v___x_5980_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5971_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v_a_5981_; lean_object* v___x_5982_; 
v_a_5981_ = lean_ctor_get(v___x_5980_, 0);
lean_inc(v_a_5981_);
lean_dec_ref_known(v___x_5980_, 1);
v___x_5982_ = l_Lean_Elab_WF_assignSubsumed(v_a_5981_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
lean_dec(v_a_5981_);
if (lean_obj_tag(v___x_5982_) == 0)
{
lean_object* v_a_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v_a_5983_ = lean_ctor_get(v___x_5982_, 0);
lean_inc(v_a_5983_);
lean_dec_ref_known(v___x_5982_, 1);
v___x_5984_ = lean_array_get_size(v_decrTactics_5972_);
v___x_5985_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5973_, v___x_5984_, v_a_5983_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
lean_dec(v_a_5983_);
if (lean_obj_tag(v___x_5985_) == 0)
{
lean_object* v_a_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; size_t v_sz_5992_; size_t v___x_5993_; lean_object* v___x_5994_; 
v_a_5986_ = lean_ctor_get(v___x_5985_, 0);
lean_inc(v_a_5986_);
lean_dec_ref_known(v___x_5985_, 1);
v___x_5987_ = lean_unsigned_to_nat(0u);
v___x_5988_ = lean_array_get_size(v_a_5986_);
v___x_5989_ = l_Array_toSubarray___redArg(v_a_5986_, v___x_5987_, v___x_5988_);
v___x_5990_ = l_Array_toSubarray___redArg(v_decrTactics_5972_, v___x_5987_, v___x_5984_);
v___x_5991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v_sz_5992_ = lean_array_size(v_funNames_5974_);
v___x_5993_ = ((size_t)0ULL);
v___x_5994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5974_, v_sz_5992_, v___x_5993_, v___x_5991_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v___x_5995_; 
lean_dec_ref_known(v___x_5994_, 1);
v___x_5995_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5971_, v___y_5976_);
return v___x_5995_;
}
else
{
lean_object* v_a_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6003_; 
lean_dec_ref(v_value_5971_);
v_a_5996_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5998_ = v___x_5994_;
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_a_5996_);
lean_dec(v___x_5994_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v___x_6001_; 
if (v_isShared_5999_ == 0)
{
v___x_6001_ = v___x_5998_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_a_5996_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
}
}
}
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
lean_dec_ref(v_decrTactics_5972_);
lean_dec_ref(v_value_5971_);
v_a_6004_ = lean_ctor_get(v___x_5985_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5985_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5985_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5985_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
return v___x_6009_;
}
}
}
}
else
{
lean_object* v_a_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6019_; 
lean_dec_ref(v_decrTactics_5972_);
lean_dec_ref(v_value_5971_);
v_a_6012_ = lean_ctor_get(v___x_5982_, 0);
v_isSharedCheck_6019_ = !lean_is_exclusive(v___x_5982_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_6014_ = v___x_5982_;
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_a_6012_);
lean_dec(v___x_5982_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6017_; 
if (v_isShared_6015_ == 0)
{
v___x_6017_ = v___x_6014_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
v___x_6017_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
return v___x_6017_;
}
}
}
}
else
{
lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec_ref(v_decrTactics_5972_);
lean_dec_ref(v_value_5971_);
v_a_6020_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_5980_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_5980_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6028_, lean_object* v_decrTactics_6029_, lean_object* v_argsPacker_6030_, lean_object* v_funNames_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6028_, v_decrTactics_6029_, v_argsPacker_6030_, v_funNames_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec_ref(v_funNames_6031_);
lean_dec_ref(v_argsPacker_6030_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6038_, uint8_t v_isExporting_6039_, lean_object* v___x_6040_, lean_object* v___y_6041_, lean_object* v___x_6042_, lean_object* v_a_x3f_6043_){
_start:
{
lean_object* v___x_6045_; lean_object* v_env_6046_; lean_object* v_nextMacroScope_6047_; lean_object* v_ngen_6048_; lean_object* v_auxDeclNGen_6049_; lean_object* v_traceState_6050_; lean_object* v_messages_6051_; lean_object* v_infoState_6052_; lean_object* v_snapshotTasks_6053_; lean_object* v___x_6055_; uint8_t v_isShared_6056_; uint8_t v_isSharedCheck_6078_; 
v___x_6045_ = lean_st_ref_take(v___y_6038_);
v_env_6046_ = lean_ctor_get(v___x_6045_, 0);
v_nextMacroScope_6047_ = lean_ctor_get(v___x_6045_, 1);
v_ngen_6048_ = lean_ctor_get(v___x_6045_, 2);
v_auxDeclNGen_6049_ = lean_ctor_get(v___x_6045_, 3);
v_traceState_6050_ = lean_ctor_get(v___x_6045_, 4);
v_messages_6051_ = lean_ctor_get(v___x_6045_, 6);
v_infoState_6052_ = lean_ctor_get(v___x_6045_, 7);
v_snapshotTasks_6053_ = lean_ctor_get(v___x_6045_, 8);
v_isSharedCheck_6078_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6078_ == 0)
{
lean_object* v_unused_6079_; 
v_unused_6079_ = lean_ctor_get(v___x_6045_, 5);
lean_dec(v_unused_6079_);
v___x_6055_ = v___x_6045_;
v_isShared_6056_ = v_isSharedCheck_6078_;
goto v_resetjp_6054_;
}
else
{
lean_inc(v_snapshotTasks_6053_);
lean_inc(v_infoState_6052_);
lean_inc(v_messages_6051_);
lean_inc(v_traceState_6050_);
lean_inc(v_auxDeclNGen_6049_);
lean_inc(v_ngen_6048_);
lean_inc(v_nextMacroScope_6047_);
lean_inc(v_env_6046_);
lean_dec(v___x_6045_);
v___x_6055_ = lean_box(0);
v_isShared_6056_ = v_isSharedCheck_6078_;
goto v_resetjp_6054_;
}
v_resetjp_6054_:
{
lean_object* v___x_6057_; lean_object* v___x_6059_; 
v___x_6057_ = l_Lean_Environment_setExporting(v_env_6046_, v_isExporting_6039_);
if (v_isShared_6056_ == 0)
{
lean_ctor_set(v___x_6055_, 5, v___x_6040_);
lean_ctor_set(v___x_6055_, 0, v___x_6057_);
v___x_6059_ = v___x_6055_;
goto v_reusejp_6058_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6057_);
lean_ctor_set(v_reuseFailAlloc_6077_, 1, v_nextMacroScope_6047_);
lean_ctor_set(v_reuseFailAlloc_6077_, 2, v_ngen_6048_);
lean_ctor_set(v_reuseFailAlloc_6077_, 3, v_auxDeclNGen_6049_);
lean_ctor_set(v_reuseFailAlloc_6077_, 4, v_traceState_6050_);
lean_ctor_set(v_reuseFailAlloc_6077_, 5, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6077_, 6, v_messages_6051_);
lean_ctor_set(v_reuseFailAlloc_6077_, 7, v_infoState_6052_);
lean_ctor_set(v_reuseFailAlloc_6077_, 8, v_snapshotTasks_6053_);
v___x_6059_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6058_;
}
v_reusejp_6058_:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v_mctx_6062_; lean_object* v_zetaDeltaFVarIds_6063_; lean_object* v_postponed_6064_; lean_object* v_diag_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6075_; 
v___x_6060_ = lean_st_ref_set(v___y_6038_, v___x_6059_);
v___x_6061_ = lean_st_ref_take(v___y_6041_);
v_mctx_6062_ = lean_ctor_get(v___x_6061_, 0);
v_zetaDeltaFVarIds_6063_ = lean_ctor_get(v___x_6061_, 2);
v_postponed_6064_ = lean_ctor_get(v___x_6061_, 3);
v_diag_6065_ = lean_ctor_get(v___x_6061_, 4);
v_isSharedCheck_6075_ = !lean_is_exclusive(v___x_6061_);
if (v_isSharedCheck_6075_ == 0)
{
lean_object* v_unused_6076_; 
v_unused_6076_ = lean_ctor_get(v___x_6061_, 1);
lean_dec(v_unused_6076_);
v___x_6067_ = v___x_6061_;
v_isShared_6068_ = v_isSharedCheck_6075_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_diag_6065_);
lean_inc(v_postponed_6064_);
lean_inc(v_zetaDeltaFVarIds_6063_);
lean_inc(v_mctx_6062_);
lean_dec(v___x_6061_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6075_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6070_; 
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 1, v___x_6042_);
v___x_6070_ = v___x_6067_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_mctx_6062_);
lean_ctor_set(v_reuseFailAlloc_6074_, 1, v___x_6042_);
lean_ctor_set(v_reuseFailAlloc_6074_, 2, v_zetaDeltaFVarIds_6063_);
lean_ctor_set(v_reuseFailAlloc_6074_, 3, v_postponed_6064_);
lean_ctor_set(v_reuseFailAlloc_6074_, 4, v_diag_6065_);
v___x_6070_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6071_ = lean_st_ref_set(v___y_6041_, v___x_6070_);
v___x_6072_ = lean_box(0);
v___x_6073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
return v___x_6073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6080_, lean_object* v_isExporting_6081_, lean_object* v___x_6082_, lean_object* v___y_6083_, lean_object* v___x_6084_, lean_object* v_a_x3f_6085_, lean_object* v___y_6086_){
_start:
{
uint8_t v_isExporting_boxed_6087_; lean_object* v_res_6088_; 
v_isExporting_boxed_6087_ = lean_unbox(v_isExporting_6081_);
v_res_6088_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6080_, v_isExporting_boxed_6087_, v___x_6082_, v___y_6083_, v___x_6084_, v_a_x3f_6085_);
lean_dec(v_a_x3f_6085_);
lean_dec(v___y_6083_);
lean_dec(v___y_6080_);
return v_res_6088_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6089_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
return v___x_6091_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
return v___x_6093_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6094_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6095_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
lean_ctor_set(v___x_6095_, 2, v___x_6094_);
lean_ctor_set(v___x_6095_, 3, v___x_6094_);
lean_ctor_set(v___x_6095_, 4, v___x_6094_);
lean_ctor_set(v___x_6095_, 5, v___x_6094_);
return v___x_6095_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6096_, uint8_t v_isExporting_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v___x_6103_; lean_object* v_env_6104_; uint8_t v_isExporting_6105_; uint8_t v___y_6172_; lean_object* v___x_6174_; uint8_t v_isModule_6175_; uint8_t v___x_6176_; 
v___x_6103_ = lean_st_ref_get(v___y_6101_);
v_env_6104_ = lean_ctor_get(v___x_6103_, 0);
lean_inc_ref(v_env_6104_);
lean_dec(v___x_6103_);
v_isExporting_6105_ = lean_ctor_get_uint8(v_env_6104_, sizeof(void*)*8);
v___x_6174_ = l_Lean_Environment_header(v_env_6104_);
lean_dec_ref(v_env_6104_);
v_isModule_6175_ = lean_ctor_get_uint8(v___x_6174_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6174_);
v___x_6176_ = lean_bool_not(v_isModule_6175_);
if (v___x_6176_ == 0)
{
if (v_isExporting_6105_ == 0)
{
if (v_isExporting_6097_ == 0)
{
lean_object* v___x_6177_; 
lean_inc(v___y_6101_);
lean_inc_ref(v___y_6100_);
lean_inc(v___y_6099_);
lean_inc_ref(v___y_6098_);
v___x_6177_ = lean_apply_5(v_x_6096_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, lean_box(0));
return v___x_6177_;
}
else
{
goto v___jp_6106_;
}
}
else
{
v___y_6172_ = v_isExporting_6097_;
goto v___jp_6171_;
}
}
else
{
v___y_6172_ = v___x_6176_;
goto v___jp_6171_;
}
v___jp_6106_:
{
lean_object* v___x_6107_; lean_object* v_env_6108_; lean_object* v_nextMacroScope_6109_; lean_object* v_ngen_6110_; lean_object* v_auxDeclNGen_6111_; lean_object* v_traceState_6112_; lean_object* v_messages_6113_; lean_object* v_infoState_6114_; lean_object* v_snapshotTasks_6115_; lean_object* v___x_6117_; uint8_t v_isShared_6118_; uint8_t v_isSharedCheck_6169_; 
v___x_6107_ = lean_st_ref_take(v___y_6101_);
v_env_6108_ = lean_ctor_get(v___x_6107_, 0);
v_nextMacroScope_6109_ = lean_ctor_get(v___x_6107_, 1);
v_ngen_6110_ = lean_ctor_get(v___x_6107_, 2);
v_auxDeclNGen_6111_ = lean_ctor_get(v___x_6107_, 3);
v_traceState_6112_ = lean_ctor_get(v___x_6107_, 4);
v_messages_6113_ = lean_ctor_get(v___x_6107_, 6);
v_infoState_6114_ = lean_ctor_get(v___x_6107_, 7);
v_snapshotTasks_6115_ = lean_ctor_get(v___x_6107_, 8);
v_isSharedCheck_6169_ = !lean_is_exclusive(v___x_6107_);
if (v_isSharedCheck_6169_ == 0)
{
lean_object* v_unused_6170_; 
v_unused_6170_ = lean_ctor_get(v___x_6107_, 5);
lean_dec(v_unused_6170_);
v___x_6117_ = v___x_6107_;
v_isShared_6118_ = v_isSharedCheck_6169_;
goto v_resetjp_6116_;
}
else
{
lean_inc(v_snapshotTasks_6115_);
lean_inc(v_infoState_6114_);
lean_inc(v_messages_6113_);
lean_inc(v_traceState_6112_);
lean_inc(v_auxDeclNGen_6111_);
lean_inc(v_ngen_6110_);
lean_inc(v_nextMacroScope_6109_);
lean_inc(v_env_6108_);
lean_dec(v___x_6107_);
v___x_6117_ = lean_box(0);
v_isShared_6118_ = v_isSharedCheck_6169_;
goto v_resetjp_6116_;
}
v_resetjp_6116_:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6119_ = l_Lean_Environment_setExporting(v_env_6108_, v_isExporting_6097_);
v___x_6120_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6118_ == 0)
{
lean_ctor_set(v___x_6117_, 5, v___x_6120_);
lean_ctor_set(v___x_6117_, 0, v___x_6119_);
v___x_6122_ = v___x_6117_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v___x_6119_);
lean_ctor_set(v_reuseFailAlloc_6168_, 1, v_nextMacroScope_6109_);
lean_ctor_set(v_reuseFailAlloc_6168_, 2, v_ngen_6110_);
lean_ctor_set(v_reuseFailAlloc_6168_, 3, v_auxDeclNGen_6111_);
lean_ctor_set(v_reuseFailAlloc_6168_, 4, v_traceState_6112_);
lean_ctor_set(v_reuseFailAlloc_6168_, 5, v___x_6120_);
lean_ctor_set(v_reuseFailAlloc_6168_, 6, v_messages_6113_);
lean_ctor_set(v_reuseFailAlloc_6168_, 7, v_infoState_6114_);
lean_ctor_set(v_reuseFailAlloc_6168_, 8, v_snapshotTasks_6115_);
v___x_6122_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v_mctx_6125_; lean_object* v_zetaDeltaFVarIds_6126_; lean_object* v_postponed_6127_; lean_object* v_diag_6128_; lean_object* v___x_6130_; uint8_t v_isShared_6131_; uint8_t v_isSharedCheck_6166_; 
v___x_6123_ = lean_st_ref_set(v___y_6101_, v___x_6122_);
v___x_6124_ = lean_st_ref_take(v___y_6099_);
v_mctx_6125_ = lean_ctor_get(v___x_6124_, 0);
v_zetaDeltaFVarIds_6126_ = lean_ctor_get(v___x_6124_, 2);
v_postponed_6127_ = lean_ctor_get(v___x_6124_, 3);
v_diag_6128_ = lean_ctor_get(v___x_6124_, 4);
v_isSharedCheck_6166_ = !lean_is_exclusive(v___x_6124_);
if (v_isSharedCheck_6166_ == 0)
{
lean_object* v_unused_6167_; 
v_unused_6167_ = lean_ctor_get(v___x_6124_, 1);
lean_dec(v_unused_6167_);
v___x_6130_ = v___x_6124_;
v_isShared_6131_ = v_isSharedCheck_6166_;
goto v_resetjp_6129_;
}
else
{
lean_inc(v_diag_6128_);
lean_inc(v_postponed_6127_);
lean_inc(v_zetaDeltaFVarIds_6126_);
lean_inc(v_mctx_6125_);
lean_dec(v___x_6124_);
v___x_6130_ = lean_box(0);
v_isShared_6131_ = v_isSharedCheck_6166_;
goto v_resetjp_6129_;
}
v_resetjp_6129_:
{
lean_object* v___x_6132_; lean_object* v___x_6134_; 
v___x_6132_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6131_ == 0)
{
lean_ctor_set(v___x_6130_, 1, v___x_6132_);
v___x_6134_ = v___x_6130_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_mctx_6125_);
lean_ctor_set(v_reuseFailAlloc_6165_, 1, v___x_6132_);
lean_ctor_set(v_reuseFailAlloc_6165_, 2, v_zetaDeltaFVarIds_6126_);
lean_ctor_set(v_reuseFailAlloc_6165_, 3, v_postponed_6127_);
lean_ctor_set(v_reuseFailAlloc_6165_, 4, v_diag_6128_);
v___x_6134_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
lean_object* v___x_6135_; lean_object* v_r_6136_; 
v___x_6135_ = lean_st_ref_set(v___y_6099_, v___x_6134_);
lean_inc(v___y_6101_);
lean_inc_ref(v___y_6100_);
lean_inc(v___y_6099_);
lean_inc_ref(v___y_6098_);
v_r_6136_ = lean_apply_5(v_x_6096_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, lean_box(0));
if (lean_obj_tag(v_r_6136_) == 0)
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6153_; 
v_a_6137_ = lean_ctor_get(v_r_6136_, 0);
v_isSharedCheck_6153_ = !lean_is_exclusive(v_r_6136_);
if (v_isSharedCheck_6153_ == 0)
{
v___x_6139_ = v_r_6136_;
v_isShared_6140_ = v_isSharedCheck_6153_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v_r_6136_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6153_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
lean_inc(v_a_6137_);
if (v_isShared_6140_ == 0)
{
lean_ctor_set_tag(v___x_6139_, 1);
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
lean_object* v___x_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
v___x_6143_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6101_, v_isExporting_6105_, v___x_6120_, v___y_6099_, v___x_6132_, v___x_6142_);
lean_dec_ref(v___x_6142_);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6143_);
if (v_isSharedCheck_6150_ == 0)
{
lean_object* v_unused_6151_; 
v_unused_6151_ = lean_ctor_get(v___x_6143_, 0);
lean_dec(v_unused_6151_);
v___x_6145_ = v___x_6143_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_dec(v___x_6143_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
lean_ctor_set(v___x_6145_, 0, v_a_6137_);
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6137_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
}
else
{
lean_object* v_a_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6163_; 
v_a_6154_ = lean_ctor_get(v_r_6136_, 0);
lean_inc(v_a_6154_);
lean_dec_ref_known(v_r_6136_, 1);
v___x_6155_ = lean_box(0);
v___x_6156_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6101_, v_isExporting_6105_, v___x_6120_, v___y_6099_, v___x_6132_, v___x_6155_);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6163_ == 0)
{
lean_object* v_unused_6164_; 
v_unused_6164_ = lean_ctor_get(v___x_6156_, 0);
lean_dec(v_unused_6164_);
v___x_6158_ = v___x_6156_;
v_isShared_6159_ = v_isSharedCheck_6163_;
goto v_resetjp_6157_;
}
else
{
lean_dec(v___x_6156_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6163_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v___x_6161_; 
if (v_isShared_6159_ == 0)
{
lean_ctor_set_tag(v___x_6158_, 1);
lean_ctor_set(v___x_6158_, 0, v_a_6154_);
v___x_6161_ = v___x_6158_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_a_6154_);
v___x_6161_ = v_reuseFailAlloc_6162_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
return v___x_6161_;
}
}
}
}
}
}
}
}
v___jp_6171_:
{
if (v___y_6172_ == 0)
{
goto v___jp_6106_;
}
else
{
lean_object* v___x_6173_; 
lean_inc(v___y_6101_);
lean_inc_ref(v___y_6100_);
lean_inc(v___y_6099_);
lean_inc_ref(v___y_6098_);
v___x_6173_ = lean_apply_5(v_x_6096_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, lean_box(0));
return v___x_6173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6178_, lean_object* v_isExporting_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_){
_start:
{
uint8_t v_isExporting_boxed_6185_; lean_object* v_res_6186_; 
v_isExporting_boxed_6185_ = lean_unbox(v_isExporting_6179_);
v_res_6186_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6178_, v_isExporting_boxed_6185_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6187_, uint8_t v_when_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_){
_start:
{
if (v_when_6188_ == 0)
{
lean_object* v___x_6194_; 
lean_inc(v___y_6192_);
lean_inc_ref(v___y_6191_);
lean_inc(v___y_6190_);
lean_inc_ref(v___y_6189_);
v___x_6194_ = lean_apply_5(v_x_6187_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, lean_box(0));
return v___x_6194_;
}
else
{
uint8_t v___x_6195_; lean_object* v___x_6196_; 
v___x_6195_ = 0;
v___x_6196_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6187_, v___x_6195_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
return v___x_6196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6197_, lean_object* v_when_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_){
_start:
{
uint8_t v_when_boxed_6204_; lean_object* v_res_6205_; 
v_when_boxed_6204_ = lean_unbox(v_when_6198_);
v_res_6205_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6197_, v_when_boxed_6204_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
return v_res_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6206_, lean_object* v_argsPacker_6207_, lean_object* v_decrTactics_6208_, lean_object* v_value_6209_, lean_object* v_a_6210_, lean_object* v_a_6211_, lean_object* v_a_6212_, lean_object* v_a_6213_){
_start:
{
lean_object* v___f_6215_; uint8_t v___x_6216_; lean_object* v___x_6217_; 
v___f_6215_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6215_, 0, v_value_6209_);
lean_closure_set(v___f_6215_, 1, v_decrTactics_6208_);
lean_closure_set(v___f_6215_, 2, v_argsPacker_6207_);
lean_closure_set(v___f_6215_, 3, v_funNames_6206_);
v___x_6216_ = 1;
v___x_6217_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6215_, v___x_6216_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6218_, lean_object* v_argsPacker_6219_, lean_object* v_decrTactics_6220_, lean_object* v_value_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6218_, v_argsPacker_6219_, v_decrTactics_6220_, v_value_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_);
lean_dec(v_a_6225_);
lean_dec_ref(v_a_6224_);
lean_dec(v_a_6223_);
lean_dec_ref(v_a_6222_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6228_, lean_object* v_msg_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
lean_object* v___x_6237_; 
v___x_6237_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_);
return v___x_6237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6238_, lean_object* v_msg_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
lean_object* v_res_6247_; 
v_res_6247_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6238_, v_msg_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
return v_res_6247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_){
_start:
{
lean_object* v___x_6257_; 
v___x_6257_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6255_);
return v___x_6257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
lean_object* v_res_6267_; 
v_res_6267_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_);
lean_dec(v___y_6265_);
lean_dec_ref(v___y_6264_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
lean_dec(v___y_6261_);
lean_dec_ref(v___y_6260_);
lean_dec(v___y_6259_);
lean_dec_ref(v___y_6258_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6268_, lean_object* v_x_6269_, lean_object* v_mkInfoTree_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
lean_object* v___x_6280_; 
v___x_6280_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6269_, v_mkInfoTree_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
return v___x_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6281_, lean_object* v_x_6282_, lean_object* v_mkInfoTree_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_){
_start:
{
lean_object* v_res_6293_; 
v_res_6293_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6281_, v_x_6282_, v_mkInfoTree_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
return v_res_6293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6294_, size_t v_i_6295_, size_t v_stop_6296_, lean_object* v_b_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v___x_6305_; 
v___x_6305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6294_, v_i_6295_, v_stop_6296_, v_b_6297_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
return v___x_6305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6306_, lean_object* v_i_6307_, lean_object* v_stop_6308_, lean_object* v_b_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_){
_start:
{
size_t v_i_boxed_6317_; size_t v_stop_boxed_6318_; lean_object* v_res_6319_; 
v_i_boxed_6317_ = lean_unbox_usize(v_i_6307_);
lean_dec(v_i_6307_);
v_stop_boxed_6318_ = lean_unbox_usize(v_stop_6308_);
lean_dec(v_stop_6308_);
v_res_6319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6306_, v_i_boxed_6317_, v_stop_boxed_6318_, v_b_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
lean_dec(v___y_6315_);
lean_dec_ref(v___y_6314_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
lean_dec_ref(v_as_6306_);
return v_res_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6320_, lean_object* v_x_6321_, uint8_t v_isExporting_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
lean_object* v___x_6328_; 
v___x_6328_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6321_, v_isExporting_6322_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
return v___x_6328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6329_, lean_object* v_x_6330_, lean_object* v_isExporting_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_){
_start:
{
uint8_t v_isExporting_boxed_6337_; lean_object* v_res_6338_; 
v_isExporting_boxed_6337_ = lean_unbox(v_isExporting_6331_);
v_res_6338_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6329_, v_x_6330_, v_isExporting_boxed_6337_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_);
lean_dec(v___y_6335_);
lean_dec_ref(v___y_6334_);
lean_dec(v___y_6333_);
lean_dec_ref(v___y_6332_);
return v_res_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6339_, lean_object* v_x_6340_, uint8_t v_when_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_){
_start:
{
lean_object* v___x_6347_; 
v___x_6347_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6340_, v_when_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_);
return v___x_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6348_, lean_object* v_x_6349_, lean_object* v_when_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_){
_start:
{
uint8_t v_when_boxed_6356_; lean_object* v_res_6357_; 
v_when_boxed_6356_ = lean_unbox(v_when_6350_);
v_res_6357_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6348_, v_x_6349_, v_when_boxed_6356_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
lean_dec(v___y_6354_);
lean_dec_ref(v___y_6353_);
lean_dec(v___y_6352_);
lean_dec_ref(v___y_6351_);
return v_res_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6358_, lean_object* v_macroStack_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_){
_start:
{
lean_object* v___x_6367_; 
v___x_6367_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6358_, v_macroStack_6359_, v___y_6364_);
return v___x_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6368_, lean_object* v_macroStack_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_){
_start:
{
lean_object* v_res_6377_; 
v_res_6377_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6368_, v_macroStack_6369_, v___y_6370_, v___y_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_);
lean_dec(v___y_6375_);
lean_dec_ref(v___y_6374_);
lean_dec(v___y_6373_);
lean_dec_ref(v___y_6372_);
lean_dec(v___y_6371_);
lean_dec_ref(v___y_6370_);
return v_res_6377_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; 
v___x_6384_ = lean_box(0);
v___x_6385_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6386_ = l_Lean_mkConst(v___x_6385_, v___x_6384_);
return v___x_6386_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6391_ = lean_box(0);
v___x_6392_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6393_ = l_Lean_mkConst(v___x_6392_, v___x_6391_);
return v___x_6393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_){
_start:
{
lean_object* v___x_6400_; 
v___x_6400_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6394_, v_a_6396_);
if (lean_obj_tag(v___x_6400_) == 0)
{
lean_object* v_a_6401_; lean_object* v___x_6403_; uint8_t v_isShared_6404_; uint8_t v_isSharedCheck_6468_; 
v_a_6401_ = lean_ctor_get(v___x_6400_, 0);
v_isSharedCheck_6468_ = !lean_is_exclusive(v___x_6400_);
if (v_isSharedCheck_6468_ == 0)
{
v___x_6403_ = v___x_6400_;
v_isShared_6404_ = v_isSharedCheck_6468_;
goto v_resetjp_6402_;
}
else
{
lean_inc(v_a_6401_);
lean_dec(v___x_6400_);
v___x_6403_ = lean_box(0);
v_isShared_6404_ = v_isSharedCheck_6468_;
goto v_resetjp_6402_;
}
v_resetjp_6402_:
{
lean_object* v___x_6410_; uint8_t v___x_6411_; 
v___x_6410_ = l_Lean_Expr_cleanupAnnotations(v_a_6401_);
v___x_6411_ = l_Lean_Expr_isApp(v___x_6410_);
if (v___x_6411_ == 0)
{
lean_dec_ref(v___x_6410_);
goto v___jp_6405_;
}
else
{
lean_object* v_arg_6412_; lean_object* v___x_6413_; uint8_t v___x_6414_; 
v_arg_6412_ = lean_ctor_get(v___x_6410_, 1);
lean_inc_ref(v_arg_6412_);
v___x_6413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6410_);
v___x_6414_ = l_Lean_Expr_isApp(v___x_6413_);
if (v___x_6414_ == 0)
{
lean_dec_ref(v___x_6413_);
lean_dec_ref(v_arg_6412_);
goto v___jp_6405_;
}
else
{
lean_object* v_arg_6415_; lean_object* v___x_6416_; uint8_t v___x_6417_; 
v_arg_6415_ = lean_ctor_get(v___x_6413_, 1);
lean_inc_ref(v_arg_6415_);
v___x_6416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6413_);
v___x_6417_ = l_Lean_Expr_isApp(v___x_6416_);
if (v___x_6417_ == 0)
{
lean_dec_ref(v___x_6416_);
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
goto v___jp_6405_;
}
else
{
lean_object* v_arg_6418_; lean_object* v___x_6419_; uint8_t v___x_6420_; 
v_arg_6418_ = lean_ctor_get(v___x_6416_, 1);
lean_inc_ref(v_arg_6418_);
v___x_6419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6416_);
v___x_6420_ = l_Lean_Expr_isApp(v___x_6419_);
if (v___x_6420_ == 0)
{
lean_dec_ref(v___x_6419_);
lean_dec_ref(v_arg_6418_);
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
goto v___jp_6405_;
}
else
{
lean_object* v___x_6421_; lean_object* v___x_6422_; uint8_t v___x_6423_; 
v___x_6421_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6419_);
v___x_6422_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6423_ = l_Lean_Expr_isConstOf(v___x_6421_, v___x_6422_);
lean_dec_ref(v___x_6421_);
if (v___x_6423_ == 0)
{
lean_dec_ref(v_arg_6418_);
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
goto v___jp_6405_;
}
else
{
lean_object* v___x_6424_; lean_object* v___x_6425_; 
lean_del_object(v___x_6403_);
v___x_6424_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6425_ = l_Lean_Meta_isExprDefEq(v_arg_6418_, v___x_6424_, v_a_6395_, v_a_6396_, v_a_6397_, v_a_6398_);
if (lean_obj_tag(v___x_6425_) == 0)
{
lean_object* v_a_6426_; lean_object* v___x_6428_; uint8_t v_isShared_6429_; uint8_t v_isSharedCheck_6459_; 
v_a_6426_ = lean_ctor_get(v___x_6425_, 0);
v_isSharedCheck_6459_ = !lean_is_exclusive(v___x_6425_);
if (v_isSharedCheck_6459_ == 0)
{
v___x_6428_ = v___x_6425_;
v_isShared_6429_ = v_isSharedCheck_6459_;
goto v_resetjp_6427_;
}
else
{
lean_inc(v_a_6426_);
lean_dec(v___x_6425_);
v___x_6428_ = lean_box(0);
v_isShared_6429_ = v_isSharedCheck_6459_;
goto v_resetjp_6427_;
}
v_resetjp_6427_:
{
uint8_t v___x_6430_; 
v___x_6430_ = lean_unbox(v_a_6426_);
lean_dec(v_a_6426_);
if (v___x_6430_ == 0)
{
lean_object* v___x_6431_; lean_object* v___x_6433_; 
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
v___x_6431_ = lean_box(0);
if (v_isShared_6429_ == 0)
{
lean_ctor_set(v___x_6428_, 0, v___x_6431_);
v___x_6433_ = v___x_6428_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v___x_6431_);
v___x_6433_ = v_reuseFailAlloc_6434_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
return v___x_6433_;
}
}
else
{
lean_object* v___x_6435_; lean_object* v___x_6436_; 
lean_del_object(v___x_6428_);
v___x_6435_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6436_ = l_Lean_Meta_isExprDefEq(v_arg_6412_, v___x_6435_, v_a_6395_, v_a_6396_, v_a_6397_, v_a_6398_);
if (lean_obj_tag(v___x_6436_) == 0)
{
lean_object* v_a_6437_; lean_object* v___x_6439_; uint8_t v_isShared_6440_; uint8_t v_isSharedCheck_6450_; 
v_a_6437_ = lean_ctor_get(v___x_6436_, 0);
v_isSharedCheck_6450_ = !lean_is_exclusive(v___x_6436_);
if (v_isSharedCheck_6450_ == 0)
{
v___x_6439_ = v___x_6436_;
v_isShared_6440_ = v_isSharedCheck_6450_;
goto v_resetjp_6438_;
}
else
{
lean_inc(v_a_6437_);
lean_dec(v___x_6436_);
v___x_6439_ = lean_box(0);
v_isShared_6440_ = v_isSharedCheck_6450_;
goto v_resetjp_6438_;
}
v_resetjp_6438_:
{
uint8_t v___x_6441_; 
v___x_6441_ = lean_unbox(v_a_6437_);
lean_dec(v_a_6437_);
if (v___x_6441_ == 0)
{
lean_object* v___x_6442_; lean_object* v___x_6444_; 
lean_dec_ref(v_arg_6415_);
v___x_6442_ = lean_box(0);
if (v_isShared_6440_ == 0)
{
lean_ctor_set(v___x_6439_, 0, v___x_6442_);
v___x_6444_ = v___x_6439_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v___x_6442_);
v___x_6444_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
return v___x_6444_;
}
}
else
{
lean_object* v___x_6446_; lean_object* v___x_6448_; 
v___x_6446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6446_, 0, v_arg_6415_);
if (v_isShared_6440_ == 0)
{
lean_ctor_set(v___x_6439_, 0, v___x_6446_);
v___x_6448_ = v___x_6439_;
goto v_reusejp_6447_;
}
else
{
lean_object* v_reuseFailAlloc_6449_; 
v_reuseFailAlloc_6449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6449_, 0, v___x_6446_);
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
else
{
lean_object* v_a_6451_; lean_object* v___x_6453_; uint8_t v_isShared_6454_; uint8_t v_isSharedCheck_6458_; 
lean_dec_ref(v_arg_6415_);
v_a_6451_ = lean_ctor_get(v___x_6436_, 0);
v_isSharedCheck_6458_ = !lean_is_exclusive(v___x_6436_);
if (v_isSharedCheck_6458_ == 0)
{
v___x_6453_ = v___x_6436_;
v_isShared_6454_ = v_isSharedCheck_6458_;
goto v_resetjp_6452_;
}
else
{
lean_inc(v_a_6451_);
lean_dec(v___x_6436_);
v___x_6453_ = lean_box(0);
v_isShared_6454_ = v_isSharedCheck_6458_;
goto v_resetjp_6452_;
}
v_resetjp_6452_:
{
lean_object* v___x_6456_; 
if (v_isShared_6454_ == 0)
{
v___x_6456_ = v___x_6453_;
goto v_reusejp_6455_;
}
else
{
lean_object* v_reuseFailAlloc_6457_; 
v_reuseFailAlloc_6457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6457_, 0, v_a_6451_);
v___x_6456_ = v_reuseFailAlloc_6457_;
goto v_reusejp_6455_;
}
v_reusejp_6455_:
{
return v___x_6456_;
}
}
}
}
}
}
else
{
lean_object* v_a_6460_; lean_object* v___x_6462_; uint8_t v_isShared_6463_; uint8_t v_isSharedCheck_6467_; 
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
v_a_6460_ = lean_ctor_get(v___x_6425_, 0);
v_isSharedCheck_6467_ = !lean_is_exclusive(v___x_6425_);
if (v_isSharedCheck_6467_ == 0)
{
v___x_6462_ = v___x_6425_;
v_isShared_6463_ = v_isSharedCheck_6467_;
goto v_resetjp_6461_;
}
else
{
lean_inc(v_a_6460_);
lean_dec(v___x_6425_);
v___x_6462_ = lean_box(0);
v_isShared_6463_ = v_isSharedCheck_6467_;
goto v_resetjp_6461_;
}
v_resetjp_6461_:
{
lean_object* v___x_6465_; 
if (v_isShared_6463_ == 0)
{
v___x_6465_ = v___x_6462_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6466_; 
v_reuseFailAlloc_6466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6466_, 0, v_a_6460_);
v___x_6465_ = v_reuseFailAlloc_6466_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
return v___x_6465_;
}
}
}
}
}
}
}
}
v___jp_6405_:
{
lean_object* v___x_6406_; lean_object* v___x_6408_; 
v___x_6406_ = lean_box(0);
if (v_isShared_6404_ == 0)
{
lean_ctor_set(v___x_6403_, 0, v___x_6406_);
v___x_6408_ = v___x_6403_;
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
lean_object* v_a_6469_; lean_object* v___x_6471_; uint8_t v_isShared_6472_; uint8_t v_isSharedCheck_6476_; 
v_a_6469_ = lean_ctor_get(v___x_6400_, 0);
v_isSharedCheck_6476_ = !lean_is_exclusive(v___x_6400_);
if (v_isSharedCheck_6476_ == 0)
{
v___x_6471_ = v___x_6400_;
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
else
{
lean_inc(v_a_6469_);
lean_dec(v___x_6400_);
v___x_6471_ = lean_box(0);
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
v_resetjp_6470_:
{
lean_object* v___x_6474_; 
if (v_isShared_6472_ == 0)
{
v___x_6474_ = v___x_6471_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
v___x_6474_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
return v___x_6474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_, lean_object* v_a_6480_, lean_object* v_a_6481_, lean_object* v_a_6482_){
_start:
{
lean_object* v_res_6483_; 
v_res_6483_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6477_, v_a_6478_, v_a_6479_, v_a_6480_, v_a_6481_);
lean_dec(v_a_6481_);
lean_dec_ref(v_a_6480_);
lean_dec(v_a_6479_);
lean_dec_ref(v_a_6478_);
return v_res_6483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6484_, lean_object* v_maxFVars_x3f_6485_, lean_object* v_k_6486_, uint8_t v_cleanupAnnotations_6487_, uint8_t v_whnfType_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_){
_start:
{
lean_object* v___f_6496_; lean_object* v___x_6497_; 
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
v___f_6496_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6496_, 0, v_k_6486_);
lean_closure_set(v___f_6496_, 1, v___y_6489_);
lean_closure_set(v___f_6496_, 2, v___y_6490_);
v___x_6497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6484_, v_maxFVars_x3f_6485_, v___f_6496_, v_cleanupAnnotations_6487_, v_whnfType_6488_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_);
if (lean_obj_tag(v___x_6497_) == 0)
{
return v___x_6497_;
}
else
{
lean_object* v_a_6498_; lean_object* v___x_6500_; uint8_t v_isShared_6501_; uint8_t v_isSharedCheck_6505_; 
v_a_6498_ = lean_ctor_get(v___x_6497_, 0);
v_isSharedCheck_6505_ = !lean_is_exclusive(v___x_6497_);
if (v_isSharedCheck_6505_ == 0)
{
v___x_6500_ = v___x_6497_;
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
else
{
lean_inc(v_a_6498_);
lean_dec(v___x_6497_);
v___x_6500_ = lean_box(0);
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
v_resetjp_6499_:
{
lean_object* v___x_6503_; 
if (v_isShared_6501_ == 0)
{
v___x_6503_ = v___x_6500_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
v___x_6503_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
return v___x_6503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6506_, lean_object* v_maxFVars_x3f_6507_, lean_object* v_k_6508_, lean_object* v_cleanupAnnotations_6509_, lean_object* v_whnfType_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6518_; uint8_t v_whnfType_boxed_6519_; lean_object* v_res_6520_; 
v_cleanupAnnotations_boxed_6518_ = lean_unbox(v_cleanupAnnotations_6509_);
v_whnfType_boxed_6519_ = lean_unbox(v_whnfType_6510_);
v_res_6520_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6506_, v_maxFVars_x3f_6507_, v_k_6508_, v_cleanupAnnotations_boxed_6518_, v_whnfType_boxed_6519_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_);
lean_dec(v___y_6516_);
lean_dec_ref(v___y_6515_);
lean_dec(v___y_6514_);
lean_dec_ref(v___y_6513_);
lean_dec(v___y_6512_);
lean_dec_ref(v___y_6511_);
return v_res_6520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6521_, lean_object* v_type_6522_, lean_object* v_maxFVars_x3f_6523_, lean_object* v_k_6524_, uint8_t v_cleanupAnnotations_6525_, uint8_t v_whnfType_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_){
_start:
{
lean_object* v___x_6534_; 
v___x_6534_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6522_, v_maxFVars_x3f_6523_, v_k_6524_, v_cleanupAnnotations_6525_, v_whnfType_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_, v___y_6531_, v___y_6532_);
return v___x_6534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6535_, lean_object* v_type_6536_, lean_object* v_maxFVars_x3f_6537_, lean_object* v_k_6538_, lean_object* v_cleanupAnnotations_6539_, lean_object* v_whnfType_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6548_; uint8_t v_whnfType_boxed_6549_; lean_object* v_res_6550_; 
v_cleanupAnnotations_boxed_6548_ = lean_unbox(v_cleanupAnnotations_6539_);
v_whnfType_boxed_6549_ = lean_unbox(v_whnfType_6540_);
v_res_6550_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6535_, v_type_6536_, v_maxFVars_x3f_6537_, v_k_6538_, v_cleanupAnnotations_boxed_6548_, v_whnfType_boxed_6549_, v___y_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_, v___y_6546_);
lean_dec(v___y_6546_);
lean_dec_ref(v___y_6545_);
lean_dec(v___y_6544_);
lean_dec_ref(v___y_6543_);
lean_dec(v___y_6542_);
lean_dec_ref(v___y_6541_);
return v_res_6550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6551_, lean_object* v_x_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v_keyedConfig_6560_; uint8_t v_trackZetaDelta_6561_; lean_object* v_zetaDeltaSet_6562_; lean_object* v_localInstances_6563_; lean_object* v_defEqCtx_x3f_6564_; lean_object* v_synthPendingDepth_6565_; lean_object* v_canUnfold_x3f_6566_; uint8_t v_univApprox_6567_; uint8_t v_inTypeClassResolution_6568_; uint8_t v_cacheInferType_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v_keyedConfig_6560_ = lean_ctor_get(v___y_6555_, 0);
v_trackZetaDelta_6561_ = lean_ctor_get_uint8(v___y_6555_, sizeof(void*)*7);
v_zetaDeltaSet_6562_ = lean_ctor_get(v___y_6555_, 1);
v_localInstances_6563_ = lean_ctor_get(v___y_6555_, 3);
v_defEqCtx_x3f_6564_ = lean_ctor_get(v___y_6555_, 4);
v_synthPendingDepth_6565_ = lean_ctor_get(v___y_6555_, 5);
v_canUnfold_x3f_6566_ = lean_ctor_get(v___y_6555_, 6);
v_univApprox_6567_ = lean_ctor_get_uint8(v___y_6555_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6568_ = lean_ctor_get_uint8(v___y_6555_, sizeof(void*)*7 + 2);
v_cacheInferType_6569_ = lean_ctor_get_uint8(v___y_6555_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_6566_);
lean_inc(v_synthPendingDepth_6565_);
lean_inc(v_defEqCtx_x3f_6564_);
lean_inc_ref(v_localInstances_6563_);
lean_inc(v_zetaDeltaSet_6562_);
lean_inc_ref(v_keyedConfig_6560_);
v___x_6570_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6570_, 0, v_keyedConfig_6560_);
lean_ctor_set(v___x_6570_, 1, v_zetaDeltaSet_6562_);
lean_ctor_set(v___x_6570_, 2, v_lctx_6551_);
lean_ctor_set(v___x_6570_, 3, v_localInstances_6563_);
lean_ctor_set(v___x_6570_, 4, v_defEqCtx_x3f_6564_);
lean_ctor_set(v___x_6570_, 5, v_synthPendingDepth_6565_);
lean_ctor_set(v___x_6570_, 6, v_canUnfold_x3f_6566_);
lean_ctor_set_uint8(v___x_6570_, sizeof(void*)*7, v_trackZetaDelta_6561_);
lean_ctor_set_uint8(v___x_6570_, sizeof(void*)*7 + 1, v_univApprox_6567_);
lean_ctor_set_uint8(v___x_6570_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6568_);
lean_ctor_set_uint8(v___x_6570_, sizeof(void*)*7 + 3, v_cacheInferType_6569_);
lean_inc(v___y_6558_);
lean_inc_ref(v___y_6557_);
lean_inc(v___y_6556_);
lean_inc(v___y_6554_);
lean_inc_ref(v___y_6553_);
v___x_6571_ = lean_apply_7(v_x_6552_, v___y_6553_, v___y_6554_, v___x_6570_, v___y_6556_, v___y_6557_, v___y_6558_, lean_box(0));
if (lean_obj_tag(v___x_6571_) == 0)
{
lean_object* v_a_6572_; lean_object* v___x_6574_; uint8_t v_isShared_6575_; uint8_t v_isSharedCheck_6579_; 
v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6579_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6579_ == 0)
{
v___x_6574_ = v___x_6571_;
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
else
{
lean_inc(v_a_6572_);
lean_dec(v___x_6571_);
v___x_6574_ = lean_box(0);
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
v_resetjp_6573_:
{
lean_object* v___x_6577_; 
if (v_isShared_6575_ == 0)
{
v___x_6577_ = v___x_6574_;
goto v_reusejp_6576_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_a_6572_);
v___x_6577_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6576_;
}
v_reusejp_6576_:
{
return v___x_6577_;
}
}
}
else
{
return v___x_6571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6580_, lean_object* v_x_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_, lean_object* v___y_6584_, lean_object* v___y_6585_, lean_object* v___y_6586_, lean_object* v___y_6587_, lean_object* v___y_6588_){
_start:
{
lean_object* v_res_6589_; 
v_res_6589_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6580_, v_x_6581_, v___y_6582_, v___y_6583_, v___y_6584_, v___y_6585_, v___y_6586_, v___y_6587_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec(v___y_6585_);
lean_dec_ref(v___y_6584_);
lean_dec(v___y_6583_);
lean_dec_ref(v___y_6582_);
return v_res_6589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6590_, lean_object* v_lctx_6591_, lean_object* v_x_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_){
_start:
{
lean_object* v___x_6600_; 
v___x_6600_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6591_, v_x_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
return v___x_6600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6601_, lean_object* v_lctx_6602_, lean_object* v_x_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_){
_start:
{
lean_object* v_res_6611_; 
v_res_6611_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6601_, v_lctx_6602_, v_x_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_);
lean_dec(v___y_6609_);
lean_dec_ref(v___y_6608_);
lean_dec(v___y_6607_);
lean_dec_ref(v___y_6606_);
lean_dec(v___y_6605_);
lean_dec_ref(v___y_6604_);
return v_res_6611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6628_, lean_object* v___x_6629_, lean_object* v_wfRel_6630_, lean_object* v_x_6631_, lean_object* v_type_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_){
_start:
{
lean_object* v___x_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; 
v___x_6640_ = lean_unsigned_to_nat(0u);
v___x_6641_ = lean_array_get_borrowed(v___x_6628_, v_x_6631_, v___x_6640_);
v___x_6642_ = l_Lean_Expr_fvarId_x21(v___x_6641_);
v___x_6643_ = l_Lean_FVarId_getUserName___redArg(v___x_6642_, v___y_6635_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6643_) == 0)
{
lean_object* v_a_6644_; lean_object* v___x_6645_; 
v_a_6644_ = lean_ctor_get(v___x_6643_, 0);
lean_inc(v_a_6644_);
lean_dec_ref_known(v___x_6643_, 1);
lean_inc(v___y_6638_);
lean_inc_ref(v___y_6637_);
lean_inc(v___y_6636_);
lean_inc_ref(v___y_6635_);
lean_inc(v___x_6641_);
v___x_6645_ = lean_infer_type(v___x_6641_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6645_) == 0)
{
lean_object* v_a_6646_; lean_object* v___x_6647_; 
v_a_6646_ = lean_ctor_get(v___x_6645_, 0);
lean_inc_n(v_a_6646_, 2);
lean_dec_ref_known(v___x_6645_, 1);
v___x_6647_ = l_Lean_Meta_getLevel(v_a_6646_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6647_) == 0)
{
lean_object* v_a_6648_; lean_object* v___x_6649_; 
v_a_6648_ = lean_ctor_get(v___x_6647_, 0);
lean_inc(v_a_6648_);
lean_dec_ref_known(v___x_6647_, 1);
lean_inc_ref(v_type_6632_);
v___x_6649_ = l_Lean_Meta_getLevel(v_type_6632_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6649_) == 0)
{
lean_object* v_a_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; uint8_t v___x_6653_; uint8_t v___x_6654_; uint8_t v___x_6655_; lean_object* v___x_6656_; 
v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
lean_inc(v_a_6650_);
lean_dec_ref_known(v___x_6649_, 1);
v___x_6651_ = lean_mk_empty_array_with_capacity(v___x_6629_);
lean_inc(v___x_6641_);
lean_inc_ref(v___x_6651_);
v___x_6652_ = lean_array_push(v___x_6651_, v___x_6641_);
v___x_6653_ = 0;
v___x_6654_ = 1;
v___x_6655_ = 1;
v___x_6656_ = l_Lean_Meta_mkLambdaFVars(v___x_6652_, v_type_6632_, v___x_6653_, v___x_6654_, v___x_6653_, v___x_6654_, v___x_6655_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
lean_dec_ref(v___x_6652_);
if (lean_obj_tag(v___x_6656_) == 0)
{
lean_object* v_a_6657_; lean_object* v___x_6658_; 
v_a_6657_ = lean_ctor_get(v___x_6656_, 0);
lean_inc(v_a_6657_);
lean_dec_ref_known(v___x_6656_, 1);
lean_inc_ref(v_wfRel_6630_);
v___x_6658_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6630_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6658_) == 0)
{
lean_object* v_a_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6703_; 
v_a_6659_ = lean_ctor_get(v___x_6658_, 0);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6658_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6661_ = v___x_6658_;
v_isShared_6662_ = v_isSharedCheck_6703_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_a_6659_);
lean_dec(v___x_6658_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6703_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
if (lean_obj_tag(v_a_6659_) == 1)
{
lean_object* v_val_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6672_; 
lean_dec_ref(v___x_6651_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_val_6663_ = lean_ctor_get(v_a_6659_, 0);
lean_inc(v_val_6663_);
lean_dec_ref_known(v_a_6659_, 1);
v___x_6664_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6665_ = lean_box(0);
v___x_6666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6666_, 0, v_a_6650_);
lean_ctor_set(v___x_6666_, 1, v___x_6665_);
v___x_6667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6667_, 0, v_a_6648_);
lean_ctor_set(v___x_6667_, 1, v___x_6666_);
v___x_6668_ = l_Lean_mkConst(v___x_6664_, v___x_6667_);
v___x_6669_ = l_Lean_mkApp3(v___x_6668_, v_a_6646_, v_a_6657_, v_val_6663_);
v___x_6670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6670_, 0, v___x_6669_);
lean_ctor_set(v___x_6670_, 1, v_a_6644_);
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 0, v___x_6670_);
v___x_6672_ = v___x_6661_;
goto v_reusejp_6671_;
}
else
{
lean_object* v_reuseFailAlloc_6673_; 
v_reuseFailAlloc_6673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6673_, 0, v___x_6670_);
v___x_6672_ = v_reuseFailAlloc_6673_;
goto v_reusejp_6671_;
}
v_reusejp_6671_:
{
return v___x_6672_;
}
}
else
{
lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; 
lean_del_object(v___x_6661_);
lean_dec(v_a_6659_);
v___x_6674_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6630_);
v___x_6675_ = l_Lean_mkProj(v___x_6674_, v___x_6640_, v_wfRel_6630_);
v___x_6676_ = l_Lean_mkProj(v___x_6674_, v___x_6629_, v_wfRel_6630_);
v___x_6677_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6678_ = lean_array_push(v___x_6651_, v___x_6676_);
v___x_6679_ = l_Lean_Meta_mkAppM(v___x_6677_, v___x_6678_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6679_) == 0)
{
lean_object* v_a_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6694_; 
v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
v_isSharedCheck_6694_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6694_ == 0)
{
v___x_6682_ = v___x_6679_;
v_isShared_6683_ = v_isSharedCheck_6694_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_a_6680_);
lean_dec(v___x_6679_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6694_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6692_; 
v___x_6684_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6685_ = lean_box(0);
v___x_6686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6686_, 0, v_a_6650_);
lean_ctor_set(v___x_6686_, 1, v___x_6685_);
v___x_6687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6687_, 0, v_a_6648_);
lean_ctor_set(v___x_6687_, 1, v___x_6686_);
v___x_6688_ = l_Lean_mkConst(v___x_6684_, v___x_6687_);
v___x_6689_ = l_Lean_mkApp4(v___x_6688_, v_a_6646_, v_a_6657_, v___x_6675_, v_a_6680_);
v___x_6690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6690_, 0, v___x_6689_);
lean_ctor_set(v___x_6690_, 1, v_a_6644_);
if (v_isShared_6683_ == 0)
{
lean_ctor_set(v___x_6682_, 0, v___x_6690_);
v___x_6692_ = v___x_6682_;
goto v_reusejp_6691_;
}
else
{
lean_object* v_reuseFailAlloc_6693_; 
v_reuseFailAlloc_6693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6693_, 0, v___x_6690_);
v___x_6692_ = v_reuseFailAlloc_6693_;
goto v_reusejp_6691_;
}
v_reusejp_6691_:
{
return v___x_6692_;
}
}
}
else
{
lean_object* v_a_6695_; lean_object* v___x_6697_; uint8_t v_isShared_6698_; uint8_t v_isSharedCheck_6702_; 
lean_dec_ref(v___x_6675_);
lean_dec(v_a_6657_);
lean_dec(v_a_6650_);
lean_dec(v_a_6648_);
lean_dec(v_a_6646_);
lean_dec(v_a_6644_);
v_a_6695_ = lean_ctor_get(v___x_6679_, 0);
v_isSharedCheck_6702_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6702_ == 0)
{
v___x_6697_ = v___x_6679_;
v_isShared_6698_ = v_isSharedCheck_6702_;
goto v_resetjp_6696_;
}
else
{
lean_inc(v_a_6695_);
lean_dec(v___x_6679_);
v___x_6697_ = lean_box(0);
v_isShared_6698_ = v_isSharedCheck_6702_;
goto v_resetjp_6696_;
}
v_resetjp_6696_:
{
lean_object* v___x_6700_; 
if (v_isShared_6698_ == 0)
{
v___x_6700_ = v___x_6697_;
goto v_reusejp_6699_;
}
else
{
lean_object* v_reuseFailAlloc_6701_; 
v_reuseFailAlloc_6701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_a_6695_);
v___x_6700_ = v_reuseFailAlloc_6701_;
goto v_reusejp_6699_;
}
v_reusejp_6699_:
{
return v___x_6700_;
}
}
}
}
}
}
else
{
lean_object* v_a_6704_; lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6711_; 
lean_dec(v_a_6657_);
lean_dec_ref(v___x_6651_);
lean_dec(v_a_6650_);
lean_dec(v_a_6648_);
lean_dec(v_a_6646_);
lean_dec(v_a_6644_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6704_ = lean_ctor_get(v___x_6658_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v___x_6658_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6706_ = v___x_6658_;
v_isShared_6707_ = v_isSharedCheck_6711_;
goto v_resetjp_6705_;
}
else
{
lean_inc(v_a_6704_);
lean_dec(v___x_6658_);
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
else
{
lean_object* v_a_6712_; lean_object* v___x_6714_; uint8_t v_isShared_6715_; uint8_t v_isSharedCheck_6719_; 
lean_dec_ref(v___x_6651_);
lean_dec(v_a_6650_);
lean_dec(v_a_6648_);
lean_dec(v_a_6646_);
lean_dec(v_a_6644_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6712_ = lean_ctor_get(v___x_6656_, 0);
v_isSharedCheck_6719_ = !lean_is_exclusive(v___x_6656_);
if (v_isSharedCheck_6719_ == 0)
{
v___x_6714_ = v___x_6656_;
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
else
{
lean_inc(v_a_6712_);
lean_dec(v___x_6656_);
v___x_6714_ = lean_box(0);
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
v_resetjp_6713_:
{
lean_object* v___x_6717_; 
if (v_isShared_6715_ == 0)
{
v___x_6717_ = v___x_6714_;
goto v_reusejp_6716_;
}
else
{
lean_object* v_reuseFailAlloc_6718_; 
v_reuseFailAlloc_6718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_a_6712_);
v___x_6717_ = v_reuseFailAlloc_6718_;
goto v_reusejp_6716_;
}
v_reusejp_6716_:
{
return v___x_6717_;
}
}
}
}
else
{
lean_object* v_a_6720_; lean_object* v___x_6722_; uint8_t v_isShared_6723_; uint8_t v_isSharedCheck_6727_; 
lean_dec(v_a_6648_);
lean_dec(v_a_6646_);
lean_dec(v_a_6644_);
lean_dec_ref(v_type_6632_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6720_ = lean_ctor_get(v___x_6649_, 0);
v_isSharedCheck_6727_ = !lean_is_exclusive(v___x_6649_);
if (v_isSharedCheck_6727_ == 0)
{
v___x_6722_ = v___x_6649_;
v_isShared_6723_ = v_isSharedCheck_6727_;
goto v_resetjp_6721_;
}
else
{
lean_inc(v_a_6720_);
lean_dec(v___x_6649_);
v___x_6722_ = lean_box(0);
v_isShared_6723_ = v_isSharedCheck_6727_;
goto v_resetjp_6721_;
}
v_resetjp_6721_:
{
lean_object* v___x_6725_; 
if (v_isShared_6723_ == 0)
{
v___x_6725_ = v___x_6722_;
goto v_reusejp_6724_;
}
else
{
lean_object* v_reuseFailAlloc_6726_; 
v_reuseFailAlloc_6726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6726_, 0, v_a_6720_);
v___x_6725_ = v_reuseFailAlloc_6726_;
goto v_reusejp_6724_;
}
v_reusejp_6724_:
{
return v___x_6725_;
}
}
}
}
else
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
lean_dec(v_a_6646_);
lean_dec(v_a_6644_);
lean_dec_ref(v_type_6632_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6728_ = lean_ctor_get(v___x_6647_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6647_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6647_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6647_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
v___x_6733_ = v___x_6730_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_a_6728_);
v___x_6733_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
return v___x_6733_;
}
}
}
}
else
{
lean_object* v_a_6736_; lean_object* v___x_6738_; uint8_t v_isShared_6739_; uint8_t v_isSharedCheck_6743_; 
lean_dec(v_a_6644_);
lean_dec_ref(v_type_6632_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6736_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6743_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6743_ == 0)
{
v___x_6738_ = v___x_6645_;
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
else
{
lean_inc(v_a_6736_);
lean_dec(v___x_6645_);
v___x_6738_ = lean_box(0);
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
v_resetjp_6737_:
{
lean_object* v___x_6741_; 
if (v_isShared_6739_ == 0)
{
v___x_6741_ = v___x_6738_;
goto v_reusejp_6740_;
}
else
{
lean_object* v_reuseFailAlloc_6742_; 
v_reuseFailAlloc_6742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6736_);
v___x_6741_ = v_reuseFailAlloc_6742_;
goto v_reusejp_6740_;
}
v_reusejp_6740_:
{
return v___x_6741_;
}
}
}
}
else
{
lean_object* v_a_6744_; lean_object* v___x_6746_; uint8_t v_isShared_6747_; uint8_t v_isSharedCheck_6751_; 
lean_dec_ref(v_type_6632_);
lean_dec_ref(v_wfRel_6630_);
lean_dec(v___x_6629_);
v_a_6744_ = lean_ctor_get(v___x_6643_, 0);
v_isSharedCheck_6751_ = !lean_is_exclusive(v___x_6643_);
if (v_isSharedCheck_6751_ == 0)
{
v___x_6746_ = v___x_6643_;
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
else
{
lean_inc(v_a_6744_);
lean_dec(v___x_6643_);
v___x_6746_ = lean_box(0);
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
v_resetjp_6745_:
{
lean_object* v___x_6749_; 
if (v_isShared_6747_ == 0)
{
v___x_6749_ = v___x_6746_;
goto v_reusejp_6748_;
}
else
{
lean_object* v_reuseFailAlloc_6750_; 
v_reuseFailAlloc_6750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6744_);
v___x_6749_ = v_reuseFailAlloc_6750_;
goto v_reusejp_6748_;
}
v_reusejp_6748_:
{
return v___x_6749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6752_, lean_object* v___x_6753_, lean_object* v_wfRel_6754_, lean_object* v_x_6755_, lean_object* v_type_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_){
_start:
{
lean_object* v_res_6764_; 
v_res_6764_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6752_, v___x_6753_, v_wfRel_6754_, v_x_6755_, v_type_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
lean_dec(v___y_6762_);
lean_dec_ref(v___y_6761_);
lean_dec(v___y_6760_);
lean_dec_ref(v___y_6759_);
lean_dec(v___y_6758_);
lean_dec_ref(v___y_6757_);
lean_dec_ref(v_x_6755_);
lean_dec_ref(v___x_6752_);
return v_res_6764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6765_, lean_object* v_declName_6766_, lean_object* v_x_6767_, lean_object* v_F_6768_, lean_object* v_val_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_){
_start:
{
lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; 
v___x_6777_ = lean_array_get_size(v_prefixArgs_6765_);
v___x_6778_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6778_, 0, v_declName_6766_);
lean_closure_set(v___x_6778_, 1, v___x_6777_);
v___x_6779_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6767_, v_F_6768_, v_val_6769_, v___x_6778_, v___y_6770_, v___y_6771_, v___y_6772_, v___y_6773_, v___y_6774_, v___y_6775_);
return v___x_6779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6780_, lean_object* v_declName_6781_, lean_object* v_x_6782_, lean_object* v_F_6783_, lean_object* v_val_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_){
_start:
{
lean_object* v_res_6792_; 
v_res_6792_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6780_, v_declName_6781_, v_x_6782_, v_F_6783_, v_val_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_);
lean_dec(v___y_6790_);
lean_dec_ref(v___y_6789_);
lean_dec(v___y_6788_);
lean_dec_ref(v___y_6787_);
lean_dec(v___y_6786_);
lean_dec_ref(v___y_6785_);
lean_dec_ref(v_prefixArgs_6780_);
return v_res_6792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6793_, lean_object* v___x_6794_, lean_object* v___x_6795_, lean_object* v___f_6796_, lean_object* v_funNames_6797_, lean_object* v_argsPacker_6798_, lean_object* v_decrTactics_6799_, uint8_t v___x_6800_, lean_object* v_fst_6801_, lean_object* v_prefixArgs_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_){
_start:
{
lean_object* v___x_6810_; 
lean_inc_ref(v___x_6794_);
lean_inc_ref(v___x_6793_);
v___x_6810_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6793_, v___x_6794_, v___x_6795_, v___f_6796_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
if (lean_obj_tag(v___x_6810_) == 0)
{
lean_object* v_a_6811_; lean_object* v___x_6812_; 
v_a_6811_ = lean_ctor_get(v___x_6810_, 0);
lean_inc(v_a_6811_);
lean_dec_ref_known(v___x_6810_, 1);
v___x_6812_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6797_, v_argsPacker_6798_, v_decrTactics_6799_, v_a_6811_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
if (lean_obj_tag(v___x_6812_) == 0)
{
lean_object* v_a_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6817_; uint8_t v___x_6818_; uint8_t v___x_6819_; lean_object* v___x_6820_; 
v_a_6813_ = lean_ctor_get(v___x_6812_, 0);
lean_inc(v_a_6813_);
lean_dec_ref_known(v___x_6812_, 1);
v___x_6814_ = lean_unsigned_to_nat(2u);
v___x_6815_ = lean_mk_empty_array_with_capacity(v___x_6814_);
v___x_6816_ = lean_array_push(v___x_6815_, v___x_6793_);
v___x_6817_ = lean_array_push(v___x_6816_, v___x_6794_);
v___x_6818_ = 1;
v___x_6819_ = 1;
v___x_6820_ = l_Lean_Meta_mkLambdaFVars(v___x_6817_, v_a_6813_, v___x_6800_, v___x_6818_, v___x_6800_, v___x_6818_, v___x_6819_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
lean_dec_ref(v___x_6817_);
if (lean_obj_tag(v___x_6820_) == 0)
{
lean_object* v_a_6821_; lean_object* v___x_6822_; lean_object* v___x_6823_; 
v_a_6821_ = lean_ctor_get(v___x_6820_, 0);
lean_inc(v_a_6821_);
lean_dec_ref_known(v___x_6820_, 1);
v___x_6822_ = l_Lean_Expr_app___override(v_fst_6801_, v_a_6821_);
v___x_6823_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6802_, v___x_6822_, v___x_6800_, v___x_6818_, v___x_6800_, v___x_6818_, v___x_6819_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
return v___x_6823_;
}
else
{
lean_dec_ref(v_fst_6801_);
return v___x_6820_;
}
}
else
{
lean_dec_ref(v_fst_6801_);
lean_dec_ref(v___x_6794_);
lean_dec_ref(v___x_6793_);
return v___x_6812_;
}
}
else
{
lean_dec_ref(v_fst_6801_);
lean_dec_ref(v_decrTactics_6799_);
lean_dec_ref(v_argsPacker_6798_);
lean_dec_ref(v_funNames_6797_);
lean_dec_ref(v___x_6794_);
lean_dec_ref(v___x_6793_);
return v___x_6810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6824_ = _args[0];
lean_object* v___x_6825_ = _args[1];
lean_object* v___x_6826_ = _args[2];
lean_object* v___f_6827_ = _args[3];
lean_object* v_funNames_6828_ = _args[4];
lean_object* v_argsPacker_6829_ = _args[5];
lean_object* v_decrTactics_6830_ = _args[6];
lean_object* v___x_6831_ = _args[7];
lean_object* v_fst_6832_ = _args[8];
lean_object* v_prefixArgs_6833_ = _args[9];
lean_object* v___y_6834_ = _args[10];
lean_object* v___y_6835_ = _args[11];
lean_object* v___y_6836_ = _args[12];
lean_object* v___y_6837_ = _args[13];
lean_object* v___y_6838_ = _args[14];
lean_object* v___y_6839_ = _args[15];
lean_object* v___y_6840_ = _args[16];
_start:
{
uint8_t v___x_5940__boxed_6841_; lean_object* v_res_6842_; 
v___x_5940__boxed_6841_ = lean_unbox(v___x_6831_);
v_res_6842_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6824_, v___x_6825_, v___x_6826_, v___f_6827_, v_funNames_6828_, v_argsPacker_6829_, v_decrTactics_6830_, v___x_5940__boxed_6841_, v_fst_6832_, v_prefixArgs_6833_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_, v___y_6838_, v___y_6839_);
lean_dec(v___y_6839_);
lean_dec_ref(v___y_6838_);
lean_dec(v___y_6837_);
lean_dec_ref(v___y_6836_);
lean_dec(v___y_6835_);
lean_dec_ref(v___y_6834_);
lean_dec_ref(v_prefixArgs_6833_);
return v_res_6842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6843_, lean_object* v_snd_6844_, lean_object* v___x_6845_, lean_object* v_prefixArgs_6846_, lean_object* v_value_6847_, lean_object* v___f_6848_, lean_object* v_funNames_6849_, lean_object* v_argsPacker_6850_, lean_object* v_decrTactics_6851_, uint8_t v___x_6852_, lean_object* v_fst_6853_, lean_object* v_xs_6854_, lean_object* v_x_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_){
_start:
{
lean_object* v_lctx_6863_; lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; lean_object* v___x_6867_; lean_object* v___x_6868_; lean_object* v___x_6869_; lean_object* v___x_6870_; lean_object* v___x_6871_; lean_object* v___f_6872_; lean_object* v___x_6873_; 
v_lctx_6863_ = lean_ctor_get(v___y_6858_, 2);
v___x_6864_ = lean_unsigned_to_nat(0u);
v___x_6865_ = lean_array_get_borrowed(v___x_6843_, v_xs_6854_, v___x_6864_);
v___x_6866_ = l_Lean_Expr_fvarId_x21(v___x_6865_);
lean_inc_ref(v_lctx_6863_);
v___x_6867_ = l_Lean_LocalContext_setUserName(v_lctx_6863_, v___x_6866_, v_snd_6844_);
v___x_6868_ = lean_array_get_borrowed(v___x_6843_, v_xs_6854_, v___x_6845_);
lean_inc_n(v___x_6865_, 2);
lean_inc_ref(v_prefixArgs_6846_);
v___x_6869_ = lean_array_push(v_prefixArgs_6846_, v___x_6865_);
v___x_6870_ = l_Lean_Expr_beta(v_value_6847_, v___x_6869_);
v___x_6871_ = lean_box(v___x_6852_);
lean_inc(v___x_6868_);
v___f_6872_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6872_, 0, v___x_6865_);
lean_closure_set(v___f_6872_, 1, v___x_6868_);
lean_closure_set(v___f_6872_, 2, v___x_6870_);
lean_closure_set(v___f_6872_, 3, v___f_6848_);
lean_closure_set(v___f_6872_, 4, v_funNames_6849_);
lean_closure_set(v___f_6872_, 5, v_argsPacker_6850_);
lean_closure_set(v___f_6872_, 6, v_decrTactics_6851_);
lean_closure_set(v___f_6872_, 7, v___x_6871_);
lean_closure_set(v___f_6872_, 8, v_fst_6853_);
lean_closure_set(v___f_6872_, 9, v_prefixArgs_6846_);
v___x_6873_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6867_, v___f_6872_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_);
return v___x_6873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6874_ = _args[0];
lean_object* v_snd_6875_ = _args[1];
lean_object* v___x_6876_ = _args[2];
lean_object* v_prefixArgs_6877_ = _args[3];
lean_object* v_value_6878_ = _args[4];
lean_object* v___f_6879_ = _args[5];
lean_object* v_funNames_6880_ = _args[6];
lean_object* v_argsPacker_6881_ = _args[7];
lean_object* v_decrTactics_6882_ = _args[8];
lean_object* v___x_6883_ = _args[9];
lean_object* v_fst_6884_ = _args[10];
lean_object* v_xs_6885_ = _args[11];
lean_object* v_x_6886_ = _args[12];
lean_object* v___y_6887_ = _args[13];
lean_object* v___y_6888_ = _args[14];
lean_object* v___y_6889_ = _args[15];
lean_object* v___y_6890_ = _args[16];
lean_object* v___y_6891_ = _args[17];
lean_object* v___y_6892_ = _args[18];
lean_object* v___y_6893_ = _args[19];
_start:
{
uint8_t v___x_6010__boxed_6894_; lean_object* v_res_6895_; 
v___x_6010__boxed_6894_ = lean_unbox(v___x_6883_);
v_res_6895_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6874_, v_snd_6875_, v___x_6876_, v_prefixArgs_6877_, v_value_6878_, v___f_6879_, v_funNames_6880_, v_argsPacker_6881_, v_decrTactics_6882_, v___x_6010__boxed_6894_, v_fst_6884_, v_xs_6885_, v_x_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
lean_dec(v___y_6892_);
lean_dec_ref(v___y_6891_);
lean_dec(v___y_6890_);
lean_dec_ref(v___y_6889_);
lean_dec(v___y_6888_);
lean_dec_ref(v___y_6887_);
lean_dec_ref(v_x_6886_);
lean_dec_ref(v_xs_6885_);
lean_dec(v___x_6876_);
lean_dec_ref(v___x_6874_);
return v_res_6895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6900_, lean_object* v_prefixArgs_6901_, lean_object* v_argsPacker_6902_, lean_object* v_wfRel_6903_, lean_object* v_funNames_6904_, lean_object* v_decrTactics_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_){
_start:
{
lean_object* v_declName_6913_; lean_object* v_type_6914_; lean_object* v_value_6915_; lean_object* v___x_6916_; 
v_declName_6913_ = lean_ctor_get(v_preDef_6900_, 3);
lean_inc(v_declName_6913_);
v_type_6914_ = lean_ctor_get(v_preDef_6900_, 6);
lean_inc_ref(v_type_6914_);
v_value_6915_ = lean_ctor_get(v_preDef_6900_, 7);
lean_inc_ref(v_value_6915_);
lean_dec_ref(v_preDef_6900_);
v___x_6916_ = l_Lean_Meta_instantiateForall(v_type_6914_, v_prefixArgs_6901_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_);
if (lean_obj_tag(v___x_6916_) == 0)
{
lean_object* v_a_6917_; lean_object* v___x_6918_; lean_object* v___x_6919_; lean_object* v___f_6920_; lean_object* v___x_6921_; uint8_t v___x_6922_; lean_object* v___x_6923_; 
v_a_6917_ = lean_ctor_get(v___x_6916_, 0);
lean_inc(v_a_6917_);
lean_dec_ref_known(v___x_6916_, 1);
v___x_6918_ = l_Lean_instInhabitedExpr;
v___x_6919_ = lean_unsigned_to_nat(1u);
v___f_6920_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6920_, 0, v___x_6918_);
lean_closure_set(v___f_6920_, 1, v___x_6919_);
lean_closure_set(v___f_6920_, 2, v_wfRel_6903_);
v___x_6921_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6922_ = 0;
v___x_6923_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6917_, v___x_6921_, v___f_6920_, v___x_6922_, v___x_6922_, v_a_6906_, v_a_6907_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_);
if (lean_obj_tag(v___x_6923_) == 0)
{
lean_object* v_a_6924_; lean_object* v_fst_6925_; lean_object* v_snd_6926_; lean_object* v___x_6927_; 
v_a_6924_ = lean_ctor_get(v___x_6923_, 0);
lean_inc(v_a_6924_);
lean_dec_ref_known(v___x_6923_, 1);
v_fst_6925_ = lean_ctor_get(v_a_6924_, 0);
lean_inc_n(v_fst_6925_, 2);
v_snd_6926_ = lean_ctor_get(v_a_6924_, 1);
lean_inc(v_snd_6926_);
lean_dec(v_a_6924_);
lean_inc(v_a_6911_);
lean_inc_ref(v_a_6910_);
lean_inc(v_a_6909_);
lean_inc_ref(v_a_6908_);
v___x_6927_ = lean_infer_type(v_fst_6925_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_);
if (lean_obj_tag(v___x_6927_) == 0)
{
lean_object* v_a_6928_; lean_object* v___x_6929_; 
v_a_6928_ = lean_ctor_get(v___x_6927_, 0);
lean_inc(v_a_6928_);
lean_dec_ref_known(v___x_6927_, 1);
lean_inc(v_a_6911_);
lean_inc_ref(v_a_6910_);
lean_inc(v_a_6909_);
lean_inc_ref(v_a_6908_);
v___x_6929_ = lean_whnf(v_a_6928_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_);
if (lean_obj_tag(v___x_6929_) == 0)
{
lean_object* v_a_6930_; lean_object* v___f_6931_; lean_object* v___x_6932_; lean_object* v___f_6933_; lean_object* v___x_6934_; lean_object* v___x_6935_; lean_object* v___x_6936_; 
v_a_6930_ = lean_ctor_get(v___x_6929_, 0);
lean_inc(v_a_6930_);
lean_dec_ref_known(v___x_6929_, 1);
lean_inc_ref(v_prefixArgs_6901_);
v___f_6931_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6931_, 0, v_prefixArgs_6901_);
lean_closure_set(v___f_6931_, 1, v_declName_6913_);
v___x_6932_ = lean_box(v___x_6922_);
v___f_6933_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6933_, 0, v___x_6918_);
lean_closure_set(v___f_6933_, 1, v_snd_6926_);
lean_closure_set(v___f_6933_, 2, v___x_6919_);
lean_closure_set(v___f_6933_, 3, v_prefixArgs_6901_);
lean_closure_set(v___f_6933_, 4, v_value_6915_);
lean_closure_set(v___f_6933_, 5, v___f_6931_);
lean_closure_set(v___f_6933_, 6, v_funNames_6904_);
lean_closure_set(v___f_6933_, 7, v_argsPacker_6902_);
lean_closure_set(v___f_6933_, 8, v_decrTactics_6905_);
lean_closure_set(v___f_6933_, 9, v___x_6932_);
lean_closure_set(v___f_6933_, 10, v_fst_6925_);
v___x_6934_ = l_Lean_Expr_bindingDomain_x21(v_a_6930_);
lean_dec(v_a_6930_);
v___x_6935_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6936_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6934_, v___x_6935_, v___f_6933_, v___x_6922_, v___x_6922_, v_a_6906_, v_a_6907_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_);
return v___x_6936_;
}
else
{
lean_dec(v_snd_6926_);
lean_dec(v_fst_6925_);
lean_dec_ref(v_value_6915_);
lean_dec(v_declName_6913_);
lean_dec_ref(v_decrTactics_6905_);
lean_dec_ref(v_funNames_6904_);
lean_dec_ref(v_argsPacker_6902_);
lean_dec_ref(v_prefixArgs_6901_);
return v___x_6929_;
}
}
else
{
lean_dec(v_snd_6926_);
lean_dec(v_fst_6925_);
lean_dec_ref(v_value_6915_);
lean_dec(v_declName_6913_);
lean_dec_ref(v_decrTactics_6905_);
lean_dec_ref(v_funNames_6904_);
lean_dec_ref(v_argsPacker_6902_);
lean_dec_ref(v_prefixArgs_6901_);
return v___x_6927_;
}
}
else
{
lean_object* v_a_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6944_; 
lean_dec_ref(v_value_6915_);
lean_dec(v_declName_6913_);
lean_dec_ref(v_decrTactics_6905_);
lean_dec_ref(v_funNames_6904_);
lean_dec_ref(v_argsPacker_6902_);
lean_dec_ref(v_prefixArgs_6901_);
v_a_6937_ = lean_ctor_get(v___x_6923_, 0);
v_isSharedCheck_6944_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6944_ == 0)
{
v___x_6939_ = v___x_6923_;
v_isShared_6940_ = v_isSharedCheck_6944_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_a_6937_);
lean_dec(v___x_6923_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6944_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
lean_object* v___x_6942_; 
if (v_isShared_6940_ == 0)
{
v___x_6942_ = v___x_6939_;
goto v_reusejp_6941_;
}
else
{
lean_object* v_reuseFailAlloc_6943_; 
v_reuseFailAlloc_6943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6943_, 0, v_a_6937_);
v___x_6942_ = v_reuseFailAlloc_6943_;
goto v_reusejp_6941_;
}
v_reusejp_6941_:
{
return v___x_6942_;
}
}
}
}
else
{
lean_dec_ref(v_value_6915_);
lean_dec(v_declName_6913_);
lean_dec_ref(v_decrTactics_6905_);
lean_dec_ref(v_funNames_6904_);
lean_dec_ref(v_wfRel_6903_);
lean_dec_ref(v_argsPacker_6902_);
lean_dec_ref(v_prefixArgs_6901_);
return v___x_6916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6945_, lean_object* v_prefixArgs_6946_, lean_object* v_argsPacker_6947_, lean_object* v_wfRel_6948_, lean_object* v_funNames_6949_, lean_object* v_decrTactics_6950_, lean_object* v_a_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_, lean_object* v_a_6954_, lean_object* v_a_6955_, lean_object* v_a_6956_, lean_object* v_a_6957_){
_start:
{
lean_object* v_res_6958_; 
v_res_6958_ = l_Lean_Elab_WF_mkFix(v_preDef_6945_, v_prefixArgs_6946_, v_argsPacker_6947_, v_wfRel_6948_, v_funNames_6949_, v_decrTactics_6950_, v_a_6951_, v_a_6952_, v_a_6953_, v_a_6954_, v_a_6955_, v_a_6956_);
lean_dec(v_a_6956_);
lean_dec_ref(v_a_6955_);
lean_dec(v_a_6954_);
lean_dec_ref(v_a_6953_);
lean_dec(v_a_6952_);
lean_dec_ref(v_a_6951_);
return v_res_6958_;
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
