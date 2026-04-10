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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_assignSubsumed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_assignSubsumed___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_assignSubsumed___closed__0 = (const lean_object*)&l_Lean_Elab_WF_assignSubsumed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_78_);
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
lean_dec_ref(v___y_196_);
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
lean_dec_ref(v___x_635_);
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
lean_dec_ref(v___x_645_);
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
lean_dec_ref(v___x_562_);
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
lean_dec_ref(v___x_564_);
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
lean_dec_ref(v___x_572_);
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
lean_dec_ref(v___x_836_);
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
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_58733__overap_1076_; lean_object* v___x_1077_; 
v___x_1072_ = l_StateRefT_x27_instMonad___redArg(v___x_1071_);
v___x_1073_ = l_StateRefT_x27_instMonad___redArg(v___x_1072_);
v___x_1074_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1075_ = l_instInhabitedOfMonad___redArg(v___x_1073_, v___x_1074_);
v___x_58733__overap_1076_ = lean_panic_fn_borrowed(v___x_1075_, v_msg_989_);
lean_dec(v___x_1075_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc(v___y_990_);
v___x_1077_ = lean_apply_9(v___x_58733__overap_1076_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
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
lean_dec_ref(v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v_bs_x27_1134_ = lean_array_uset(v_bs_1118_, v_i_1117_, v___x_1133_);
if (lean_obj_tag(v_a_1132_) == 6)
{
lean_object* v_val_1141_; lean_object* v_numFields_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; 
v_val_1141_ = lean_ctor_get(v_a_1132_, 0);
lean_inc_ref(v_val_1141_);
lean_dec_ref(v_a_1132_);
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
lean_dec_ref(v___x_1146_);
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
lean_dec_ref(v___x_1206_);
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
lean_dec_ref(v___x_1420_);
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
lean_dec_ref(v___x_1524_);
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
lean_dec_ref(v___x_1720_);
if (lean_obj_tag(v_val_1722_) == 1)
{
uint8_t v_v_1723_; 
v_v_1723_ = lean_ctor_get_uint8(v_val_1722_, 0);
lean_dec_ref(v_val_1722_);
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
lean_dec_ref(v___x_1762_);
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
lean_dec_ref(v___x_1801_);
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
lean_dec_ref(v___x_1860_);
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
lean_dec_ref(v___x_1924_);
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
lean_dec_ref(v___x_1927_);
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
lean_dec_ref(v___x_1929_);
v___x_1931_ = l_Lean_Expr_bindingDomain_x21(v_a_1930_);
lean_dec(v_a_1930_);
v___x_1932_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1931_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v_lower_1936_; lean_object* v_upper_1937_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
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
lean_dec_ref(v___x_1973_);
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
lean_dec_ref(v___x_1911_);
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
lean_dec_ref(v_x_1985_);
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
lean_dec_ref(v___x_2003_);
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
lean_dec_ref(v___x_2073_);
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
uint8_t v___x_67130__boxed_2115_; lean_object* v_res_2116_; 
v___x_67130__boxed_2115_ = lean_unbox(v___x_2100_);
v_res_2116_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2096_, v_b_2097_, v_recFnName_2098_, v_fixedPrefixSize_2099_, v___x_67130__boxed_2115_, v___x_2101_, v_a_2102_, v_e_2103_, v_xs_2104_, v_altBody_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
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
lean_dec_ref(v___x_2147_);
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
lean_dec_ref(v_e_2163_);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2177_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_binderType_2174_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___f_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
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
lean_dec_ref(v_e_2163_);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2186_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_binderType_2183_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
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
lean_dec_ref(v_e_2163_);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2196_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_type_2192_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2196_);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2198_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_value_2193_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___f_2200_; uint8_t v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
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
lean_dec_ref(v_e_2163_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v_fileName_2208_; lean_object* v_fileMap_2209_; lean_object* v_options_2210_; lean_object* v_currRecDepth_2211_; lean_object* v_maxRecDepth_2212_; lean_object* v_ref_2213_; lean_object* v_currNamespace_2214_; lean_object* v_openDecls_2215_; lean_object* v_initHeartbeats_2216_; lean_object* v_maxHeartbeats_2217_; lean_object* v_quotContext_2218_; lean_object* v_currMacroScope_2219_; uint8_t v_diag_2220_; lean_object* v_cancelTk_x3f_2221_; uint8_t v_suppressElabErrors_2222_; lean_object* v_inheritedTraceOptions_2223_; lean_object* v_ref_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_data_2204_);
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref(v___x_2206_);
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
lean_dec_ref(v___x_2225_);
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
lean_dec_ref(v_e_2163_);
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
lean_dec_ref(v___x_2254_);
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
lean_dec_ref(v_a_2255_);
lean_inc_ref(v_F_2162_);
v___x_2258_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2257_, v_F_2162_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_val_2260_; lean_object* v_toMatcherInfo_2261_; lean_object* v_matcherName_2262_; lean_object* v_matcherLevels_2263_; lean_object* v_params_2264_; lean_object* v_motive_2265_; lean_object* v_discrs_2266_; lean_object* v_alts_2267_; lean_object* v_remaining_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_val_2260_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_val_2260_);
lean_dec_ref(v_a_2259_);
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
lean_dec_ref(v___x_2272_);
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
lean_dec_ref(v_e_2163_);
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
lean_dec_ref(v_e_2163_);
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
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0(void){
_start:
{
uint8_t v___x_2340_; uint64_t v___x_2341_; 
v___x_2340_ = 0;
v___x_2341_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2342_, lean_object* v_fixedPrefixSize_2343_, lean_object* v_F_2344_, lean_object* v_e_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___x_2355_; 
lean_inc_ref(v_e_2345_);
lean_inc(v_recFnName_2342_);
v___x_2355_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2342_, v_e_2345_, v_a_2346_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2494_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2494_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2494_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_unbox(v_a_2356_);
lean_dec(v_a_2356_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2362_; 
lean_dec_ref(v_F_2344_);
lean_dec(v_fixedPrefixSize_2343_);
lean_dec(v_recFnName_2342_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v_e_2345_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_e_2345_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
else
{
lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___x_2472_; 
lean_del_object(v___x_2358_);
v___x_2364_ = lean_st_ref_get(v_a_2347_);
v___x_2365_ = 0;
v___x_2472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2364_, v_e_2345_);
lean_dec(v___x_2364_);
if (lean_obj_tag(v___x_2472_) == 1)
{
lean_object* v_val_2473_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; 
v_val_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_val_2473_);
lean_dec_ref(v___x_2472_);
v_fst_2474_ = lean_ctor_get(v_val_2473_, 0);
lean_inc(v_fst_2474_);
v_snd_2475_ = lean_ctor_get(v_val_2473_, 1);
lean_inc(v_snd_2475_);
lean_dec(v_val_2473_);
v___x_2476_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2475_, v_a_2350_);
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
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2483_; 
lean_dec_ref(v_e_2345_);
lean_dec_ref(v_F_2344_);
lean_dec(v_fixedPrefixSize_2343_);
lean_dec(v_recFnName_2342_);
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
lean_dec_ref(v_e_2345_);
lean_dec_ref(v_F_2344_);
lean_dec(v_fixedPrefixSize_2343_);
lean_dec(v_recFnName_2342_);
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
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
goto v___jp_2366_;
}
v___jp_2366_:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_e_2345_);
v___x_2375_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2342_, v_fixedPrefixSize_2343_, v_F_2344_, v_e_2345_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2463_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2463_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2463_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_options_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2382_ = lean_st_ref_take(v___y_2368_);
lean_inc(v_a_2376_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2376_);
lean_ctor_set(v___x_2383_, 1, v_a_2378_);
lean_inc_ref(v_e_2345_);
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2382_, v_e_2345_, v___x_2383_);
v___x_2385_ = lean_st_ref_set(v___y_2368_, v___x_2384_);
v_options_2386_ = lean_ctor_get(v___y_2373_, 2);
v___x_2387_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2388_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2390_; 
lean_dec_ref(v_e_2345_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v_a_2376_);
v___x_2390_ = v___x_2380_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2376_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
else
{
lean_object* v___x_2392_; uint8_t v_foApprox_2393_; uint8_t v_ctxApprox_2394_; uint8_t v_quasiPatternApprox_2395_; uint8_t v_constApprox_2396_; uint8_t v_isDefEqStuckEx_2397_; uint8_t v_unificationHints_2398_; uint8_t v_proofIrrelevance_2399_; uint8_t v_assignSyntheticOpaque_2400_; uint8_t v_offsetCnstrs_2401_; uint8_t v_etaStruct_2402_; uint8_t v_univApprox_2403_; uint8_t v_iota_2404_; uint8_t v_beta_2405_; uint8_t v_proj_2406_; uint8_t v_zeta_2407_; uint8_t v_zetaDelta_2408_; uint8_t v_zetaUnused_2409_; uint8_t v_zetaHave_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2462_; 
lean_del_object(v___x_2380_);
v___x_2392_ = l_Lean_Meta_Context_config(v___y_2371_);
v_foApprox_2393_ = lean_ctor_get_uint8(v___x_2392_, 0);
v_ctxApprox_2394_ = lean_ctor_get_uint8(v___x_2392_, 1);
v_quasiPatternApprox_2395_ = lean_ctor_get_uint8(v___x_2392_, 2);
v_constApprox_2396_ = lean_ctor_get_uint8(v___x_2392_, 3);
v_isDefEqStuckEx_2397_ = lean_ctor_get_uint8(v___x_2392_, 4);
v_unificationHints_2398_ = lean_ctor_get_uint8(v___x_2392_, 5);
v_proofIrrelevance_2399_ = lean_ctor_get_uint8(v___x_2392_, 6);
v_assignSyntheticOpaque_2400_ = lean_ctor_get_uint8(v___x_2392_, 7);
v_offsetCnstrs_2401_ = lean_ctor_get_uint8(v___x_2392_, 8);
v_etaStruct_2402_ = lean_ctor_get_uint8(v___x_2392_, 10);
v_univApprox_2403_ = lean_ctor_get_uint8(v___x_2392_, 11);
v_iota_2404_ = lean_ctor_get_uint8(v___x_2392_, 12);
v_beta_2405_ = lean_ctor_get_uint8(v___x_2392_, 13);
v_proj_2406_ = lean_ctor_get_uint8(v___x_2392_, 14);
v_zeta_2407_ = lean_ctor_get_uint8(v___x_2392_, 15);
v_zetaDelta_2408_ = lean_ctor_get_uint8(v___x_2392_, 16);
v_zetaUnused_2409_ = lean_ctor_get_uint8(v___x_2392_, 17);
v_zetaHave_2410_ = lean_ctor_get_uint8(v___x_2392_, 18);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2412_ = v___x_2392_;
v_isShared_2413_ = v_isSharedCheck_2462_;
goto v_resetjp_2411_;
}
else
{
lean_dec(v___x_2392_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2462_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
uint8_t v_trackZetaDelta_2414_; lean_object* v_zetaDeltaSet_2415_; lean_object* v_lctx_2416_; lean_object* v_localInstances_2417_; lean_object* v_defEqCtx_x3f_2418_; lean_object* v_synthPendingDepth_2419_; lean_object* v_canUnfold_x3f_2420_; uint8_t v_univApprox_2421_; uint8_t v_inTypeClassResolution_2422_; uint8_t v_cacheInferType_2423_; uint8_t v___x_2424_; lean_object* v_config_2426_; 
v_trackZetaDelta_2414_ = lean_ctor_get_uint8(v___y_2371_, sizeof(void*)*7);
v_zetaDeltaSet_2415_ = lean_ctor_get(v___y_2371_, 1);
v_lctx_2416_ = lean_ctor_get(v___y_2371_, 2);
v_localInstances_2417_ = lean_ctor_get(v___y_2371_, 3);
v_defEqCtx_x3f_2418_ = lean_ctor_get(v___y_2371_, 4);
v_synthPendingDepth_2419_ = lean_ctor_get(v___y_2371_, 5);
v_canUnfold_x3f_2420_ = lean_ctor_get(v___y_2371_, 6);
v_univApprox_2421_ = lean_ctor_get_uint8(v___y_2371_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2422_ = lean_ctor_get_uint8(v___y_2371_, sizeof(void*)*7 + 2);
v_cacheInferType_2423_ = lean_ctor_get_uint8(v___y_2371_, sizeof(void*)*7 + 3);
v___x_2424_ = 0;
if (v_isShared_2413_ == 0)
{
v_config_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 0, v_foApprox_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 1, v_ctxApprox_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 2, v_quasiPatternApprox_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 3, v_constApprox_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 4, v_isDefEqStuckEx_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 5, v_unificationHints_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 6, v_proofIrrelevance_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 7, v_assignSyntheticOpaque_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 8, v_offsetCnstrs_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 10, v_etaStruct_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 11, v_univApprox_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 12, v_iota_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 13, v_beta_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 14, v_proj_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 15, v_zeta_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 16, v_zetaDelta_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 17, v_zetaUnused_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 18, v_zetaHave_2410_);
v_config_2426_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
uint64_t v___x_2427_; uint64_t v___x_2428_; uint64_t v___x_2429_; lean_object* v___f_2430_; uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v_key_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_ctor_set_uint8(v_config_2426_, 9, v___x_2424_);
v___x_2427_ = l_Lean_Meta_Context_configKey(v___y_2371_);
v___x_2428_ = 2ULL;
v___x_2429_ = lean_uint64_shift_right(v___x_2427_, v___x_2428_);
lean_inc(v_a_2376_);
v___f_2430_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2430_, 0, v_a_2376_);
lean_closure_set(v___f_2430_, 1, v_e_2345_);
v___x_2431_ = lean_uint64_shift_left(v___x_2429_, v___x_2428_);
v___x_2432_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2433_ = lean_uint64_lor(v___x_2431_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2434_, 0, v_config_2426_);
lean_ctor_set_uint64(v___x_2434_, sizeof(void*)*1, v_key_2433_);
lean_inc(v_canUnfold_x3f_2420_);
lean_inc(v_synthPendingDepth_2419_);
lean_inc(v_defEqCtx_x3f_2418_);
lean_inc_ref(v_localInstances_2417_);
lean_inc_ref(v_lctx_2416_);
lean_inc(v_zetaDeltaSet_2415_);
v___x_2435_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v_zetaDeltaSet_2415_);
lean_ctor_set(v___x_2435_, 2, v_lctx_2416_);
lean_ctor_set(v___x_2435_, 3, v_localInstances_2417_);
lean_ctor_set(v___x_2435_, 4, v_defEqCtx_x3f_2418_);
lean_ctor_set(v___x_2435_, 5, v_synthPendingDepth_2419_);
lean_ctor_set(v___x_2435_, 6, v_canUnfold_x3f_2420_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7, v_trackZetaDelta_2414_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 1, v_univApprox_2421_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2422_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 3, v_cacheInferType_2423_);
v___x_2436_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2430_, v___x_2365_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___x_2435_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec_ref(v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2444_);
v___x_2438_ = v___x_2436_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2376_);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2376_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; 
v_unused_2452_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2452_);
v___x_2446_ = v___x_2436_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_dec(v___x_2436_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2376_);
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2376_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2376_);
v_a_2453_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2436_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2436_);
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
}
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_a_2376_);
lean_dec_ref(v_e_2345_);
v_a_2464_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2377_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2377_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_dec_ref(v_e_2345_);
return v___x_2375_;
}
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_e_2345_);
lean_dec_ref(v_F_2344_);
lean_dec(v_fixedPrefixSize_2343_);
lean_dec(v_recFnName_2342_);
v_a_2495_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2355_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2355_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2503_, lean_object* v_recFnName_2504_, lean_object* v_fixedPrefixSize_2505_, lean_object* v_F_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_expr_instantiate1(v_body_2503_, v_x_2507_);
v___x_2518_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2504_, v_fixedPrefixSize_2505_, v_F_2506_, v___x_2517_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2519_, lean_object* v_fixedPrefixSize_2520_, lean_object* v_F_2521_, lean_object* v_e_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2519_, v_fixedPrefixSize_2520_, v_F_2521_, v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec(v_a_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2533_, lean_object* v_fixedPrefixSize_2534_, lean_object* v_F_2535_, lean_object* v_sz_2536_, lean_object* v_i_2537_, lean_object* v_bs_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
size_t v_sz_boxed_2548_; size_t v_i_boxed_2549_; lean_object* v_res_2550_; 
v_sz_boxed_2548_ = lean_unbox_usize(v_sz_2536_);
lean_dec(v_sz_2536_);
v_i_boxed_2549_ = lean_unbox_usize(v_i_2537_);
lean_dec(v_i_2537_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2533_, v_fixedPrefixSize_2534_, v_F_2535_, v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2551_, lean_object* v_fixedPrefixSize_2552_, lean_object* v_F_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2551_, v_fixedPrefixSize_2552_, v_F_2553_, v_x_2554_, v_x_2555_, v_x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec(v___y_2557_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2567_, lean_object* v_fixedPrefixSize_2568_, lean_object* v_e_2569_, lean_object* v_as_2570_, lean_object* v_bs_2571_, lean_object* v_i_2572_, lean_object* v_cs_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2567_, v_fixedPrefixSize_2568_, v_e_2569_, v_as_2570_, v_bs_2571_, v_i_2572_, v_cs_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v_bs_2571_);
lean_dec_ref(v_as_2570_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2584_, lean_object* v_fixedPrefixSize_2585_, lean_object* v_F_2586_, lean_object* v_e_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2584_, v_fixedPrefixSize_2585_, v_F_2586_, v_e_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec(v_a_2588_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2598_, lean_object* v_fixedPrefixSize_2599_, lean_object* v_F_2600_, lean_object* v_e_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2598_, v_fixedPrefixSize_2599_, v_F_2600_, v_e_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec(v_a_2602_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2612_, lean_object* v_fixedPrefixSize_2613_, lean_object* v_F_2614_, lean_object* v_e_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2612_, v_fixedPrefixSize_2613_, v_F_2614_, v_e_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec(v_a_2616_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2626_, lean_object* v_k_2627_, uint8_t v_allowLevelAssignments_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2627_, v_allowLevelAssignments_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_k_2640_, lean_object* v_allowLevelAssignments_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2651_; lean_object* v_res_2652_; 
v_allowLevelAssignments_boxed_2651_ = lean_unbox(v_allowLevelAssignments_2641_);
v_res_2652_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2639_, v_k_2640_, v_allowLevelAssignments_boxed_2651_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2653_, lean_object* v_name_2654_, uint8_t v_bi_2655_, lean_object* v_type_2656_, lean_object* v_k_2657_, uint8_t v_kind_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2654_, v_bi_2655_, v_type_2656_, v_k_2657_, v_kind_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_name_2670_, lean_object* v_bi_2671_, lean_object* v_type_2672_, lean_object* v_k_2673_, lean_object* v_kind_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v_bi_boxed_2684_; uint8_t v_kind_boxed_2685_; lean_object* v_res_2686_; 
v_bi_boxed_2684_ = lean_unbox(v_bi_2671_);
v_kind_boxed_2685_ = lean_unbox(v_kind_2674_);
v_res_2686_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2669_, v_name_2670_, v_bi_boxed_2684_, v_type_2672_, v_k_2673_, v_kind_boxed_2685_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v___y_2675_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2687_, lean_object* v_e_2688_, lean_object* v_maxFVars_2689_, lean_object* v_k_2690_, uint8_t v_cleanupAnnotations_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2688_, v_maxFVars_2689_, v_k_2690_, v_cleanupAnnotations_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_e_2703_, lean_object* v_maxFVars_2704_, lean_object* v_k_2705_, lean_object* v_cleanupAnnotations_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2716_; lean_object* v_res_2717_; 
v_cleanupAnnotations_boxed_2716_ = lean_unbox(v_cleanupAnnotations_2706_);
v_res_2717_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2702_, v_e_2703_, v_maxFVars_2704_, v_k_2705_, v_cleanupAnnotations_boxed_2716_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2718_, lean_object* v_R_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2720_, v_b_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2723_, lean_object* v_msg_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2723_, v_msg_2724_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2735_, lean_object* v_msg_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2735_, v_msg_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2747_, lean_object* v_m_2748_, lean_object* v_a_2749_, lean_object* v_b_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2748_, v_a_2749_, v_b_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2752_, lean_object* v_msg_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2753_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec(v___y_2766_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2776_, lean_object* v_m_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2777_, v_a_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2780_, lean_object* v_m_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2780_, v_m_2781_, v_a_2782_);
lean_dec_ref(v_a_2782_);
lean_dec_ref(v_m_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2784_, lean_object* v_name_2785_, lean_object* v_type_2786_, lean_object* v_val_2787_, lean_object* v_k_2788_, uint8_t v_nondep_2789_, uint8_t v_kind_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2785_, v_type_2786_, v_val_2787_, v_k_2788_, v_nondep_2789_, v_kind_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2801_, lean_object* v_name_2802_, lean_object* v_type_2803_, lean_object* v_val_2804_, lean_object* v_k_2805_, lean_object* v_nondep_2806_, lean_object* v_kind_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v_nondep_boxed_2817_; uint8_t v_kind_boxed_2818_; lean_object* v_res_2819_; 
v_nondep_boxed_2817_ = lean_unbox(v_nondep_2806_);
v_kind_boxed_2818_ = lean_unbox(v_kind_2807_);
v_res_2819_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2801_, v_name_2802_, v_type_2803_, v_val_2804_, v_k_2805_, v_nondep_boxed_2817_, v_kind_boxed_2818_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2820_, v___y_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2842_, lean_object* v_a_2843_, lean_object* v_x_2844_){
_start:
{
uint8_t v___x_2845_; 
v___x_2845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2843_, v_x_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2846_, lean_object* v_a_2847_, lean_object* v_x_2848_){
_start:
{
uint8_t v_res_2849_; lean_object* v_r_2850_; 
v_res_2849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2846_, v_a_2847_, v_x_2848_);
lean_dec(v_x_2848_);
lean_dec_ref(v_a_2847_);
v_r_2850_ = lean_box(v_res_2849_);
return v_r_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2851_, lean_object* v_data_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2854_, lean_object* v_a_2855_, lean_object* v_b_2856_, lean_object* v_x_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2855_, v_b_2856_, v_x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2859_, lean_object* v_a_2860_, lean_object* v_x_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2860_, v_x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2863_, lean_object* v_a_2864_, lean_object* v_x_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2863_, v_a_2864_, v_x_2865_);
lean_dec(v_x_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2867_, lean_object* v_i_2868_, lean_object* v_source_2869_, lean_object* v_target_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2868_, v_source_2869_, v_target_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2872_, lean_object* v_constName_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_constName_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2884_, v_constName_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2897_, v_x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2900_, lean_object* v_ref_2901_, lean_object* v_constName_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2901_, v_constName_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_ref_2914_, lean_object* v_constName_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2913_, v_ref_2914_, v_constName_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec(v_ref_2914_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2926_, lean_object* v_ref_2927_, lean_object* v_msg_2928_, lean_object* v_declHint_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2927_, v_msg_2928_, v_declHint_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2940_, lean_object* v_ref_2941_, lean_object* v_msg_2942_, lean_object* v_declHint_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2940_, v_ref_2941_, v_msg_2942_, v_declHint_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec(v_ref_2941_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2954_, lean_object* v_declHint_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2954_, v_declHint_2955_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2966_, lean_object* v_declHint_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2966_, v_declHint_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec(v___y_2968_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2978_, lean_object* v_ref_2979_, lean_object* v_msg_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2979_, v_msg_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2991_, lean_object* v_ref_2992_, lean_object* v_msg_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2991_, v_ref_2992_, v_msg_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec(v_ref_2992_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_ref_3011_; lean_object* v___x_3012_; lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3057_; 
v_ref_3011_ = lean_ctor_get(v___y_3008_, 5);
v___x_3012_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3057_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3057_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v_traceState_3018_; lean_object* v_env_3019_; lean_object* v_nextMacroScope_3020_; lean_object* v_ngen_3021_; lean_object* v_auxDeclNGen_3022_; lean_object* v_cache_3023_; lean_object* v_messages_3024_; lean_object* v_infoState_3025_; lean_object* v_snapshotTasks_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3056_; 
v___x_3017_ = lean_st_ref_take(v___y_3009_);
v_traceState_3018_ = lean_ctor_get(v___x_3017_, 4);
v_env_3019_ = lean_ctor_get(v___x_3017_, 0);
v_nextMacroScope_3020_ = lean_ctor_get(v___x_3017_, 1);
v_ngen_3021_ = lean_ctor_get(v___x_3017_, 2);
v_auxDeclNGen_3022_ = lean_ctor_get(v___x_3017_, 3);
v_cache_3023_ = lean_ctor_get(v___x_3017_, 5);
v_messages_3024_ = lean_ctor_get(v___x_3017_, 6);
v_infoState_3025_ = lean_ctor_get(v___x_3017_, 7);
v_snapshotTasks_3026_ = lean_ctor_get(v___x_3017_, 8);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3028_ = v___x_3017_;
v_isShared_3029_ = v_isSharedCheck_3056_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_snapshotTasks_3026_);
lean_inc(v_infoState_3025_);
lean_inc(v_messages_3024_);
lean_inc(v_cache_3023_);
lean_inc(v_traceState_3018_);
lean_inc(v_auxDeclNGen_3022_);
lean_inc(v_ngen_3021_);
lean_inc(v_nextMacroScope_3020_);
lean_inc(v_env_3019_);
lean_dec(v___x_3017_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3056_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
uint64_t v_tid_3030_; lean_object* v_traces_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3055_; 
v_tid_3030_ = lean_ctor_get_uint64(v_traceState_3018_, sizeof(void*)*1);
v_traces_3031_ = lean_ctor_get(v_traceState_3018_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_traceState_3018_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3033_ = v_traceState_3018_;
v_isShared_3034_ = v_isSharedCheck_3055_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_traces_3031_);
lean_dec(v_traceState_3018_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3055_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; double v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3037_ = 0;
v___x_3038_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3039_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3039_, 0, v_cls_3004_);
lean_ctor_set(v___x_3039_, 1, v___x_3035_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
lean_ctor_set_float(v___x_3039_, sizeof(void*)*3, v___x_3036_);
lean_ctor_set_float(v___x_3039_, sizeof(void*)*3 + 8, v___x_3036_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*3 + 16, v___x_3037_);
v___x_3040_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3041_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v_a_3013_);
lean_ctor_set(v___x_3041_, 2, v___x_3040_);
lean_inc(v_ref_3011_);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_ref_3011_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_PersistentArray_push___redArg(v_traces_3031_, v___x_3042_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3043_);
v___x_3045_ = v___x_3033_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3043_);
lean_ctor_set_uint64(v_reuseFailAlloc_3054_, sizeof(void*)*1, v_tid_3030_);
v___x_3045_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___x_3045_);
v___x_3047_ = v___x_3028_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_env_3019_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_nextMacroScope_3020_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_ngen_3021_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_auxDeclNGen_3022_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3053_, 5, v_cache_3023_);
lean_ctor_set(v_reuseFailAlloc_3053_, 6, v_messages_3024_);
lean_ctor_set(v_reuseFailAlloc_3053_, 7, v_infoState_3025_);
lean_ctor_set(v_reuseFailAlloc_3053_, 8, v_snapshotTasks_3026_);
v___x_3047_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = lean_st_ref_set(v___y_3009_, v___x_3047_);
v___x_3049_ = lean_box(0);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3049_);
v___x_3051_ = v___x_3015_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3058_, lean_object* v_msg_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3058_, v_msg_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3065_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_unsigned_to_nat(16u);
v___x_3068_ = lean_mk_array(v___x_3067_, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3074_ = l_Lean_stringToMessageData(v___x_3073_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3077_ = l_Lean_stringToMessageData(v___x_3076_);
return v___x_3077_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3080_ = l_Lean_stringToMessageData(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3081_, lean_object* v_fixedPrefixSize_3082_, lean_object* v_F_3083_, lean_object* v_e_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v_options_3113_; uint8_t v_hasTrace_3114_; 
v_options_3113_ = lean_ctor_get(v_a_3089_, 2);
v_hasTrace_3114_ = lean_ctor_get_uint8(v_options_3113_, sizeof(void*)*1);
if (v_hasTrace_3114_ == 0)
{
v___y_3093_ = v_a_3085_;
v___y_3094_ = v_a_3086_;
v___y_3095_ = v_a_3087_;
v___y_3096_ = v_a_3088_;
v___y_3097_ = v_a_3089_;
v___y_3098_ = v_a_3090_;
goto v___jp_3092_;
}
else
{
lean_object* v_inheritedTraceOptions_3115_; lean_object* v_cls_3116_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v_options_3123_; lean_object* v_inheritedTraceOptions_3124_; lean_object* v___y_3125_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_inheritedTraceOptions_3115_ = lean_ctor_get(v_a_3089_, 13);
v_cls_3116_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3146_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3115_, v_options_3113_, v___x_3146_);
if (v___x_3147_ == 0)
{
v___y_3118_ = v_a_3085_;
v___y_3119_ = v_a_3086_;
v___y_3120_ = v_a_3087_;
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v_options_3123_ = v_options_3113_;
v_inheritedTraceOptions_3124_ = v_inheritedTraceOptions_3115_;
v___y_3125_ = v_a_3090_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3084_);
v___x_3149_ = l_Lean_indentExpr(v_e_3084_);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3116_, v___x_3150_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref(v___x_3151_);
v___y_3118_ = v_a_3085_;
v___y_3119_ = v_a_3086_;
v___y_3120_ = v_a_3087_;
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v_options_3123_ = v_options_3113_;
v_inheritedTraceOptions_3124_ = v_inheritedTraceOptions_3115_;
v___y_3125_ = v_a_3090_;
goto v___jp_3117_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_e_3084_);
lean_dec_ref(v_F_3083_);
lean_dec(v_fixedPrefixSize_3082_);
lean_dec(v_recFnName_3081_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
v___jp_3117_:
{
lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3124_, v_options_3123_, v___x_3126_);
if (v___x_3127_ == 0)
{
v___y_3093_ = v___y_3118_;
v___y_3094_ = v___y_3119_;
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3125_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3128_; 
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
lean_inc_ref(v_F_3083_);
v___x_3128_ = lean_infer_type(v_F_3083_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3125_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3083_);
v___x_3131_ = l_Lean_MessageData_ofExpr(v_F_3083_);
v___x_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = l_Lean_indentExpr(v_a_3129_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3116_, v___x_3136_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3125_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_dec_ref(v___x_3137_);
v___y_3093_ = v___y_3118_;
v___y_3094_ = v___y_3119_;
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3125_;
goto v___jp_3092_;
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_e_3084_);
lean_dec_ref(v_F_3083_);
lean_dec(v_fixedPrefixSize_3082_);
lean_dec(v_recFnName_3081_);
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_dec_ref(v_e_3084_);
lean_dec_ref(v_F_3083_);
lean_dec(v_fixedPrefixSize_3082_);
lean_dec(v_recFnName_3081_);
return v___x_3128_;
}
}
}
}
v___jp_3092_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3099_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3100_ = lean_st_mk_ref(v___x_3099_);
v___x_3101_ = lean_st_mk_ref(v___x_3099_);
v___x_3102_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3081_, v_fixedPrefixSize_3082_, v_F_3083_, v_e_3084_, v___x_3101_, v___x_3100_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3107_ = lean_st_ref_get(v___x_3101_);
lean_dec(v___x_3101_);
lean_dec(v___x_3107_);
v___x_3108_ = lean_st_ref_get(v___x_3100_);
lean_dec(v___x_3100_);
lean_dec(v___x_3108_);
if (v_isShared_3106_ == 0)
{
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3103_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_dec(v___x_3101_);
lean_dec(v___x_3100_);
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3160_, lean_object* v_fixedPrefixSize_3161_, lean_object* v_F_3162_, lean_object* v_e_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3160_, v_fixedPrefixSize_3161_, v_F_3162_, v_e_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3172_, lean_object* v_msg_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3172_, v_msg_3173_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3182_, lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3182_, v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v_b_3195_, lean_object* v_c_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; 
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v___y_3194_);
lean_inc_ref(v___y_3193_);
v___x_3202_ = lean_apply_9(v_k_3192_, v_b_3195_, v_c_3196_, v___y_3193_, v___y_3194_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, lean_box(0));
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v_b_3206_, lean_object* v_c_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3203_, v___y_3204_, v___y_3205_, v_b_3206_, v_c_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3214_, lean_object* v_k_3215_, uint8_t v_cleanupAnnotations_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___f_3224_; uint8_t v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
v___f_3224_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3224_, 0, v_k_3215_);
lean_closure_set(v___f_3224_, 1, v___y_3217_);
lean_closure_set(v___f_3224_, 2, v___y_3218_);
v___x_3225_ = 1;
v___x_3226_ = 0;
v___x_3227_ = lean_box(0);
v___x_3228_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3214_, v___x_3225_, v___x_3226_, v___x_3225_, v___x_3226_, v___x_3227_, v___f_3224_, v_cleanupAnnotations_3216_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3228_) == 0)
{
return v___x_3228_;
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3237_, lean_object* v_k_3238_, lean_object* v_cleanupAnnotations_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3247_; lean_object* v_res_3248_; 
v_cleanupAnnotations_boxed_3247_ = lean_unbox(v_cleanupAnnotations_3239_);
v_res_3248_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3237_, v_k_3238_, v_cleanupAnnotations_boxed_3247_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3249_, lean_object* v_e_3250_, lean_object* v_k_3251_, uint8_t v_cleanupAnnotations_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3250_, v_k_3251_, v_cleanupAnnotations_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3261_, lean_object* v_e_3262_, lean_object* v_k_3263_, lean_object* v_cleanupAnnotations_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3272_; lean_object* v_res_3273_; 
v_cleanupAnnotations_boxed_3272_ = lean_unbox(v_cleanupAnnotations_3264_);
v_res_3273_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3261_, v_e_3262_, v_k_3263_, v_cleanupAnnotations_boxed_3272_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3274_, lean_object* v_maxFVars_3275_, lean_object* v_k_3276_, uint8_t v_cleanupAnnotations_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___f_3285_; uint8_t v___x_3286_; uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
v___f_3285_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3285_, 0, v_k_3276_);
lean_closure_set(v___f_3285_, 1, v___y_3278_);
lean_closure_set(v___f_3285_, 2, v___y_3279_);
v___x_3286_ = 1;
v___x_3287_ = 0;
v___x_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3288_, 0, v_maxFVars_3275_);
v___x_3289_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3274_, v___x_3286_, v___x_3287_, v___x_3286_, v___x_3287_, v___x_3288_, v___f_3285_, v_cleanupAnnotations_3277_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec_ref(v___x_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
return v___x_3289_;
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3298_, lean_object* v_maxFVars_3299_, lean_object* v_k_3300_, lean_object* v_cleanupAnnotations_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3309_; lean_object* v_res_3310_; 
v_cleanupAnnotations_boxed_3309_ = lean_unbox(v_cleanupAnnotations_3301_);
v_res_3310_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3298_, v_maxFVars_3299_, v_k_3300_, v_cleanupAnnotations_boxed_3309_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3311_, lean_object* v_e_3312_, lean_object* v_maxFVars_3313_, lean_object* v_k_3314_, uint8_t v_cleanupAnnotations_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3312_, v_maxFVars_3313_, v_k_3314_, v_cleanupAnnotations_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_e_3325_, lean_object* v_maxFVars_3326_, lean_object* v_k_3327_, lean_object* v_cleanupAnnotations_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3336_; lean_object* v_res_3337_; 
v_cleanupAnnotations_boxed_3336_ = lean_unbox(v_cleanupAnnotations_3328_);
v_res_3337_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3324_, v_e_3325_, v_maxFVars_3326_, v_k_3327_, v_cleanupAnnotations_boxed_3336_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3338_, lean_object* v___x_3339_, lean_object* v___x_3340_, lean_object* v_x_3341_, uint8_t v___x_3342_, lean_object* v_xs_3343_, lean_object* v_type_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3352_ = l_Lean_LocalDecl_type(v_a_3338_);
v___x_3353_ = lean_array_get_borrowed(v___x_3339_, v_xs_3343_, v___x_3340_);
v___x_3354_ = l_Lean_Expr_replaceFVar(v___x_3352_, v_x_3341_, v___x_3353_);
lean_dec_ref(v___x_3352_);
v___x_3355_ = l_Lean_mkArrow(v___x_3354_, v_type_3344_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; uint8_t v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc_n(v_a_3356_, 2);
lean_dec_ref(v___x_3355_);
v___x_3357_ = 0;
v___x_3358_ = 1;
v___x_3359_ = l_Lean_Meta_mkLambdaFVars(v_xs_3343_, v_a_3356_, v___x_3357_, v___x_3342_, v___x_3357_, v___x_3342_, v___x_3358_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = l_Lean_Meta_getLevel(v_a_3356_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3370_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3370_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3370_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_a_3360_);
lean_ctor_set(v___x_3366_, 1, v_a_3362_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3366_);
v___x_3368_ = v___x_3364_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_a_3360_);
v_a_3371_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3361_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3361_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_a_3356_);
v_a_3379_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3359_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3359_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_a_3387_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3355_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3355_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3395_, lean_object* v___x_3396_, lean_object* v___x_3397_, lean_object* v_x_3398_, lean_object* v___x_3399_, lean_object* v_xs_3400_, lean_object* v_type_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
uint8_t v___x_6703__boxed_3409_; lean_object* v_res_3410_; 
v___x_6703__boxed_3409_ = lean_unbox(v___x_3399_);
v_res_3410_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3395_, v___x_3396_, v___x_3397_, v_x_3398_, v___x_6703__boxed_3409_, v_xs_3400_, v_type_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v_xs_3400_);
lean_dec(v___x_3397_);
lean_dec_ref(v___x_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v_b_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v___x_3420_; 
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3417_);
lean_inc(v___y_3416_);
lean_inc_ref(v___y_3415_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
v___x_3420_ = lean_apply_8(v_k_3411_, v_b_3414_, v___y_3412_, v___y_3413_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, lean_box(0));
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v_b_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3421_, v___y_3422_, v___y_3423_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3431_, uint8_t v_bi_3432_, lean_object* v_type_3433_, lean_object* v_k_3434_, uint8_t v_kind_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___f_3443_; lean_object* v___x_3444_; 
lean_inc(v___y_3437_);
lean_inc_ref(v___y_3436_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3443_, 0, v_k_3434_);
lean_closure_set(v___f_3443_, 1, v___y_3436_);
lean_closure_set(v___f_3443_, 2, v___y_3437_);
v___x_3444_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3431_, v_bi_3432_, v_type_3433_, v___f_3443_, v_kind_3435_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3444_) == 0)
{
return v___x_3444_;
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3453_, lean_object* v_bi_3454_, lean_object* v_type_3455_, lean_object* v_k_3456_, lean_object* v_kind_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v_bi_boxed_3465_; uint8_t v_kind_boxed_3466_; lean_object* v_res_3467_; 
v_bi_boxed_3465_ = lean_unbox(v_bi_3454_);
v_kind_boxed_3466_ = lean_unbox(v_kind_3457_);
v_res_3467_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3453_, v_bi_boxed_3465_, v_type_3455_, v_k_3456_, v_kind_boxed_3466_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3468_, lean_object* v_type_3469_, lean_object* v_k_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = 0;
v___x_3479_ = 0;
v___x_3480_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3468_, v___x_3478_, v_type_3469_, v_k_3470_, v___x_3479_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3481_, lean_object* v_type_3482_, lean_object* v_k_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3481_, v_type_3482_, v_k_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3505_, lean_object* v_F_3506_, lean_object* v_val_3507_, lean_object* v_k_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
uint8_t v___y_3517_; uint8_t v___x_3632_; 
v___x_3632_ = l_Lean_Expr_isFVar(v_x_3505_);
if (v___x_3632_ == 0)
{
v___y_3517_ = v___x_3632_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3634_ = lean_unsigned_to_nat(6u);
v___x_3635_ = l_Lean_Expr_isAppOfArity(v_val_3507_, v___x_3633_, v___x_3634_);
v___y_3517_ = v___x_3635_;
goto v___jp_3516_;
}
v___jp_3516_:
{
if (v___y_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
v___x_3518_ = lean_apply_10(v_k_3508_, v_x_3505_, v_F_3506_, v_val_3507_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, lean_box(0));
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3519_ = lean_unsigned_to_nat(3u);
v___x_3520_ = l_Lean_Expr_getAppNumArgs(v_val_3507_);
v___x_3521_ = lean_nat_sub(v___x_3520_, v___x_3519_);
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = lean_nat_sub(v___x_3521_, v___x_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = l_Lean_Expr_getRevArg_x21(v_val_3507_, v___x_3523_);
v___x_3525_ = lean_expr_eqv(v___x_3524_, v_x_3505_);
lean_dec_ref(v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v___x_3520_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
v___x_3526_ = lean_apply_10(v_k_3508_, v_x_3505_, v_F_3506_, v_val_3507_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, lean_box(0));
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3527_ = lean_unsigned_to_nat(4u);
v___x_3528_ = lean_nat_sub(v___x_3520_, v___x_3527_);
v___x_3529_ = lean_nat_sub(v___x_3528_, v___x_3522_);
lean_dec(v___x_3528_);
v___x_3530_ = l_Lean_Expr_getRevArg_x21(v_val_3507_, v___x_3529_);
v___x_3531_ = l_Lean_Expr_isLambda(v___x_3530_);
lean_dec_ref(v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; 
lean_dec(v___x_3520_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
v___x_3532_ = lean_apply_10(v_k_3508_, v_x_3505_, v_F_3506_, v_val_3507_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, lean_box(0));
return v___x_3532_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3533_ = lean_unsigned_to_nat(5u);
v___x_3534_ = lean_nat_sub(v___x_3520_, v___x_3533_);
v___x_3535_ = lean_nat_sub(v___x_3534_, v___x_3522_);
lean_dec(v___x_3534_);
v___x_3536_ = l_Lean_Expr_getRevArg_x21(v_val_3507_, v___x_3535_);
v___x_3537_ = l_Lean_Expr_isLambda(v___x_3536_);
lean_dec_ref(v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec(v___x_3520_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
v___x_3538_ = lean_apply_10(v_k_3508_, v_x_3505_, v_F_3506_, v_val_3507_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, lean_box(0));
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = l_Lean_Expr_fvarId_x21(v_F_3506_);
v___x_3540_ = l_Lean_FVarId_getDecl___redArg(v___x_3539_, v_a_3511_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v_dummy_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_args_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc_n(v_a_3541_, 2);
lean_dec_ref(v___x_3540_);
v___x_3542_ = l_Lean_instInhabitedExpr;
v_dummy_3543_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3520_);
v___x_3544_ = lean_mk_array(v___x_3520_, v_dummy_3543_);
v___x_3545_ = lean_nat_sub(v___x_3520_, v___x_3522_);
lean_dec(v___x_3520_);
v_args_3546_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3507_, v___x_3544_, v___x_3545_);
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = lean_box(v___x_3531_);
lean_inc_ref(v_x_3505_);
v___f_3549_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3549_, 0, v_a_3541_);
lean_closure_set(v___f_3549_, 1, v___x_3542_);
lean_closure_set(v___f_3549_, 2, v___x_3547_);
lean_closure_set(v___f_3549_, 3, v_x_3505_);
lean_closure_set(v___f_3549_, 4, v___x_3548_);
v___x_3550_ = lean_unsigned_to_nat(2u);
v___x_3551_ = lean_array_get(v___x_3542_, v_args_3546_, v___x_3550_);
v___x_3552_ = 0;
v___x_3553_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3551_, v___f_3549_, v___x_3552_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v_fst_3555_; lean_object* v_snd_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3615_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref(v___x_3553_);
v_fst_3555_ = lean_ctor_get(v_a_3554_, 0);
v_snd_3556_ = lean_ctor_get(v_a_3554_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3554_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3558_ = v_a_3554_;
v_isShared_3559_ = v_isSharedCheck_3615_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_snd_3556_);
lean_inc(v_fst_3555_);
lean_dec(v_a_3554_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3615_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_00_u03b1_3560_; lean_object* v_00_u03b2_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_00_u03b1_3560_ = lean_array_get(v___x_3542_, v_args_3546_, v___x_3547_);
v_00_u03b2_3561_ = lean_array_get(v___x_3542_, v_args_3546_, v___x_3522_);
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3563_ = lean_array_get(v___x_3542_, v_args_3546_, v___x_3527_);
lean_inc_ref(v_x_3505_);
lean_inc(v_a_3541_);
lean_inc_ref(v_k_3508_);
lean_inc(v_00_u03b2_3561_);
lean_inc(v_00_u03b1_3560_);
v___x_3564_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3542_, v___x_3547_, v_00_u03b1_3560_, v_00_u03b2_3561_, v___x_3519_, v_k_3508_, v___x_3550_, v___x_3552_, v___x_3531_, v_a_3541_, v_x_3505_, v___x_3522_, v___x_3562_, v___x_3563_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3567_ = lean_array_get(v___x_3542_, v_args_3546_, v___x_3533_);
lean_dec_ref(v_args_3546_);
lean_inc_ref(v_x_3505_);
lean_inc(v_00_u03b2_3561_);
lean_inc(v_00_u03b1_3560_);
v___x_3568_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3542_, v___x_3547_, v_00_u03b1_3560_, v_00_u03b2_3561_, v___x_3519_, v_k_3508_, v___x_3550_, v___x_3552_, v___x_3531_, v_a_3541_, v_x_3505_, v___x_3522_, v___x_3566_, v___x_3567_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
lean_inc(v_00_u03b1_3560_);
v___x_3570_ = l_Lean_Meta_getLevel(v_00_u03b1_3560_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
lean_inc(v_00_u03b2_3561_);
v___x_3572_ = l_Lean_Meta_getLevel(v_00_u03b2_3561_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3598_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3598_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3598_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3578_ = lean_box(0);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 1);
lean_ctor_set(v___x_3558_, 1, v___x_3578_);
lean_ctor_set(v___x_3558_, 0, v_a_3573_);
v___x_3580_ = v___x_3558_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3573_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3581_, 0, v_a_3571_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_snd_3556_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = l_Lean_mkConst(v___x_3577_, v___x_3582_);
v___x_3584_ = lean_unsigned_to_nat(7u);
v___x_3585_ = lean_mk_empty_array_with_capacity(v___x_3584_);
v___x_3586_ = lean_array_push(v___x_3585_, v_00_u03b1_3560_);
v___x_3587_ = lean_array_push(v___x_3586_, v_00_u03b2_3561_);
v___x_3588_ = lean_array_push(v___x_3587_, v_fst_3555_);
v___x_3589_ = lean_array_push(v___x_3588_, v_x_3505_);
v___x_3590_ = lean_array_push(v___x_3589_, v_a_3565_);
v___x_3591_ = lean_array_push(v___x_3590_, v_a_3569_);
v___x_3592_ = lean_array_push(v___x_3591_, v_F_3506_);
v___x_3593_ = l_Lean_mkAppN(v___x_3583_, v___x_3592_);
lean_dec_ref(v___x_3592_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3593_);
v___x_3595_ = v___x_3575_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
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
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v_a_3571_);
lean_dec(v_a_3569_);
lean_dec(v_a_3565_);
lean_dec(v_00_u03b2_3561_);
lean_dec(v_00_u03b1_3560_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3556_);
lean_dec(v_fst_3555_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
v_a_3599_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3572_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3572_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v_a_3569_);
lean_dec(v_a_3565_);
lean_dec(v_00_u03b2_3561_);
lean_dec(v_00_u03b1_3560_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3556_);
lean_dec(v_fst_3555_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
v_a_3607_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3570_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3570_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_dec(v_a_3565_);
lean_dec(v_00_u03b2_3561_);
lean_dec(v_00_u03b1_3560_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3556_);
lean_dec(v_fst_3555_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
return v___x_3568_;
}
}
else
{
lean_dec(v_00_u03b2_3561_);
lean_dec(v_00_u03b1_3560_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3556_);
lean_dec(v_fst_3555_);
lean_dec_ref(v_args_3546_);
lean_dec(v_a_3541_);
lean_dec_ref(v_k_3508_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v_args_3546_);
lean_dec(v_a_3541_);
lean_dec_ref(v_k_3508_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
v_a_3616_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3553_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3553_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v___x_3520_);
lean_dec_ref(v_k_3508_);
lean_dec_ref(v_val_3507_);
lean_dec_ref(v_F_3506_);
lean_dec_ref(v_x_3505_);
v_a_3624_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3540_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3540_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3636_, lean_object* v_body_3637_, lean_object* v_k_3638_, lean_object* v___x_3639_, uint8_t v___x_3640_, uint8_t v___x_3641_, lean_object* v_FNew_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; 
lean_inc_ref(v_FNew_3642_);
lean_inc_ref(v___x_3636_);
v___x_3650_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3636_, v_FNew_3642_, v_body_3637_, v_k_3638_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = lean_mk_empty_array_with_capacity(v___x_3639_);
v___x_3653_ = lean_array_push(v___x_3652_, v___x_3636_);
v___x_3654_ = lean_array_push(v___x_3653_, v_FNew_3642_);
v___x_3655_ = 1;
v___x_3656_ = l_Lean_Meta_mkLambdaFVars(v___x_3654_, v_a_3651_, v___x_3640_, v___x_3641_, v___x_3640_, v___x_3641_, v___x_3655_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec_ref(v___x_3654_);
return v___x_3656_;
}
else
{
lean_dec_ref(v_FNew_3642_);
lean_dec_ref(v___x_3636_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3657_, lean_object* v_body_3658_, lean_object* v_k_3659_, lean_object* v___x_3660_, lean_object* v___x_3661_, lean_object* v___x_3662_, lean_object* v_FNew_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v___x_6949__boxed_3671_; uint8_t v___x_6950__boxed_3672_; lean_object* v_res_3673_; 
v___x_6949__boxed_3671_ = lean_unbox(v___x_3661_);
v___x_6950__boxed_3672_ = lean_unbox(v___x_3662_);
v_res_3673_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3657_, v_body_3658_, v_k_3659_, v___x_3660_, v___x_6949__boxed_3671_, v___x_6950__boxed_3672_, v_FNew_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___x_3660_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3674_, lean_object* v___x_3675_, lean_object* v_00_u03b1_3676_, lean_object* v_00_u03b2_3677_, lean_object* v___x_3678_, lean_object* v_ctorName_3679_, lean_object* v_k_3680_, lean_object* v___x_3681_, uint8_t v___x_3682_, uint8_t v___x_3683_, lean_object* v_a_3684_, lean_object* v_x_3685_, lean_object* v_xs_3686_, lean_object* v_body_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3695_ = lean_array_get_borrowed(v___x_3674_, v_xs_3686_, v___x_3675_);
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_00_u03b1_3676_);
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_00_u03b2_3677_);
lean_inc(v___x_3695_);
v___x_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3695_);
v___x_3699_ = lean_mk_empty_array_with_capacity(v___x_3678_);
v___x_3700_ = lean_array_push(v___x_3699_, v___x_3696_);
v___x_3701_ = lean_array_push(v___x_3700_, v___x_3697_);
v___x_3702_ = lean_array_push(v___x_3701_, v___x_3698_);
v___x_3703_ = l_Lean_Meta_mkAppOptM(v_ctorName_3679_, v___x_3702_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref(v___x_3703_);
v___x_3705_ = lean_box(v___x_3682_);
v___x_3706_ = lean_box(v___x_3683_);
lean_inc(v___x_3695_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3707_, 0, v___x_3695_);
lean_closure_set(v___f_3707_, 1, v_body_3687_);
lean_closure_set(v___f_3707_, 2, v_k_3680_);
lean_closure_set(v___f_3707_, 3, v___x_3681_);
lean_closure_set(v___f_3707_, 4, v___x_3705_);
lean_closure_set(v___f_3707_, 5, v___x_3706_);
v___x_3708_ = l_Lean_LocalDecl_type(v_a_3684_);
v___x_3709_ = l_Lean_Expr_replaceFVar(v___x_3708_, v_x_3685_, v_a_3704_);
lean_dec(v_a_3704_);
lean_dec_ref(v___x_3708_);
v___x_3710_ = l_Lean_LocalDecl_userName(v_a_3684_);
v___x_3711_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3710_, v___x_3709_, v___f_3707_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
return v___x_3711_;
}
else
{
lean_dec_ref(v_body_3687_);
lean_dec_ref(v_x_3685_);
lean_dec(v___x_3681_);
lean_dec_ref(v_k_3680_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3712_ = _args[0];
lean_object* v___x_3713_ = _args[1];
lean_object* v_00_u03b1_3714_ = _args[2];
lean_object* v_00_u03b2_3715_ = _args[3];
lean_object* v___x_3716_ = _args[4];
lean_object* v_ctorName_3717_ = _args[5];
lean_object* v_k_3718_ = _args[6];
lean_object* v___x_3719_ = _args[7];
lean_object* v___x_3720_ = _args[8];
lean_object* v___x_3721_ = _args[9];
lean_object* v_a_3722_ = _args[10];
lean_object* v_x_3723_ = _args[11];
lean_object* v_xs_3724_ = _args[12];
lean_object* v_body_3725_ = _args[13];
lean_object* v___y_3726_ = _args[14];
lean_object* v___y_3727_ = _args[15];
lean_object* v___y_3728_ = _args[16];
lean_object* v___y_3729_ = _args[17];
lean_object* v___y_3730_ = _args[18];
lean_object* v___y_3731_ = _args[19];
lean_object* v___y_3732_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3733_; uint8_t v___x_6971__boxed_3734_; lean_object* v_res_3735_; 
v___x_6970__boxed_3733_ = lean_unbox(v___x_3720_);
v___x_6971__boxed_3734_ = lean_unbox(v___x_3721_);
v_res_3735_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3712_, v___x_3713_, v_00_u03b1_3714_, v_00_u03b2_3715_, v___x_3716_, v_ctorName_3717_, v_k_3718_, v___x_3719_, v___x_6970__boxed_3733_, v___x_6971__boxed_3734_, v_a_3722_, v_x_3723_, v_xs_3724_, v_body_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec_ref(v_xs_3724_);
lean_dec_ref(v_a_3722_);
lean_dec(v___x_3716_);
lean_dec(v___x_3713_);
lean_dec_ref(v___x_3712_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3736_, lean_object* v___x_3737_, lean_object* v_00_u03b1_3738_, lean_object* v_00_u03b2_3739_, lean_object* v___x_3740_, lean_object* v_k_3741_, lean_object* v___x_3742_, uint8_t v___x_3743_, uint8_t v___x_3744_, lean_object* v_a_3745_, lean_object* v_x_3746_, lean_object* v___x_3747_, lean_object* v_ctorName_3748_, lean_object* v_minor_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___f_3759_; lean_object* v___x_3760_; 
v___x_3757_ = lean_box(v___x_3743_);
v___x_3758_ = lean_box(v___x_3744_);
v___f_3759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3759_, 0, v___x_3736_);
lean_closure_set(v___f_3759_, 1, v___x_3737_);
lean_closure_set(v___f_3759_, 2, v_00_u03b1_3738_);
lean_closure_set(v___f_3759_, 3, v_00_u03b2_3739_);
lean_closure_set(v___f_3759_, 4, v___x_3740_);
lean_closure_set(v___f_3759_, 5, v_ctorName_3748_);
lean_closure_set(v___f_3759_, 6, v_k_3741_);
lean_closure_set(v___f_3759_, 7, v___x_3742_);
lean_closure_set(v___f_3759_, 8, v___x_3757_);
lean_closure_set(v___f_3759_, 9, v___x_3758_);
lean_closure_set(v___f_3759_, 10, v_a_3745_);
lean_closure_set(v___f_3759_, 11, v_x_3746_);
v___x_3760_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3749_, v___x_3747_, v___f_3759_, v___x_3743_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3761_ = _args[0];
lean_object* v___x_3762_ = _args[1];
lean_object* v_00_u03b1_3763_ = _args[2];
lean_object* v_00_u03b2_3764_ = _args[3];
lean_object* v___x_3765_ = _args[4];
lean_object* v_k_3766_ = _args[5];
lean_object* v___x_3767_ = _args[6];
lean_object* v___x_3768_ = _args[7];
lean_object* v___x_3769_ = _args[8];
lean_object* v_a_3770_ = _args[9];
lean_object* v_x_3771_ = _args[10];
lean_object* v___x_3772_ = _args[11];
lean_object* v_ctorName_3773_ = _args[12];
lean_object* v_minor_3774_ = _args[13];
lean_object* v___y_3775_ = _args[14];
lean_object* v___y_3776_ = _args[15];
lean_object* v___y_3777_ = _args[16];
lean_object* v___y_3778_ = _args[17];
lean_object* v___y_3779_ = _args[18];
lean_object* v___y_3780_ = _args[19];
lean_object* v___y_3781_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3782_; uint8_t v___x_6935__boxed_3783_; lean_object* v_res_3784_; 
v___x_6934__boxed_3782_ = lean_unbox(v___x_3768_);
v___x_6935__boxed_3783_ = lean_unbox(v___x_3769_);
v_res_3784_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3761_, v___x_3762_, v_00_u03b1_3763_, v_00_u03b2_3764_, v___x_3765_, v_k_3766_, v___x_3767_, v___x_6934__boxed_3782_, v___x_6935__boxed_3783_, v_a_3770_, v_x_3771_, v___x_3772_, v_ctorName_3773_, v_minor_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3785_, lean_object* v_F_3786_, lean_object* v_val_3787_, lean_object* v_k_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3785_, v_F_3786_, v_val_3787_, v_k_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3797_, lean_object* v_name_3798_, uint8_t v_bi_3799_, lean_object* v_type_3800_, lean_object* v_k_3801_, uint8_t v_kind_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3798_, v_bi_3799_, v_type_3800_, v_k_3801_, v_kind_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_name_3812_, lean_object* v_bi_3813_, lean_object* v_type_3814_, lean_object* v_k_3815_, lean_object* v_kind_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
uint8_t v_bi_boxed_3824_; uint8_t v_kind_boxed_3825_; lean_object* v_res_3826_; 
v_bi_boxed_3824_ = lean_unbox(v_bi_3813_);
v_kind_boxed_3825_ = lean_unbox(v_kind_3816_);
v_res_3826_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3811_, v_name_3812_, v_bi_boxed_3824_, v_type_3814_, v_k_3815_, v_kind_boxed_3825_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3827_, lean_object* v_name_3828_, lean_object* v_type_3829_, lean_object* v_k_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3828_, v_type_3829_, v_k_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3839_, lean_object* v_name_3840_, lean_object* v_type_3841_, lean_object* v_k_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3839_, v_name_3840_, v_type_3841_, v_k_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3850_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3874__overap_3861_; lean_object* v___x_3862_; 
v___x_3860_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3861_ = lean_panic_fn_borrowed(v___x_3860_, v_msg_3852_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc_ref(v___y_3855_);
lean_inc(v___y_3854_);
lean_inc_ref(v___y_3853_);
v___x_3862_ = lean_apply_7(v___x_3874__overap_3861_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, lean_box(0));
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3871_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3876_ = lean_unsigned_to_nat(49u);
v___x_3877_ = lean_unsigned_to_nat(186u);
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3880_ = l_mkPanicMessageWithDecl(v___x_3879_, v___x_3878_, v___x_3877_, v___x_3876_, v___x_3875_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3886_, lean_object* v_a_3887_, lean_object* v_k_3888_, lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v___x_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v_FNew_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
uint8_t v___x_4042__boxed_3902_; uint8_t v___x_4043__boxed_3903_; uint8_t v___x_4044__boxed_3904_; lean_object* v_res_3905_; 
v___x_4042__boxed_3902_ = lean_unbox(v___x_3891_);
v___x_4043__boxed_3903_ = lean_unbox(v___x_3892_);
v___x_4044__boxed_3904_ = lean_unbox(v___x_3893_);
v_res_3905_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3886_, v_a_3887_, v_k_3888_, v___x_3889_, v___x_3890_, v___x_4042__boxed_3902_, v___x_4043__boxed_3903_, v___x_4044__boxed_3904_, v_FNew_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___x_3889_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3906_, lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v___x_3909_, uint8_t v___x_3910_, uint8_t v___x_3911_, lean_object* v_00_u03b1_3912_, lean_object* v_00_u03b2_3913_, lean_object* v___x_3914_, lean_object* v_k_3915_, lean_object* v___x_3916_, lean_object* v_a_3917_, lean_object* v_x_3918_, lean_object* v_xs_3919_, lean_object* v_body_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; 
v___x_3928_ = lean_array_get(v___x_3906_, v_xs_3919_, v___x_3907_);
v___x_3929_ = lean_array_get(v___x_3906_, v_xs_3919_, v___x_3908_);
v___x_3930_ = lean_array_get_size(v_xs_3919_);
v___x_3931_ = l_Array_toSubarray___redArg(v_xs_3919_, v___x_3909_, v___x_3930_);
v___x_3932_ = l_Subarray_copy___redArg(v___x_3931_);
v___x_3933_ = 1;
v___x_3934_ = l_Lean_Meta_mkLambdaFVars(v___x_3932_, v_body_3920_, v___x_3910_, v___x_3911_, v___x_3910_, v___x_3911_, v___x_3933_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec_ref(v___x_3932_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3961_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3961_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3961_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 1);
lean_ctor_set(v___x_3937_, 0, v_00_u03b1_3912_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_00_u03b1_3912_);
v___x_3941_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_00_u03b2_3913_);
lean_inc(v___x_3928_);
v___x_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3928_);
lean_inc(v___x_3929_);
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3929_);
v___x_3945_ = lean_mk_empty_array_with_capacity(v___x_3914_);
v___x_3946_ = lean_array_push(v___x_3945_, v___x_3941_);
v___x_3947_ = lean_array_push(v___x_3946_, v___x_3942_);
v___x_3948_ = lean_array_push(v___x_3947_, v___x_3943_);
v___x_3949_ = lean_array_push(v___x_3948_, v___x_3944_);
v___x_3950_ = l_Lean_Meta_mkAppOptM(v___x_3939_, v___x_3949_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref(v___x_3950_);
v___x_3952_ = lean_box(v___x_3910_);
v___x_3953_ = lean_box(v___x_3911_);
v___x_3954_ = lean_box(v___x_3933_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3955_, 0, v___x_3929_);
lean_closure_set(v___f_3955_, 1, v_a_3935_);
lean_closure_set(v___f_3955_, 2, v_k_3915_);
lean_closure_set(v___f_3955_, 3, v___x_3916_);
lean_closure_set(v___f_3955_, 4, v___x_3928_);
lean_closure_set(v___f_3955_, 5, v___x_3952_);
lean_closure_set(v___f_3955_, 6, v___x_3953_);
lean_closure_set(v___f_3955_, 7, v___x_3954_);
v___x_3956_ = l_Lean_LocalDecl_type(v_a_3917_);
v___x_3957_ = l_Lean_Expr_replaceFVar(v___x_3956_, v_x_3918_, v_a_3951_);
lean_dec(v_a_3951_);
lean_dec_ref(v___x_3956_);
v___x_3958_ = l_Lean_LocalDecl_userName(v_a_3917_);
v___x_3959_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3958_, v___x_3957_, v___f_3955_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
return v___x_3959_;
}
else
{
lean_dec(v_a_3935_);
lean_dec(v___x_3929_);
lean_dec(v___x_3928_);
lean_dec_ref(v_x_3918_);
lean_dec(v___x_3916_);
lean_dec_ref(v_k_3915_);
return v___x_3950_;
}
}
}
}
else
{
lean_dec(v___x_3929_);
lean_dec(v___x_3928_);
lean_dec_ref(v_x_3918_);
lean_dec(v___x_3916_);
lean_dec_ref(v_k_3915_);
lean_dec_ref(v_00_u03b2_3913_);
lean_dec_ref(v_00_u03b1_3912_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3962_ = _args[0];
lean_object* v___x_3963_ = _args[1];
lean_object* v___x_3964_ = _args[2];
lean_object* v___x_3965_ = _args[3];
lean_object* v___x_3966_ = _args[4];
lean_object* v___x_3967_ = _args[5];
lean_object* v_00_u03b1_3968_ = _args[6];
lean_object* v_00_u03b2_3969_ = _args[7];
lean_object* v___x_3970_ = _args[8];
lean_object* v_k_3971_ = _args[9];
lean_object* v___x_3972_ = _args[10];
lean_object* v_a_3973_ = _args[11];
lean_object* v_x_3974_ = _args[12];
lean_object* v_xs_3975_ = _args[13];
lean_object* v_body_3976_ = _args[14];
lean_object* v___y_3977_ = _args[15];
lean_object* v___y_3978_ = _args[16];
lean_object* v___y_3979_ = _args[17];
lean_object* v___y_3980_ = _args[18];
lean_object* v___y_3981_ = _args[19];
lean_object* v___y_3982_ = _args[20];
lean_object* v___y_3983_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_3984_; uint8_t v___x_4070__boxed_3985_; lean_object* v_res_3986_; 
v___x_4069__boxed_3984_ = lean_unbox(v___x_3966_);
v___x_4070__boxed_3985_ = lean_unbox(v___x_3967_);
v_res_3986_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3962_, v___x_3963_, v___x_3964_, v___x_3965_, v___x_4069__boxed_3984_, v___x_4070__boxed_3985_, v_00_u03b1_3968_, v_00_u03b2_3969_, v___x_3970_, v_k_3971_, v___x_3972_, v_a_3973_, v_x_3974_, v_xs_3975_, v_body_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v_a_3973_);
lean_dec(v___x_3970_);
lean_dec(v___x_3964_);
lean_dec(v___x_3963_);
lean_dec_ref(v___x_3962_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3990_, lean_object* v_F_3991_, lean_object* v_val_3992_, lean_object* v_k_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; uint8_t v___y_4011_; uint8_t v___x_4103_; 
v___x_4103_ = l_Lean_Expr_isFVar(v_x_3990_);
if (v___x_4103_ == 0)
{
v___y_4011_ = v___x_4103_;
goto v___jp_4010_;
}
else
{
lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4104_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4105_ = lean_unsigned_to_nat(5u);
v___x_4106_ = l_Lean_Expr_isAppOfArity(v_val_3992_, v___x_4104_, v___x_4105_);
v___y_4011_ = v___x_4106_;
goto v___jp_4010_;
}
v___jp_4001_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4009_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4008_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4009_;
}
v___jp_4010_:
{
if (v___y_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec_ref(v_x_3990_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
lean_inc(v_a_3995_);
lean_inc_ref(v_a_3994_);
v___x_4012_ = lean_apply_9(v_k_3993_, v_F_3991_, v_val_3992_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, lean_box(0));
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4013_ = lean_unsigned_to_nat(3u);
v___x_4014_ = l_Lean_Expr_getAppNumArgs(v_val_3992_);
v___x_4015_ = lean_nat_sub(v___x_4014_, v___x_4013_);
v___x_4016_ = lean_unsigned_to_nat(1u);
v___x_4017_ = lean_nat_sub(v___x_4015_, v___x_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = l_Lean_Expr_getRevArg_x21(v_val_3992_, v___x_4017_);
v___x_4019_ = lean_expr_eqv(v___x_4018_, v_x_3990_);
lean_dec_ref(v___x_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
lean_dec(v___x_4014_);
lean_dec_ref(v_x_3990_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
lean_inc(v_a_3995_);
lean_inc_ref(v_a_3994_);
v___x_4020_ = lean_apply_9(v_k_3993_, v_F_3991_, v_val_3992_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, lean_box(0));
return v___x_4020_;
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4021_ = lean_unsigned_to_nat(4u);
v___x_4022_ = lean_nat_sub(v___x_4014_, v___x_4021_);
v___x_4023_ = lean_nat_sub(v___x_4022_, v___x_4016_);
lean_dec(v___x_4022_);
v___x_4024_ = l_Lean_Expr_getRevArg_x21(v_val_3992_, v___x_4023_);
v___x_4025_ = l_Lean_Expr_isLambda(v___x_4024_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
lean_dec_ref(v___x_4024_);
lean_dec(v___x_4014_);
lean_dec_ref(v_x_3990_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
lean_inc(v_a_3995_);
lean_inc_ref(v_a_3994_);
v___x_4026_ = lean_apply_9(v_k_3993_, v_F_3991_, v_val_3992_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, lean_box(0));
return v___x_4026_;
}
else
{
lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4027_ = l_Lean_Expr_bindingBody_x21(v___x_4024_);
lean_dec_ref(v___x_4024_);
v___x_4028_ = l_Lean_Expr_isLambda(v___x_4027_);
lean_dec_ref(v___x_4027_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; 
lean_dec(v___x_4014_);
lean_dec_ref(v_x_3990_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
lean_inc(v_a_3995_);
lean_inc_ref(v_a_3994_);
v___x_4029_ = lean_apply_9(v_k_3993_, v_F_3991_, v_val_3992_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, lean_box(0));
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = l_Lean_Expr_getAppFn(v_val_3992_);
v___x_4031_ = l_Lean_Expr_constLevels_x21(v___x_4030_);
lean_dec_ref(v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 1)
{
lean_object* v_tail_4032_; 
v_tail_4032_ = lean_ctor_get(v___x_4031_, 1);
lean_inc(v_tail_4032_);
lean_dec_ref(v___x_4031_);
if (lean_obj_tag(v_tail_4032_) == 1)
{
lean_object* v_tail_4033_; 
v_tail_4033_ = lean_ctor_get(v_tail_4032_, 1);
lean_inc(v_tail_4033_);
if (lean_obj_tag(v_tail_4033_) == 1)
{
lean_object* v_tail_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4101_; 
v_tail_4034_ = lean_ctor_get(v_tail_4033_, 1);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_tail_4033_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v_tail_4033_, 0);
lean_dec(v_unused_4102_);
v___x_4036_ = v_tail_4033_;
v_isShared_4037_ = v_isSharedCheck_4101_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_tail_4034_);
lean_dec(v_tail_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4101_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
if (lean_obj_tag(v_tail_4034_) == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = l_Lean_Expr_fvarId_x21(v_F_3991_);
v___x_4039_ = l_Lean_FVarId_getDecl___redArg(v___x_4038_, v_a_3996_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; lean_object* v_dummy_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v_args_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___f_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc_n(v_a_4040_, 2);
lean_dec_ref(v___x_4039_);
v___x_4041_ = l_Lean_instInhabitedExpr;
v_dummy_4042_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_4014_);
v___x_4043_ = lean_mk_array(v___x_4014_, v_dummy_4042_);
v___x_4044_ = lean_nat_sub(v___x_4014_, v___x_4016_);
lean_dec(v___x_4014_);
v_args_4045_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3992_, v___x_4043_, v___x_4044_);
v___x_4046_ = lean_unsigned_to_nat(0u);
v___x_4047_ = lean_box(v___x_4025_);
lean_inc_ref(v_x_3990_);
v___f_4048_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4048_, 0, v_a_4040_);
lean_closure_set(v___f_4048_, 1, v___x_4041_);
lean_closure_set(v___f_4048_, 2, v___x_4046_);
lean_closure_set(v___f_4048_, 3, v_x_3990_);
lean_closure_set(v___f_4048_, 4, v___x_4047_);
v___x_4049_ = lean_unsigned_to_nat(2u);
v___x_4050_ = lean_array_get(v___x_4041_, v_args_4045_, v___x_4049_);
v___x_4051_ = 0;
v___x_4052_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4050_, v___f_4048_, v___x_4051_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v_fst_4054_; lean_object* v_snd_4055_; lean_object* v_00_u03b1_4056_; lean_object* v_00_u03b2_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___f_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref(v___x_4052_);
v_fst_4054_ = lean_ctor_get(v_a_4053_, 0);
lean_inc(v_fst_4054_);
v_snd_4055_ = lean_ctor_get(v_a_4053_, 1);
lean_inc(v_snd_4055_);
lean_dec(v_a_4053_);
v_00_u03b1_4056_ = lean_array_get(v___x_4041_, v_args_4045_, v___x_4046_);
v_00_u03b2_4057_ = lean_array_get(v___x_4041_, v_args_4045_, v___x_4016_);
v___x_4058_ = lean_box(v___x_4051_);
v___x_4059_ = lean_box(v___x_4025_);
lean_inc_ref(v_x_3990_);
lean_inc(v_00_u03b2_4057_);
lean_inc(v_00_u03b1_4056_);
v___f_4060_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4060_, 0, v___x_4041_);
lean_closure_set(v___f_4060_, 1, v___x_4046_);
lean_closure_set(v___f_4060_, 2, v___x_4016_);
lean_closure_set(v___f_4060_, 3, v___x_4049_);
lean_closure_set(v___f_4060_, 4, v___x_4058_);
lean_closure_set(v___f_4060_, 5, v___x_4059_);
lean_closure_set(v___f_4060_, 6, v_00_u03b1_4056_);
lean_closure_set(v___f_4060_, 7, v_00_u03b2_4057_);
lean_closure_set(v___f_4060_, 8, v___x_4021_);
lean_closure_set(v___f_4060_, 9, v_k_3993_);
lean_closure_set(v___f_4060_, 10, v___x_4013_);
lean_closure_set(v___f_4060_, 11, v_a_4040_);
lean_closure_set(v___f_4060_, 12, v_x_3990_);
v___x_4061_ = lean_array_get(v___x_4041_, v_args_4045_, v___x_4021_);
lean_dec_ref(v_args_4045_);
v___x_4062_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4061_, v___f_4060_, v___x_4051_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4084_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4084_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4084_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v_tail_4032_);
lean_ctor_set(v___x_4036_, 0, v_snd_4055_);
v___x_4069_ = v___x_4036_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_snd_4055_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_tail_4032_);
v___x_4069_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4070_ = l_Lean_mkConst(v___x_4067_, v___x_4069_);
v___x_4071_ = lean_unsigned_to_nat(6u);
v___x_4072_ = lean_mk_empty_array_with_capacity(v___x_4071_);
v___x_4073_ = lean_array_push(v___x_4072_, v_00_u03b1_4056_);
v___x_4074_ = lean_array_push(v___x_4073_, v_00_u03b2_4057_);
v___x_4075_ = lean_array_push(v___x_4074_, v_fst_4054_);
v___x_4076_ = lean_array_push(v___x_4075_, v_x_3990_);
v___x_4077_ = lean_array_push(v___x_4076_, v_a_4063_);
v___x_4078_ = lean_array_push(v___x_4077_, v_F_3991_);
v___x_4079_ = l_Lean_mkAppN(v___x_4070_, v___x_4078_);
lean_dec_ref(v___x_4078_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 0, v___x_4079_);
v___x_4081_ = v___x_4065_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4057_);
lean_dec(v_00_u03b1_4056_);
lean_dec(v_snd_4055_);
lean_dec(v_fst_4054_);
lean_del_object(v___x_4036_);
lean_dec_ref(v_tail_4032_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
return v___x_4062_;
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v_args_4045_);
lean_dec(v_a_4040_);
lean_del_object(v___x_4036_);
lean_dec_ref(v_tail_4032_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v_a_4085_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4052_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4052_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_del_object(v___x_4036_);
lean_dec_ref(v_tail_4032_);
lean_dec(v___x_4014_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_val_3992_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v_a_4093_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4039_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4039_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
else
{
lean_del_object(v___x_4036_);
lean_dec(v_tail_4034_);
lean_dec_ref(v_tail_4032_);
lean_dec(v___x_4014_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_val_3992_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v___y_4002_ = v_a_3994_;
v___y_4003_ = v_a_3995_;
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
goto v___jp_4001_;
}
}
}
else
{
lean_dec(v_tail_4033_);
lean_dec_ref(v_tail_4032_);
lean_dec(v___x_4014_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_val_3992_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v___y_4002_ = v_a_3994_;
v___y_4003_ = v_a_3995_;
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
goto v___jp_4001_;
}
}
else
{
lean_dec(v_tail_4032_);
lean_dec(v___x_4014_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_val_3992_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v___y_4002_ = v_a_3994_;
v___y_4003_ = v_a_3995_;
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
goto v___jp_4001_;
}
}
else
{
lean_dec(v___x_4031_);
lean_dec(v___x_4014_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_val_3992_);
lean_dec_ref(v_F_3991_);
lean_dec_ref(v_x_3990_);
v___y_4002_ = v_a_3994_;
v___y_4003_ = v_a_3995_;
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
goto v___jp_4001_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4107_, lean_object* v_a_4108_, lean_object* v_k_4109_, lean_object* v___x_4110_, lean_object* v___x_4111_, uint8_t v___x_4112_, uint8_t v___x_4113_, uint8_t v___x_4114_, lean_object* v_FNew_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
lean_inc_ref(v_FNew_4115_);
lean_inc_ref(v___x_4107_);
v___x_4123_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4107_, v_FNew_4115_, v_a_4108_, v_k_4109_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref(v___x_4123_);
v___x_4125_ = lean_mk_empty_array_with_capacity(v___x_4110_);
v___x_4126_ = lean_array_push(v___x_4125_, v___x_4111_);
v___x_4127_ = lean_array_push(v___x_4126_, v___x_4107_);
v___x_4128_ = lean_array_push(v___x_4127_, v_FNew_4115_);
v___x_4129_ = l_Lean_Meta_mkLambdaFVars(v___x_4128_, v_a_4124_, v___x_4112_, v___x_4113_, v___x_4112_, v___x_4113_, v___x_4114_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec_ref(v___x_4128_);
return v___x_4129_;
}
else
{
lean_dec_ref(v_FNew_4115_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4107_);
return v___x_4123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4130_, lean_object* v_F_4131_, lean_object* v_val_4132_, lean_object* v_k_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4130_, v_F_4131_, v_val_4132_, v_k_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_ref_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref(v___x_4155_);
v_ref_4156_ = lean_ctor_get(v___y_4152_, 5);
v___x_4157_ = 0;
v___x_4158_ = l_Lean_SourceInfo_fromRef(v_ref_4156_, v___x_4157_);
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4160_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4158_);
v___x_4161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4158_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_Syntax_node1(v___x_4158_, v___x_4159_, v___x_4161_);
v___x_4163_ = l_Lean_Elab_Tactic_evalTactic(v___x_4162_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v___x_4163_;
}
else
{
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v___f_4183_; lean_object* v___x_4184_; 
v___f_4183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4184_ = l_Lean_Elab_Tactic_run(v_mvarId_4175_, v___f_4183_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4195_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4187_ = v___x_4184_;
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4184_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
uint8_t v___x_4189_; 
v___x_4189_ = l_List_isEmpty___redArg(v_a_4185_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; 
lean_del_object(v___x_4187_);
v___x_4190_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4185_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4190_;
}
else
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
lean_dec(v_a_4185_);
v___x_4191_ = lean_box(0);
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 0, v___x_4191_);
v___x_4193_ = v___x_4187_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
v_a_4196_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4184_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4184_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4213_, lean_object* v_x_4214_, lean_object* v_x_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_ks_4217_; lean_object* v_vs_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4242_; 
v_ks_4217_ = lean_ctor_get(v_x_4213_, 0);
v_vs_4218_ = lean_ctor_get(v_x_4213_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4213_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4220_ = v_x_4213_;
v_isShared_4221_ = v_isSharedCheck_4242_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_vs_4218_);
lean_inc(v_ks_4217_);
lean_dec(v_x_4213_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4242_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; uint8_t v___x_4223_; 
v___x_4222_ = lean_array_get_size(v_ks_4217_);
v___x_4223_ = lean_nat_dec_lt(v_x_4214_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4227_; 
lean_dec(v_x_4214_);
v___x_4224_ = lean_array_push(v_ks_4217_, v_x_4215_);
v___x_4225_ = lean_array_push(v_vs_4218_, v_x_4216_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v___x_4225_);
lean_ctor_set(v___x_4220_, 0, v___x_4224_);
v___x_4227_ = v___x_4220_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
else
{
lean_object* v_k_x27_4229_; uint8_t v___x_4230_; 
v_k_x27_4229_ = lean_array_fget_borrowed(v_ks_4217_, v_x_4214_);
v___x_4230_ = l_Lean_instBEqMVarId_beq(v_x_4215_, v_k_x27_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4232_; 
if (v_isShared_4221_ == 0)
{
v___x_4232_ = v___x_4220_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_ks_4217_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_vs_4218_);
v___x_4232_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_nat_add(v_x_4214_, v___x_4233_);
lean_dec(v_x_4214_);
v_x_4213_ = v___x_4232_;
v_x_4214_ = v___x_4234_;
goto _start;
}
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4237_ = lean_array_fset(v_ks_4217_, v_x_4214_, v_x_4215_);
v___x_4238_ = lean_array_fset(v_vs_4218_, v_x_4214_, v_x_4216_);
lean_dec(v_x_4214_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v___x_4238_);
lean_ctor_set(v___x_4220_, 0, v___x_4237_);
v___x_4240_ = v___x_4220_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4243_, lean_object* v_k_4244_, lean_object* v_v_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = lean_unsigned_to_nat(0u);
v___x_4247_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4243_, v___x_4246_, v_k_4244_, v_v_4245_);
return v___x_4247_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4248_; size_t v___x_4249_; size_t v___x_4250_; 
v___x_4248_ = ((size_t)5ULL);
v___x_4249_ = ((size_t)1ULL);
v___x_4250_ = lean_usize_shift_left(v___x_4249_, v___x_4248_);
return v___x_4250_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4251_; size_t v___x_4252_; size_t v___x_4253_; 
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4253_ = lean_usize_sub(v___x_4252_, v___x_4251_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4255_, size_t v_x_4256_, size_t v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_){
_start:
{
if (lean_obj_tag(v_x_4255_) == 0)
{
lean_object* v_es_4260_; size_t v___x_4261_; size_t v___x_4262_; size_t v___x_4263_; size_t v___x_4264_; lean_object* v_j_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v_es_4260_ = lean_ctor_get(v_x_4255_, 0);
v___x_4261_ = ((size_t)5ULL);
v___x_4262_ = ((size_t)1ULL);
v___x_4263_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4264_ = lean_usize_land(v_x_4256_, v___x_4263_);
v_j_4265_ = lean_usize_to_nat(v___x_4264_);
v___x_4266_ = lean_array_get_size(v_es_4260_);
v___x_4267_ = lean_nat_dec_lt(v_j_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
lean_dec(v_j_4265_);
lean_dec(v_x_4259_);
lean_dec(v_x_4258_);
return v_x_4255_;
}
else
{
lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4304_; 
lean_inc_ref(v_es_4260_);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; 
v_unused_4305_ = lean_ctor_get(v_x_4255_, 0);
lean_dec(v_unused_4305_);
v___x_4269_ = v_x_4255_;
v_isShared_4270_ = v_isSharedCheck_4304_;
goto v_resetjp_4268_;
}
else
{
lean_dec(v_x_4255_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4304_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v_v_4271_; lean_object* v___x_4272_; lean_object* v_xs_x27_4273_; lean_object* v___y_4275_; 
v_v_4271_ = lean_array_fget(v_es_4260_, v_j_4265_);
v___x_4272_ = lean_box(0);
v_xs_x27_4273_ = lean_array_fset(v_es_4260_, v_j_4265_, v___x_4272_);
switch(lean_obj_tag(v_v_4271_))
{
case 0:
{
lean_object* v_key_4280_; lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4291_; 
v_key_4280_ = lean_ctor_get(v_v_4271_, 0);
v_val_4281_ = lean_ctor_get(v_v_4271_, 1);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_v_4271_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4283_ = v_v_4271_;
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_inc(v_key_4280_);
lean_dec(v_v_4271_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
uint8_t v___x_4285_; 
v___x_4285_ = l_Lean_instBEqMVarId_beq(v_x_4258_, v_key_4280_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_del_object(v___x_4283_);
v___x_4286_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4280_, v_val_4281_, v_x_4258_, v_x_4259_);
v___x_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
v___y_4275_ = v___x_4287_;
goto v___jp_4274_;
}
else
{
lean_object* v___x_4289_; 
lean_dec(v_val_4281_);
lean_dec(v_key_4280_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 1, v_x_4259_);
lean_ctor_set(v___x_4283_, 0, v_x_4258_);
v___x_4289_ = v___x_4283_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_x_4258_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v_x_4259_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
v___y_4275_ = v___x_4289_;
goto v___jp_4274_;
}
}
}
}
case 1:
{
lean_object* v_node_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4302_; 
v_node_4292_ = lean_ctor_get(v_v_4271_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_v_4271_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4294_ = v_v_4271_;
v_isShared_4295_ = v_isSharedCheck_4302_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_node_4292_);
lean_dec(v_v_4271_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4302_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4296_ = lean_usize_shift_right(v_x_4256_, v___x_4261_);
v___x_4297_ = lean_usize_add(v_x_4257_, v___x_4262_);
v___x_4298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4292_, v___x_4296_, v___x_4297_, v_x_4258_, v_x_4259_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4298_);
v___x_4300_ = v___x_4294_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
v___y_4275_ = v___x_4300_;
goto v___jp_4274_;
}
}
}
default: 
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v_x_4258_);
lean_ctor_set(v___x_4303_, 1, v_x_4259_);
v___y_4275_ = v___x_4303_;
goto v___jp_4274_;
}
}
v___jp_4274_:
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = lean_array_fset(v_xs_x27_4273_, v_j_4265_, v___y_4275_);
lean_dec(v_j_4265_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4276_);
v___x_4278_ = v___x_4269_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
else
{
lean_object* v_ks_4306_; lean_object* v_vs_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4327_; 
v_ks_4306_ = lean_ctor_get(v_x_4255_, 0);
v_vs_4307_ = lean_ctor_get(v_x_4255_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4309_ = v_x_4255_;
v_isShared_4310_ = v_isSharedCheck_4327_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_vs_4307_);
lean_inc(v_ks_4306_);
lean_dec(v_x_4255_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4327_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_ks_4306_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_vs_4307_);
v___x_4312_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v_newNode_4313_; uint8_t v___y_4315_; size_t v___x_4321_; uint8_t v___x_4322_; 
v_newNode_4313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4312_, v_x_4258_, v_x_4259_);
v___x_4321_ = ((size_t)7ULL);
v___x_4322_ = lean_usize_dec_le(v___x_4321_, v_x_4257_);
if (v___x_4322_ == 0)
{
lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4323_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4313_);
v___x_4324_ = lean_unsigned_to_nat(4u);
v___x_4325_ = lean_nat_dec_lt(v___x_4323_, v___x_4324_);
lean_dec(v___x_4323_);
v___y_4315_ = v___x_4325_;
goto v___jp_4314_;
}
else
{
v___y_4315_ = v___x_4322_;
goto v___jp_4314_;
}
v___jp_4314_:
{
if (v___y_4315_ == 0)
{
lean_object* v_ks_4316_; lean_object* v_vs_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_ks_4316_ = lean_ctor_get(v_newNode_4313_, 0);
lean_inc_ref(v_ks_4316_);
v_vs_4317_ = lean_ctor_get(v_newNode_4313_, 1);
lean_inc_ref(v_vs_4317_);
lean_dec_ref(v_newNode_4313_);
v___x_4318_ = lean_unsigned_to_nat(0u);
v___x_4319_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_4320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4257_, v_ks_4316_, v_vs_4317_, v___x_4318_, v___x_4319_);
lean_dec_ref(v_vs_4317_);
lean_dec_ref(v_ks_4316_);
return v___x_4320_;
}
else
{
return v_newNode_4313_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4328_, lean_object* v_keys_4329_, lean_object* v_vals_4330_, lean_object* v_i_4331_, lean_object* v_entries_4332_){
_start:
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = lean_array_get_size(v_keys_4329_);
v___x_4334_ = lean_nat_dec_lt(v_i_4331_, v___x_4333_);
if (v___x_4334_ == 0)
{
lean_dec(v_i_4331_);
return v_entries_4332_;
}
else
{
lean_object* v_k_4335_; lean_object* v_v_4336_; uint64_t v___x_4337_; size_t v_h_4338_; size_t v___x_4339_; lean_object* v___x_4340_; size_t v___x_4341_; size_t v___x_4342_; size_t v___x_4343_; size_t v_h_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_k_4335_ = lean_array_fget_borrowed(v_keys_4329_, v_i_4331_);
v_v_4336_ = lean_array_fget_borrowed(v_vals_4330_, v_i_4331_);
v___x_4337_ = l_Lean_instHashableMVarId_hash(v_k_4335_);
v_h_4338_ = lean_uint64_to_usize(v___x_4337_);
v___x_4339_ = ((size_t)5ULL);
v___x_4340_ = lean_unsigned_to_nat(1u);
v___x_4341_ = ((size_t)1ULL);
v___x_4342_ = lean_usize_sub(v_depth_4328_, v___x_4341_);
v___x_4343_ = lean_usize_mul(v___x_4339_, v___x_4342_);
v_h_4344_ = lean_usize_shift_right(v_h_4338_, v___x_4343_);
v___x_4345_ = lean_nat_add(v_i_4331_, v___x_4340_);
lean_dec(v_i_4331_);
lean_inc(v_v_4336_);
lean_inc(v_k_4335_);
v___x_4346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4332_, v_h_4344_, v_depth_4328_, v_k_4335_, v_v_4336_);
v_i_4331_ = v___x_4345_;
v_entries_4332_ = v___x_4346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4348_, lean_object* v_keys_4349_, lean_object* v_vals_4350_, lean_object* v_i_4351_, lean_object* v_entries_4352_){
_start:
{
size_t v_depth_boxed_4353_; lean_object* v_res_4354_; 
v_depth_boxed_4353_ = lean_unbox_usize(v_depth_4348_);
lean_dec(v_depth_4348_);
v_res_4354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4353_, v_keys_4349_, v_vals_4350_, v_i_4351_, v_entries_4352_);
lean_dec_ref(v_vals_4350_);
lean_dec_ref(v_keys_4349_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4355_, lean_object* v_x_4356_, lean_object* v_x_4357_, lean_object* v_x_4358_, lean_object* v_x_4359_){
_start:
{
size_t v_x_4261__boxed_4360_; size_t v_x_4262__boxed_4361_; lean_object* v_res_4362_; 
v_x_4261__boxed_4360_ = lean_unbox_usize(v_x_4356_);
lean_dec(v_x_4356_);
v_x_4262__boxed_4361_ = lean_unbox_usize(v_x_4357_);
lean_dec(v_x_4357_);
v_res_4362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4355_, v_x_4261__boxed_4360_, v_x_4262__boxed_4361_, v_x_4358_, v_x_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4363_, lean_object* v_x_4364_, lean_object* v_x_4365_){
_start:
{
uint64_t v___x_4366_; size_t v___x_4367_; size_t v___x_4368_; lean_object* v___x_4369_; 
v___x_4366_ = l_Lean_instHashableMVarId_hash(v_x_4364_);
v___x_4367_ = lean_uint64_to_usize(v___x_4366_);
v___x_4368_ = ((size_t)1ULL);
v___x_4369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4363_, v___x_4367_, v___x_4368_, v_x_4364_, v_x_4365_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4370_, lean_object* v_val_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v_mctx_4375_; lean_object* v_cache_4376_; lean_object* v_zetaDeltaFVarIds_4377_; lean_object* v_postponed_4378_; lean_object* v_diag_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4407_; 
v___x_4374_ = lean_st_ref_take(v___y_4372_);
v_mctx_4375_ = lean_ctor_get(v___x_4374_, 0);
v_cache_4376_ = lean_ctor_get(v___x_4374_, 1);
v_zetaDeltaFVarIds_4377_ = lean_ctor_get(v___x_4374_, 2);
v_postponed_4378_ = lean_ctor_get(v___x_4374_, 3);
v_diag_4379_ = lean_ctor_get(v___x_4374_, 4);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4381_ = v___x_4374_;
v_isShared_4382_ = v_isSharedCheck_4407_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_diag_4379_);
lean_inc(v_postponed_4378_);
lean_inc(v_zetaDeltaFVarIds_4377_);
lean_inc(v_cache_4376_);
lean_inc(v_mctx_4375_);
lean_dec(v___x_4374_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4407_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v_depth_4383_; lean_object* v_levelAssignDepth_4384_; lean_object* v_lmvarCounter_4385_; lean_object* v_mvarCounter_4386_; lean_object* v_lDecls_4387_; lean_object* v_decls_4388_; lean_object* v_userNames_4389_; lean_object* v_lAssignment_4390_; lean_object* v_eAssignment_4391_; lean_object* v_dAssignment_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4406_; 
v_depth_4383_ = lean_ctor_get(v_mctx_4375_, 0);
v_levelAssignDepth_4384_ = lean_ctor_get(v_mctx_4375_, 1);
v_lmvarCounter_4385_ = lean_ctor_get(v_mctx_4375_, 2);
v_mvarCounter_4386_ = lean_ctor_get(v_mctx_4375_, 3);
v_lDecls_4387_ = lean_ctor_get(v_mctx_4375_, 4);
v_decls_4388_ = lean_ctor_get(v_mctx_4375_, 5);
v_userNames_4389_ = lean_ctor_get(v_mctx_4375_, 6);
v_lAssignment_4390_ = lean_ctor_get(v_mctx_4375_, 7);
v_eAssignment_4391_ = lean_ctor_get(v_mctx_4375_, 8);
v_dAssignment_4392_ = lean_ctor_get(v_mctx_4375_, 9);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_mctx_4375_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4394_ = v_mctx_4375_;
v_isShared_4395_ = v_isSharedCheck_4406_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_dAssignment_4392_);
lean_inc(v_eAssignment_4391_);
lean_inc(v_lAssignment_4390_);
lean_inc(v_userNames_4389_);
lean_inc(v_decls_4388_);
lean_inc(v_lDecls_4387_);
lean_inc(v_mvarCounter_4386_);
lean_inc(v_lmvarCounter_4385_);
lean_inc(v_levelAssignDepth_4384_);
lean_inc(v_depth_4383_);
lean_dec(v_mctx_4375_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4406_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4396_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4391_, v_mvarId_4370_, v_val_4371_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 8, v___x_4396_);
v___x_4398_ = v___x_4394_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_depth_4383_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_levelAssignDepth_4384_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_lmvarCounter_4385_);
lean_ctor_set(v_reuseFailAlloc_4405_, 3, v_mvarCounter_4386_);
lean_ctor_set(v_reuseFailAlloc_4405_, 4, v_lDecls_4387_);
lean_ctor_set(v_reuseFailAlloc_4405_, 5, v_decls_4388_);
lean_ctor_set(v_reuseFailAlloc_4405_, 6, v_userNames_4389_);
lean_ctor_set(v_reuseFailAlloc_4405_, 7, v_lAssignment_4390_);
lean_ctor_set(v_reuseFailAlloc_4405_, 8, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4405_, 9, v_dAssignment_4392_);
v___x_4398_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4400_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4398_);
v___x_4400_ = v___x_4381_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_cache_4376_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_zetaDeltaFVarIds_4377_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_postponed_4378_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_diag_4379_);
v___x_4400_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4401_ = lean_st_ref_set(v___y_4372_, v___x_4400_);
v___x_4402_ = lean_box(0);
v___x_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4402_);
return v___x_4403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4408_, lean_object* v_val_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4408_, v_val_4409_, v___y_4410_);
lean_dec(v___y_4410_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4417_, lean_object* v_mv_u2082_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4427_; 
lean_inc(v_mv_u2081_4417_);
v___x_4427_ = l_Lean_MVarId_getDecl(v_mv_u2081_4417_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref(v___x_4427_);
lean_inc(v_mv_u2082_4418_);
v___x_4429_ = l_Lean_MVarId_getDecl(v_mv_u2082_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v_lctx_4431_; lean_object* v_type_4432_; lean_object* v_lctx_4433_; lean_object* v_type_4434_; uint8_t v___x_4435_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref(v___x_4429_);
v_lctx_4431_ = lean_ctor_get(v_a_4428_, 1);
lean_inc_ref(v_lctx_4431_);
v_type_4432_ = lean_ctor_get(v_a_4428_, 2);
lean_inc_ref(v_type_4432_);
lean_dec(v_a_4428_);
v_lctx_4433_ = lean_ctor_get(v_a_4430_, 1);
lean_inc_ref(v_lctx_4433_);
v_type_4434_ = lean_ctor_get(v_a_4430_, 2);
lean_inc_ref(v_type_4434_);
lean_dec(v_a_4430_);
v___x_4435_ = lean_expr_eqv(v_type_4432_, v_type_4434_);
lean_dec_ref(v_type_4434_);
lean_dec_ref(v_type_4432_);
if (v___x_4435_ == 0)
{
lean_dec_ref(v_lctx_4433_);
lean_dec_ref(v_lctx_4431_);
lean_dec(v_mv_u2082_4418_);
lean_dec(v_mv_u2081_4417_);
goto v___jp_4424_;
}
else
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4437_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4431_, v_lctx_4433_, v___x_4436_);
if (v___x_4437_ == 0)
{
uint8_t v___x_4438_; 
v___x_4438_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4433_, v_lctx_4431_, v___x_4436_);
lean_dec_ref(v_lctx_4431_);
lean_dec_ref(v_lctx_4433_);
if (v___x_4438_ == 0)
{
lean_dec(v_mv_u2082_4418_);
lean_dec(v_mv_u2081_4417_);
goto v___jp_4424_;
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4450_; 
v___x_4439_ = l_Lean_Expr_mvar___override(v_mv_u2082_4418_);
v___x_4440_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4417_, v___x_4439_, v___y_4420_);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4450_ == 0)
{
lean_object* v_unused_4451_; 
v_unused_4451_ = lean_ctor_get(v___x_4440_, 0);
lean_dec(v_unused_4451_);
v___x_4442_ = v___x_4440_;
v_isShared_4443_ = v_isSharedCheck_4450_;
goto v_resetjp_4441_;
}
else
{
lean_dec(v___x_4440_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4450_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4444_ = lean_box(v___x_4437_);
v___x_4445_ = lean_box(v___x_4435_);
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4444_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4446_);
v___x_4448_ = v___x_4442_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4464_; 
lean_dec_ref(v_lctx_4433_);
lean_dec_ref(v_lctx_4431_);
v___x_4452_ = l_Lean_Expr_mvar___override(v_mv_u2081_4417_);
v___x_4453_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4418_, v___x_4452_, v___y_4420_);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v___x_4453_, 0);
lean_dec(v_unused_4465_);
v___x_4455_ = v___x_4453_;
v_isShared_4456_ = v_isSharedCheck_4464_;
goto v_resetjp_4454_;
}
else
{
lean_dec(v___x_4453_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4464_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
uint8_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4457_ = 0;
v___x_4458_ = lean_box(v___x_4435_);
v___x_4459_ = lean_box(v___x_4457_);
v___x_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4460_);
v___x_4462_ = v___x_4455_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_dec(v_a_4428_);
lean_dec(v_mv_u2082_4418_);
lean_dec(v_mv_u2081_4417_);
v_a_4466_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4429_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4429_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_mv_u2082_4418_);
lean_dec(v_mv_u2081_4417_);
v_a_4474_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4427_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4427_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
v___jp_4424_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4482_, lean_object* v_mv_u2082_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4482_, v_mv_u2082_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4490_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4504_, lean_object* v_removed_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_b_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___y_4515_; uint8_t v___x_4538_; 
v___x_4538_ = lean_nat_dec_lt(v_a_4507_, v_upperBound_4504_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; 
lean_dec(v_a_4507_);
v___x_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_b_4508_);
return v___x_4539_;
}
else
{
uint8_t v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4540_ = 0;
v___x_4541_ = lean_box(v___x_4540_);
v___x_4542_ = lean_array_get(v___x_4541_, v_removed_4505_, v_a_4507_);
lean_dec(v___x_4541_);
v___x_4543_ = lean_unbox(v___x_4542_);
lean_dec(v___x_4542_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___f_4547_; 
v___x_4544_ = lean_array_fget_borrowed(v_a_4506_, v_a_4507_);
lean_inc(v___x_4544_);
v___x_4545_ = lean_array_push(v_b_4508_, v___x_4544_);
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
v___f_4547_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4547_, 0, v___x_4546_);
v___y_4515_ = v___f_4547_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4548_; lean_object* v___f_4549_; 
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_b_4508_);
v___f_4549_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4549_, 0, v___x_4548_);
v___y_4515_ = v___f_4549_;
goto v___jp_4514_;
}
}
v___jp_4514_:
{
lean_object* v___x_4516_; 
lean_inc(v___y_4512_);
lean_inc_ref(v___y_4511_);
lean_inc(v___y_4510_);
lean_inc_ref(v___y_4509_);
v___x_4516_ = lean_apply_5(v___y_4515_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, lean_box(0));
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4529_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4519_ = v___x_4516_;
v_isShared_4520_ = v_isSharedCheck_4529_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4516_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4529_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
if (lean_obj_tag(v_a_4517_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; 
lean_dec(v_a_4507_);
v_a_4521_ = lean_ctor_get(v_a_4517_, 0);
lean_inc(v_a_4521_);
lean_dec_ref(v_a_4517_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v_a_4521_);
v___x_4523_ = v___x_4519_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
lean_del_object(v___x_4519_);
v_a_4525_ = lean_ctor_get(v_a_4517_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v_a_4517_);
v___x_4526_ = lean_unsigned_to_nat(1u);
v___x_4527_ = lean_nat_add(v_a_4507_, v___x_4526_);
lean_dec(v_a_4507_);
v_a_4507_ = v___x_4527_;
v_b_4508_ = v_a_4525_;
goto _start;
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_a_4507_);
v_a_4530_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4516_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4516_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4550_, lean_object* v_removed_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_b_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4550_, v_removed_4551_, v_a_4552_, v_a_4553_, v_b_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec_ref(v_a_4552_);
lean_dec_ref(v_removed_4551_);
lean_dec(v_upperBound_4550_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4561_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4575_, lean_object* v___x_4576_, lean_object* v___x_4577_, lean_object* v___x_4578_, lean_object* v_a_4579_, uint8_t v___x_4580_, lean_object* v_snd_4581_, lean_object* v_fst_4582_, lean_object* v_next_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_apply_7(v_f_4575_, v___x_4576_, v___x_4577_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, lean_box(0));
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4625_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4625_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4625_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v_fst_4594_; lean_object* v_snd_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4624_; 
v_fst_4594_ = lean_ctor_get(v_a_4590_, 0);
v_snd_4595_ = lean_ctor_get(v_a_4590_, 1);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_a_4590_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4597_ = v_a_4590_;
v_isShared_4598_ = v_isSharedCheck_4624_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_snd_4595_);
lean_inc(v_fst_4594_);
lean_dec(v_a_4590_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4624_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v_removed_4600_; lean_object* v_numRemoved_4601_; uint8_t v___x_4620_; 
v___x_4620_ = lean_unbox(v_fst_4594_);
lean_dec(v_fst_4594_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = lean_nat_add(v_snd_4581_, v___x_4578_);
lean_dec(v_snd_4581_);
v___x_4622_ = lean_box(v___x_4580_);
v___x_4623_ = lean_array_set(v_fst_4582_, v_next_4583_, v___x_4622_);
v_removed_4600_ = v___x_4623_;
v_numRemoved_4601_ = v___x_4621_;
goto v___jp_4599_;
}
else
{
v_removed_4600_ = v_fst_4582_;
v_numRemoved_4601_ = v_snd_4581_;
goto v___jp_4599_;
}
v___jp_4599_:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_unbox(v_snd_4595_);
lean_dec(v_snd_4595_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4603_ = lean_nat_add(v_numRemoved_4601_, v___x_4578_);
lean_dec(v_numRemoved_4601_);
v___x_4604_ = lean_box(v___x_4580_);
v___x_4605_ = lean_array_set(v_removed_4600_, v_a_4579_, v___x_4604_);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 1, v___x_4603_);
lean_ctor_set(v___x_4597_, 0, v___x_4605_);
v___x_4607_ = v___x_4597_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v___x_4603_);
v___x_4607_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4610_; 
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4608_);
v___x_4610_ = v___x_4592_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4608_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
else
{
lean_object* v___x_4614_; 
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 1, v_numRemoved_4601_);
lean_ctor_set(v___x_4597_, 0, v_removed_4600_);
v___x_4614_ = v___x_4597_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_removed_4600_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v_numRemoved_4601_);
v___x_4614_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4615_);
v___x_4617_ = v___x_4592_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v_fst_4582_);
lean_dec(v_snd_4581_);
v_a_4626_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4589_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4589_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4634_, lean_object* v___x_4635_, lean_object* v___x_4636_, lean_object* v___x_4637_, lean_object* v_a_4638_, lean_object* v___x_4639_, lean_object* v_snd_4640_, lean_object* v_fst_4641_, lean_object* v_next_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
uint8_t v___x_4754__boxed_4648_; lean_object* v_res_4649_; 
v___x_4754__boxed_4648_ = lean_unbox(v___x_4639_);
v_res_4649_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4634_, v___x_4635_, v___x_4636_, v___x_4637_, v_a_4638_, v___x_4754__boxed_4648_, v_snd_4640_, v_fst_4641_, v_next_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
lean_dec(v_next_4642_);
lean_dec(v_a_4638_);
lean_dec(v___x_4637_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4650_, lean_object* v_a_4651_, lean_object* v_next_4652_, lean_object* v_f_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_nat_dec_lt(v_a_4654_, v_upperBound_4650_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
lean_dec(v_a_4654_);
lean_dec_ref(v_f_4653_);
lean_dec(v_next_4652_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_b_4655_);
return v___x_4662_;
}
else
{
lean_object* v_fst_4663_; lean_object* v_snd_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4711_; 
v_fst_4663_ = lean_ctor_get(v_b_4655_, 0);
v_snd_4664_ = lean_ctor_get(v_b_4655_, 1);
v_isSharedCheck_4711_ = !lean_is_exclusive(v_b_4655_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4666_ = v_b_4655_;
v_isShared_4667_ = v_isSharedCheck_4711_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_snd_4664_);
lean_inc(v_fst_4663_);
lean_dec(v_b_4655_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4711_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___y_4670_; uint8_t v___y_4693_; uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4668_ = lean_unsigned_to_nat(1u);
v___x_4703_ = 0;
v___x_4704_ = lean_box(v___x_4703_);
v___x_4705_ = lean_array_get(v___x_4704_, v_fst_4663_, v_next_4652_);
lean_dec(v___x_4704_);
v___x_4706_ = lean_unbox(v___x_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
lean_dec(v___x_4705_);
v___x_4707_ = lean_box(v___x_4703_);
v___x_4708_ = lean_array_get(v___x_4707_, v_fst_4663_, v_a_4654_);
lean_dec(v___x_4707_);
v___x_4709_ = lean_unbox(v___x_4708_);
lean_dec(v___x_4708_);
v___y_4693_ = v___x_4709_;
goto v___jp_4692_;
}
else
{
uint8_t v___x_4710_; 
v___x_4710_ = lean_unbox(v___x_4705_);
lean_dec(v___x_4705_);
v___y_4693_ = v___x_4710_;
goto v___jp_4692_;
}
v___jp_4669_:
{
lean_object* v___x_4671_; 
lean_inc(v___y_4659_);
lean_inc_ref(v___y_4658_);
lean_inc(v___y_4657_);
lean_inc_ref(v___y_4656_);
v___x_4671_ = lean_apply_5(v___y_4670_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, lean_box(0));
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4683_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4683_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4683_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
if (lean_obj_tag(v_a_4672_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; 
lean_dec(v_a_4654_);
lean_dec_ref(v_f_4653_);
lean_dec(v_next_4652_);
v_a_4676_ = lean_ctor_get(v_a_4672_, 0);
lean_inc(v_a_4676_);
lean_dec_ref(v_a_4672_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v_a_4676_);
v___x_4678_ = v___x_4674_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
lean_del_object(v___x_4674_);
v_a_4680_ = lean_ctor_get(v_a_4672_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v_a_4672_);
v___x_4681_ = lean_nat_add(v_a_4654_, v___x_4668_);
lean_dec(v_a_4654_);
v_a_4654_ = v___x_4681_;
v_b_4655_ = v_a_4680_;
goto _start;
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec(v_a_4654_);
lean_dec_ref(v_f_4653_);
lean_dec(v_next_4652_);
v_a_4684_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4671_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4671_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
v___jp_4692_:
{
if (v___y_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___f_4697_; 
lean_del_object(v___x_4666_);
v___x_4694_ = lean_array_fget_borrowed(v_a_4651_, v_next_4652_);
v___x_4695_ = lean_array_fget_borrowed(v_a_4651_, v_a_4654_);
v___x_4696_ = lean_box(v___x_4661_);
lean_inc(v_next_4652_);
lean_inc(v_a_4654_);
lean_inc(v___x_4695_);
lean_inc(v___x_4694_);
lean_inc_ref(v_f_4653_);
v___f_4697_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4697_, 0, v_f_4653_);
lean_closure_set(v___f_4697_, 1, v___x_4694_);
lean_closure_set(v___f_4697_, 2, v___x_4695_);
lean_closure_set(v___f_4697_, 3, v___x_4668_);
lean_closure_set(v___f_4697_, 4, v_a_4654_);
lean_closure_set(v___f_4697_, 5, v___x_4696_);
lean_closure_set(v___f_4697_, 6, v_snd_4664_);
lean_closure_set(v___f_4697_, 7, v_fst_4663_);
lean_closure_set(v___f_4697_, 8, v_next_4652_);
v___y_4670_ = v___f_4697_;
goto v___jp_4669_;
}
else
{
lean_object* v___x_4699_; 
if (v_isShared_4667_ == 0)
{
v___x_4699_ = v___x_4666_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_fst_4663_);
lean_ctor_set(v_reuseFailAlloc_4702_, 1, v_snd_4664_);
v___x_4699_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; lean_object* v___f_4701_; 
v___x_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
v___f_4701_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4701_, 0, v___x_4700_);
v___y_4670_ = v___f_4701_;
goto v___jp_4669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4712_, lean_object* v_a_4713_, lean_object* v_next_4714_, lean_object* v_f_4715_, lean_object* v_a_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4712_, v_a_4713_, v_next_4714_, v_f_4715_, v_a_4716_, v_b_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec_ref(v_a_4713_);
lean_dec(v_upperBound_4712_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4724_, lean_object* v___x_4725_, lean_object* v_a_4726_, lean_object* v_f_4727_, lean_object* v_a_4728_, lean_object* v_b_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
uint8_t v___x_4735_; 
v___x_4735_ = lean_nat_dec_lt(v_a_4728_, v_upperBound_4724_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec(v_a_4728_);
lean_dec_ref(v_f_4727_);
v___x_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_b_4729_);
return v___x_4736_;
}
else
{
lean_object* v_fst_4737_; lean_object* v_snd_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4759_; 
v_fst_4737_ = lean_ctor_get(v_b_4729_, 0);
v_snd_4738_ = lean_ctor_get(v_b_4729_, 1);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_b_4729_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4740_ = v_b_4729_;
v_isShared_4741_ = v_isSharedCheck_4759_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_snd_4738_);
lean_inc(v_fst_4737_);
lean_dec(v_b_4729_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4759_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4742_ = lean_unsigned_to_nat(1u);
v___x_4743_ = lean_nat_add(v_a_4728_, v___x_4742_);
if (v_isShared_4741_ == 0)
{
v___x_4745_ = v___x_4740_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_fst_4737_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_snd_4738_);
v___x_4745_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4746_; 
lean_inc(v___x_4743_);
lean_inc_ref(v_f_4727_);
v___x_4746_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4725_, v_a_4726_, v_a_4728_, v_f_4727_, v___x_4743_, v___x_4745_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v_fst_4748_; lean_object* v_snd_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4757_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc(v_a_4747_);
lean_dec_ref(v___x_4746_);
v_fst_4748_ = lean_ctor_get(v_a_4747_, 0);
v_snd_4749_ = lean_ctor_get(v_a_4747_, 1);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_a_4747_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4751_ = v_a_4747_;
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_snd_4749_);
lean_inc(v_fst_4748_);
lean_dec(v_a_4747_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_fst_4748_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_snd_4749_);
v___x_4754_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
v_a_4728_ = v___x_4743_;
v_b_4729_ = v___x_4754_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4743_);
lean_dec_ref(v_f_4727_);
return v___x_4746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4760_, lean_object* v___x_4761_, lean_object* v_a_4762_, lean_object* v_f_4763_, lean_object* v_a_4764_, lean_object* v_b_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4760_, v___x_4761_, v_a_4762_, v_f_4763_, v_a_4764_, v_b_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec_ref(v_a_4762_);
lean_dec(v___x_4761_);
lean_dec(v_upperBound_4760_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4772_, lean_object* v_f_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___x_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; lean_object* v_removed_4782_; lean_object* v_numRemoved_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4779_ = lean_array_get_size(v_a_4772_);
v___x_4780_ = 0;
v___x_4781_ = lean_box(v___x_4780_);
v_removed_4782_ = lean_mk_array(v___x_4779_, v___x_4781_);
v_numRemoved_4783_ = lean_unsigned_to_nat(0u);
v___x_4784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4784_, 0, v_removed_4782_);
lean_ctor_set(v___x_4784_, 1, v_numRemoved_4783_);
v___x_4785_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4779_, v___x_4779_, v_a_4772_, v_f_4773_, v_numRemoved_4783_, v___x_4784_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v_fst_4787_; lean_object* v_snd_4788_; lean_object* v_a_x27_4789_; lean_object* v___x_4790_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
v_fst_4787_ = lean_ctor_get(v_a_4786_, 0);
lean_inc(v_fst_4787_);
v_snd_4788_ = lean_ctor_get(v_a_4786_, 1);
lean_inc(v_snd_4788_);
lean_dec(v_a_4786_);
v_a_x27_4789_ = lean_mk_empty_array_with_capacity(v_snd_4788_);
lean_dec(v_snd_4788_);
v___x_4790_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4779_, v_fst_4787_, v_a_4772_, v_numRemoved_4783_, v_a_x27_4789_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
lean_dec(v_fst_4787_);
return v___x_4790_;
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
v_a_4791_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4785_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4785_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4799_, lean_object* v_f_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4799_, v_f_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v_a_4799_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v___f_4814_; lean_object* v___x_4815_; 
v___f_4814_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4815_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4808_, v___f_4814_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
lean_dec_ref(v_mvars_4816_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4823_, lean_object* v_val_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4823_, v_val_4824_, v___y_4826_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4831_, lean_object* v_val_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4831_, v_val_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4839_, lean_object* v_a_4840_, lean_object* v_f_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4840_, v_f_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4848_, lean_object* v_a_4849_, lean_object* v_f_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4848_, v_a_4849_, v_f_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v_a_4849_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4857_, lean_object* v_x_4858_, lean_object* v_x_4859_, lean_object* v_x_4860_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4858_, v_x_4859_, v_x_4860_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4862_, lean_object* v_00_u03b1_4863_, lean_object* v_a_4864_, lean_object* v_next_4865_, lean_object* v_f_4866_, lean_object* v_inst_4867_, lean_object* v_R_4868_, lean_object* v_a_4869_, lean_object* v_b_4870_, lean_object* v_c_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4862_, v_a_4864_, v_next_4865_, v_f_4866_, v_a_4869_, v_b_4870_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4878_, lean_object* v_00_u03b1_4879_, lean_object* v_a_4880_, lean_object* v_next_4881_, lean_object* v_f_4882_, lean_object* v_inst_4883_, lean_object* v_R_4884_, lean_object* v_a_4885_, lean_object* v_b_4886_, lean_object* v_c_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4878_, v_00_u03b1_4879_, v_a_4880_, v_next_4881_, v_f_4882_, v_inst_4883_, v_R_4884_, v_a_4885_, v_b_4886_, v_c_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec(v___y_4889_);
lean_dec_ref(v___y_4888_);
lean_dec_ref(v_a_4880_);
lean_dec(v_upperBound_4878_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4894_, lean_object* v_upperBound_4895_, lean_object* v_removed_4896_, lean_object* v_a_4897_, lean_object* v_inst_4898_, lean_object* v_R_4899_, lean_object* v_a_4900_, lean_object* v_b_4901_, lean_object* v_c_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4895_, v_removed_4896_, v_a_4897_, v_a_4900_, v_b_4901_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4909_, lean_object* v_upperBound_4910_, lean_object* v_removed_4911_, lean_object* v_a_4912_, lean_object* v_inst_4913_, lean_object* v_R_4914_, lean_object* v_a_4915_, lean_object* v_b_4916_, lean_object* v_c_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4909_, v_upperBound_4910_, v_removed_4911_, v_a_4912_, v_inst_4913_, v_R_4914_, v_a_4915_, v_b_4916_, v_c_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec_ref(v_a_4912_);
lean_dec_ref(v_removed_4911_);
lean_dec(v_upperBound_4910_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4924_, lean_object* v___x_4925_, lean_object* v_00_u03b1_4926_, lean_object* v_a_4927_, lean_object* v_f_4928_, lean_object* v_inst_4929_, lean_object* v_R_4930_, lean_object* v_a_4931_, lean_object* v_b_4932_, lean_object* v_c_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4924_, v___x_4925_, v_a_4927_, v_f_4928_, v_a_4931_, v_b_4932_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4940_, lean_object* v___x_4941_, lean_object* v_00_u03b1_4942_, lean_object* v_a_4943_, lean_object* v_f_4944_, lean_object* v_inst_4945_, lean_object* v_R_4946_, lean_object* v_a_4947_, lean_object* v_b_4948_, lean_object* v_c_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4940_, v___x_4941_, v_00_u03b1_4942_, v_a_4943_, v_f_4944_, v_inst_4945_, v_R_4946_, v_a_4947_, v_b_4948_, v_c_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec_ref(v_a_4943_);
lean_dec(v___x_4941_);
lean_dec(v_upperBound_4940_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4956_, lean_object* v_x_4957_, size_t v_x_4958_, size_t v_x_4959_, lean_object* v_x_4960_, lean_object* v_x_4961_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4957_, v_x_4958_, v_x_4959_, v_x_4960_, v_x_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4963_, lean_object* v_x_4964_, lean_object* v_x_4965_, lean_object* v_x_4966_, lean_object* v_x_4967_, lean_object* v_x_4968_){
_start:
{
size_t v_x_5214__boxed_4969_; size_t v_x_5215__boxed_4970_; lean_object* v_res_4971_; 
v_x_5214__boxed_4969_ = lean_unbox_usize(v_x_4965_);
lean_dec(v_x_4965_);
v_x_5215__boxed_4970_ = lean_unbox_usize(v_x_4966_);
lean_dec(v_x_4966_);
v_res_4971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4963_, v_x_4964_, v_x_5214__boxed_4969_, v_x_5215__boxed_4970_, v_x_4967_, v_x_4968_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4972_, lean_object* v_n_4973_, lean_object* v_k_4974_, lean_object* v_v_4975_){
_start:
{
lean_object* v___x_4976_; 
v___x_4976_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4973_, v_k_4974_, v_v_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4977_, size_t v_depth_4978_, lean_object* v_keys_4979_, lean_object* v_vals_4980_, lean_object* v_heq_4981_, lean_object* v_i_4982_, lean_object* v_entries_4983_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4978_, v_keys_4979_, v_vals_4980_, v_i_4982_, v_entries_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4985_, lean_object* v_depth_4986_, lean_object* v_keys_4987_, lean_object* v_vals_4988_, lean_object* v_heq_4989_, lean_object* v_i_4990_, lean_object* v_entries_4991_){
_start:
{
size_t v_depth_boxed_4992_; lean_object* v_res_4993_; 
v_depth_boxed_4992_ = lean_unbox_usize(v_depth_4986_);
lean_dec(v_depth_4986_);
v_res_4993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4985_, v_depth_boxed_4992_, v_keys_4987_, v_vals_4988_, v_heq_4989_, v_i_4990_, v_entries_4991_);
lean_dec_ref(v_vals_4988_);
lean_dec_ref(v_keys_4987_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4994_, lean_object* v_x_4995_, lean_object* v_x_4996_, lean_object* v_x_4997_, lean_object* v_x_4998_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4995_, v_x_4996_, v_x_4997_, v_x_4998_);
return v___x_4999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
return v___x_5002_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5005_ = l_Lean_stringToMessageData(v___x_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5006_, lean_object* v_as_5007_, size_t v_sz_5008_, size_t v_i_5009_, lean_object* v_b_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v_a_5017_; uint8_t v___x_5021_; 
v___x_5021_ = lean_usize_dec_lt(v_i_5009_, v_sz_5008_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v_b_5010_);
return v___x_5022_;
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5024_; 
v_a_5023_ = lean_array_uget_borrowed(v_as_5007_, v_i_5009_);
lean_inc(v_a_5023_);
v___x_5024_ = l_Lean_MVarId_getType(v_a_5023_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___y_5027_; lean_object* v___y_5028_; lean_object* v___y_5029_; lean_object* v___y_5030_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref(v___x_5024_);
if (lean_obj_tag(v_a_5025_) == 10)
{
lean_object* v_expr_5043_; 
v_expr_5043_ = lean_ctor_get(v_a_5025_, 1);
if (lean_obj_tag(v_expr_5043_) == 5)
{
lean_object* v_arg_5044_; lean_object* v___x_5045_; 
lean_inc_ref(v_expr_5043_);
lean_dec_ref(v_a_5025_);
v_arg_5044_ = lean_ctor_get(v_expr_5043_, 1);
lean_inc_ref_n(v_arg_5044_, 2);
lean_dec_ref(v_expr_5043_);
v___x_5045_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5006_, v_arg_5044_);
if (lean_obj_tag(v___x_5045_) == 1)
{
lean_object* v_val_5046_; lean_object* v_fst_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
lean_dec_ref(v_arg_5044_);
v_val_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_val_5046_);
lean_dec_ref(v___x_5045_);
v_fst_5047_ = lean_ctor_get(v_val_5046_, 0);
lean_inc(v_fst_5047_);
lean_dec(v_val_5046_);
v___x_5048_ = lean_array_get_size(v_b_5010_);
v___x_5049_ = lean_nat_dec_lt(v_fst_5047_, v___x_5048_);
if (v___x_5049_ == 0)
{
lean_dec(v_fst_5047_);
v_a_5017_ = v_b_5010_;
goto v___jp_5016_;
}
else
{
lean_object* v_v_5050_; lean_object* v___x_5051_; lean_object* v_xs_x27_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v_v_5050_ = lean_array_fget(v_b_5010_, v_fst_5047_);
v___x_5051_ = lean_box(0);
v_xs_x27_5052_ = lean_array_fset(v_b_5010_, v_fst_5047_, v___x_5051_);
lean_inc(v_a_5023_);
v___x_5053_ = lean_array_push(v_v_5050_, v_a_5023_);
v___x_5054_ = lean_array_fset(v_xs_x27_5052_, v_fst_5047_, v___x_5053_);
lean_dec(v_fst_5047_);
v_a_5017_ = v___x_5054_;
goto v___jp_5016_;
}
}
else
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_dec(v___x_5045_);
v___x_5055_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5056_ = l_Lean_indentExpr(v_arg_5044_);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5055_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5057_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_dec_ref(v___x_5058_);
v_a_5017_ = v_b_5010_;
goto v___jp_5016_;
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec_ref(v_b_5010_);
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_5058_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5058_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
}
else
{
v___y_5027_ = v___y_5011_;
v___y_5028_ = v___y_5012_;
v___y_5029_ = v___y_5013_;
v___y_5030_ = v___y_5014_;
goto v___jp_5026_;
}
}
else
{
v___y_5027_ = v___y_5011_;
v___y_5028_ = v___y_5012_;
v___y_5029_ = v___y_5013_;
v___y_5030_ = v___y_5014_;
goto v___jp_5026_;
}
v___jp_5026_:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5032_ = l_Lean_indentExpr(v_a_5025_);
v___x_5033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5031_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5033_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_dec_ref(v___x_5034_);
v_a_5017_ = v_b_5010_;
goto v___jp_5016_;
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
lean_dec_ref(v_b_5010_);
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5034_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5034_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec_ref(v_b_5010_);
v_a_5067_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_5024_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5024_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
v___jp_5016_:
{
size_t v___x_5018_; size_t v___x_5019_; 
v___x_5018_ = ((size_t)1ULL);
v___x_5019_ = lean_usize_add(v_i_5009_, v___x_5018_);
v_i_5009_ = v___x_5019_;
v_b_5010_ = v_a_5017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5075_, lean_object* v_as_5076_, lean_object* v_sz_5077_, lean_object* v_i_5078_, lean_object* v_b_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
size_t v_sz_boxed_5085_; size_t v_i_boxed_5086_; lean_object* v_res_5087_; 
v_sz_boxed_5085_ = lean_unbox_usize(v_sz_5077_);
lean_dec(v_sz_5077_);
v_i_boxed_5086_ = lean_unbox_usize(v_i_5078_);
lean_dec(v_i_5078_);
v_res_5087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5075_, v_as_5076_, v_sz_boxed_5085_, v_i_boxed_5086_, v_b_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
lean_dec_ref(v_as_5076_);
lean_dec_ref(v_argsPacker_5075_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5088_, lean_object* v_numFuncs_5089_, lean_object* v_goals_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v___x_5096_; lean_object* v_r_5097_; size_t v_sz_5098_; size_t v___x_5099_; lean_object* v___x_5100_; 
v___x_5096_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5097_ = lean_mk_array(v_numFuncs_5089_, v___x_5096_);
v_sz_5098_ = lean_array_size(v_goals_5090_);
v___x_5099_ = ((size_t)0ULL);
v___x_5100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5088_, v_goals_5090_, v_sz_5098_, v___x_5099_, v_r_5097_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5101_, lean_object* v_numFuncs_5102_, lean_object* v_goals_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5101_, v_numFuncs_5102_, v_goals_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec_ref(v_a_5104_);
lean_dec_ref(v_goals_5103_);
lean_dec_ref(v_argsPacker_5101_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v___x_5113_; lean_object* v_infoState_5114_; uint8_t v_enabled_5115_; 
v___x_5113_ = lean_st_ref_get(v___y_5111_);
v_infoState_5114_ = lean_ctor_get(v___x_5113_, 7);
lean_inc_ref(v_infoState_5114_);
lean_dec(v___x_5113_);
v_enabled_5115_ = lean_ctor_get_uint8(v_infoState_5114_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5114_);
if (v_enabled_5115_ == 0)
{
lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec_ref(v_t_5110_);
v___x_5116_ = lean_box(0);
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v___x_5116_);
return v___x_5117_;
}
else
{
lean_object* v___x_5118_; lean_object* v_infoState_5119_; lean_object* v_env_5120_; lean_object* v_nextMacroScope_5121_; lean_object* v_ngen_5122_; lean_object* v_auxDeclNGen_5123_; lean_object* v_traceState_5124_; lean_object* v_cache_5125_; lean_object* v_messages_5126_; lean_object* v_snapshotTasks_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5149_; 
v___x_5118_ = lean_st_ref_take(v___y_5111_);
v_infoState_5119_ = lean_ctor_get(v___x_5118_, 7);
v_env_5120_ = lean_ctor_get(v___x_5118_, 0);
v_nextMacroScope_5121_ = lean_ctor_get(v___x_5118_, 1);
v_ngen_5122_ = lean_ctor_get(v___x_5118_, 2);
v_auxDeclNGen_5123_ = lean_ctor_get(v___x_5118_, 3);
v_traceState_5124_ = lean_ctor_get(v___x_5118_, 4);
v_cache_5125_ = lean_ctor_get(v___x_5118_, 5);
v_messages_5126_ = lean_ctor_get(v___x_5118_, 6);
v_snapshotTasks_5127_ = lean_ctor_get(v___x_5118_, 8);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5129_ = v___x_5118_;
v_isShared_5130_ = v_isSharedCheck_5149_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_snapshotTasks_5127_);
lean_inc(v_infoState_5119_);
lean_inc(v_messages_5126_);
lean_inc(v_cache_5125_);
lean_inc(v_traceState_5124_);
lean_inc(v_auxDeclNGen_5123_);
lean_inc(v_ngen_5122_);
lean_inc(v_nextMacroScope_5121_);
lean_inc(v_env_5120_);
lean_dec(v___x_5118_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5149_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
uint8_t v_enabled_5131_; lean_object* v_assignment_5132_; lean_object* v_lazyAssignment_5133_; lean_object* v_trees_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5148_; 
v_enabled_5131_ = lean_ctor_get_uint8(v_infoState_5119_, sizeof(void*)*3);
v_assignment_5132_ = lean_ctor_get(v_infoState_5119_, 0);
v_lazyAssignment_5133_ = lean_ctor_get(v_infoState_5119_, 1);
v_trees_5134_ = lean_ctor_get(v_infoState_5119_, 2);
v_isSharedCheck_5148_ = !lean_is_exclusive(v_infoState_5119_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5136_ = v_infoState_5119_;
v_isShared_5137_ = v_isSharedCheck_5148_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_trees_5134_);
lean_inc(v_lazyAssignment_5133_);
lean_inc(v_assignment_5132_);
lean_dec(v_infoState_5119_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5148_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5138_ = l_Lean_PersistentArray_push___redArg(v_trees_5134_, v_t_5110_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 2, v___x_5138_);
v___x_5140_ = v___x_5136_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_assignment_5132_);
lean_ctor_set(v_reuseFailAlloc_5147_, 1, v_lazyAssignment_5133_);
lean_ctor_set(v_reuseFailAlloc_5147_, 2, v___x_5138_);
lean_ctor_set_uint8(v_reuseFailAlloc_5147_, sizeof(void*)*3, v_enabled_5131_);
v___x_5140_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5142_; 
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 7, v___x_5140_);
v___x_5142_ = v___x_5129_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_env_5120_);
lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_nextMacroScope_5121_);
lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_ngen_5122_);
lean_ctor_set(v_reuseFailAlloc_5146_, 3, v_auxDeclNGen_5123_);
lean_ctor_set(v_reuseFailAlloc_5146_, 4, v_traceState_5124_);
lean_ctor_set(v_reuseFailAlloc_5146_, 5, v_cache_5125_);
lean_ctor_set(v_reuseFailAlloc_5146_, 6, v_messages_5126_);
lean_ctor_set(v_reuseFailAlloc_5146_, 7, v___x_5140_);
lean_ctor_set(v_reuseFailAlloc_5146_, 8, v_snapshotTasks_5127_);
v___x_5142_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5143_ = lean_st_ref_set(v___y_5111_, v___x_5142_);
v___x_5144_ = lean_box(0);
v___x_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
return v___x_5145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5150_, v___y_5151_);
lean_dec(v___y_5151_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5154_, v___y_5160_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5172_, lean_object* v___y_5173_){
_start:
{
uint8_t v___x_5175_; 
v___x_5175_ = l_Lean_Expr_hasMVar(v_e_5172_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v_e_5172_);
return v___x_5176_;
}
else
{
lean_object* v___x_5177_; lean_object* v_mctx_5178_; lean_object* v___x_5179_; lean_object* v_fst_5180_; lean_object* v_snd_5181_; lean_object* v___x_5182_; lean_object* v_cache_5183_; lean_object* v_zetaDeltaFVarIds_5184_; lean_object* v_postponed_5185_; lean_object* v_diag_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5195_; 
v___x_5177_ = lean_st_ref_get(v___y_5173_);
v_mctx_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc_ref(v_mctx_5178_);
lean_dec(v___x_5177_);
v___x_5179_ = l_Lean_instantiateMVarsCore(v_mctx_5178_, v_e_5172_);
v_fst_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_fst_5180_);
v_snd_5181_ = lean_ctor_get(v___x_5179_, 1);
lean_inc(v_snd_5181_);
lean_dec_ref(v___x_5179_);
v___x_5182_ = lean_st_ref_take(v___y_5173_);
v_cache_5183_ = lean_ctor_get(v___x_5182_, 1);
v_zetaDeltaFVarIds_5184_ = lean_ctor_get(v___x_5182_, 2);
v_postponed_5185_ = lean_ctor_get(v___x_5182_, 3);
v_diag_5186_ = lean_ctor_get(v___x_5182_, 4);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5195_ == 0)
{
lean_object* v_unused_5196_; 
v_unused_5196_ = lean_ctor_get(v___x_5182_, 0);
lean_dec(v_unused_5196_);
v___x_5188_ = v___x_5182_;
v_isShared_5189_ = v_isSharedCheck_5195_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_diag_5186_);
lean_inc(v_postponed_5185_);
lean_inc(v_zetaDeltaFVarIds_5184_);
lean_inc(v_cache_5183_);
lean_dec(v___x_5182_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5195_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
lean_ctor_set(v___x_5188_, 0, v_snd_5181_);
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_snd_5181_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_cache_5183_);
lean_ctor_set(v_reuseFailAlloc_5194_, 2, v_zetaDeltaFVarIds_5184_);
lean_ctor_set(v_reuseFailAlloc_5194_, 3, v_postponed_5185_);
lean_ctor_set(v_reuseFailAlloc_5194_, 4, v_diag_5186_);
v___x_5191_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5192_ = lean_st_ref_set(v___y_5173_, v___x_5191_);
v___x_5193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5193_, 0, v_fst_5180_);
return v___x_5193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5197_, v___y_5198_);
lean_dec(v___y_5198_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5201_, v___y_5203_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
return v_res_5214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5215_, size_t v_i_5216_, size_t v_stop_5217_, lean_object* v_b_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
uint8_t v___x_5226_; 
v___x_5226_ = lean_usize_dec_eq(v_i_5216_, v_stop_5217_);
if (v___x_5226_ == 0)
{
lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5227_ = lean_array_uget_borrowed(v_as_5215_, v_i_5216_);
lean_inc(v___x_5227_);
v___x_5228_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
v___x_5229_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5228_, v___y_5224_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; size_t v___x_5231_; size_t v___x_5232_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5230_);
lean_dec_ref(v___x_5229_);
v___x_5231_ = ((size_t)1ULL);
v___x_5232_ = lean_usize_add(v_i_5216_, v___x_5231_);
v_i_5216_ = v___x_5232_;
v_b_5218_ = v_a_5230_;
goto _start;
}
else
{
return v___x_5229_;
}
}
else
{
lean_object* v___x_5234_; 
v___x_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5234_, 0, v_b_5218_);
return v___x_5234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5235_, lean_object* v_i_5236_, lean_object* v_stop_5237_, lean_object* v_b_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
size_t v_i_boxed_5246_; size_t v_stop_boxed_5247_; lean_object* v_res_5248_; 
v_i_boxed_5246_ = lean_unbox_usize(v_i_5236_);
lean_dec(v_i_5236_);
v_stop_boxed_5247_ = lean_unbox_usize(v_stop_5237_);
lean_dec(v_stop_5237_);
v_res_5248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5235_, v_i_boxed_5246_, v_stop_boxed_5247_, v_b_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec_ref(v_as_5235_);
return v_res_5248_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5249_ = lean_unsigned_to_nat(32u);
v___x_5250_ = lean_mk_empty_array_with_capacity(v___x_5249_);
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5250_);
return v___x_5251_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5252_ = ((size_t)5ULL);
v___x_5253_ = lean_unsigned_to_nat(0u);
v___x_5254_ = lean_unsigned_to_nat(32u);
v___x_5255_ = lean_mk_empty_array_with_capacity(v___x_5254_);
v___x_5256_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5257_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5257_, 0, v___x_5256_);
lean_ctor_set(v___x_5257_, 1, v___x_5255_);
lean_ctor_set(v___x_5257_, 2, v___x_5253_);
lean_ctor_set(v___x_5257_, 3, v___x_5253_);
lean_ctor_set_usize(v___x_5257_, 4, v___x_5252_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; lean_object* v_infoState_5261_; lean_object* v_trees_5262_; lean_object* v___x_5263_; lean_object* v_infoState_5264_; lean_object* v_env_5265_; lean_object* v_nextMacroScope_5266_; lean_object* v_ngen_5267_; lean_object* v_auxDeclNGen_5268_; lean_object* v_traceState_5269_; lean_object* v_cache_5270_; lean_object* v_messages_5271_; lean_object* v_snapshotTasks_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5293_; 
v___x_5260_ = lean_st_ref_get(v___y_5258_);
v_infoState_5261_ = lean_ctor_get(v___x_5260_, 7);
lean_inc_ref(v_infoState_5261_);
lean_dec(v___x_5260_);
v_trees_5262_ = lean_ctor_get(v_infoState_5261_, 2);
lean_inc_ref(v_trees_5262_);
lean_dec_ref(v_infoState_5261_);
v___x_5263_ = lean_st_ref_take(v___y_5258_);
v_infoState_5264_ = lean_ctor_get(v___x_5263_, 7);
v_env_5265_ = lean_ctor_get(v___x_5263_, 0);
v_nextMacroScope_5266_ = lean_ctor_get(v___x_5263_, 1);
v_ngen_5267_ = lean_ctor_get(v___x_5263_, 2);
v_auxDeclNGen_5268_ = lean_ctor_get(v___x_5263_, 3);
v_traceState_5269_ = lean_ctor_get(v___x_5263_, 4);
v_cache_5270_ = lean_ctor_get(v___x_5263_, 5);
v_messages_5271_ = lean_ctor_get(v___x_5263_, 6);
v_snapshotTasks_5272_ = lean_ctor_get(v___x_5263_, 8);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5274_ = v___x_5263_;
v_isShared_5275_ = v_isSharedCheck_5293_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_snapshotTasks_5272_);
lean_inc(v_infoState_5264_);
lean_inc(v_messages_5271_);
lean_inc(v_cache_5270_);
lean_inc(v_traceState_5269_);
lean_inc(v_auxDeclNGen_5268_);
lean_inc(v_ngen_5267_);
lean_inc(v_nextMacroScope_5266_);
lean_inc(v_env_5265_);
lean_dec(v___x_5263_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5293_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
uint8_t v_enabled_5276_; lean_object* v_assignment_5277_; lean_object* v_lazyAssignment_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5291_; 
v_enabled_5276_ = lean_ctor_get_uint8(v_infoState_5264_, sizeof(void*)*3);
v_assignment_5277_ = lean_ctor_get(v_infoState_5264_, 0);
v_lazyAssignment_5278_ = lean_ctor_get(v_infoState_5264_, 1);
v_isSharedCheck_5291_ = !lean_is_exclusive(v_infoState_5264_);
if (v_isSharedCheck_5291_ == 0)
{
lean_object* v_unused_5292_; 
v_unused_5292_ = lean_ctor_get(v_infoState_5264_, 2);
lean_dec(v_unused_5292_);
v___x_5280_ = v_infoState_5264_;
v_isShared_5281_ = v_isSharedCheck_5291_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_lazyAssignment_5278_);
lean_inc(v_assignment_5277_);
lean_dec(v_infoState_5264_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5291_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5282_; lean_object* v___x_5284_; 
v___x_5282_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 2, v___x_5282_);
v___x_5284_ = v___x_5280_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_assignment_5277_);
lean_ctor_set(v_reuseFailAlloc_5290_, 1, v_lazyAssignment_5278_);
lean_ctor_set(v_reuseFailAlloc_5290_, 2, v___x_5282_);
lean_ctor_set_uint8(v_reuseFailAlloc_5290_, sizeof(void*)*3, v_enabled_5276_);
v___x_5284_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5286_; 
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 7, v___x_5284_);
v___x_5286_ = v___x_5274_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_env_5265_);
lean_ctor_set(v_reuseFailAlloc_5289_, 1, v_nextMacroScope_5266_);
lean_ctor_set(v_reuseFailAlloc_5289_, 2, v_ngen_5267_);
lean_ctor_set(v_reuseFailAlloc_5289_, 3, v_auxDeclNGen_5268_);
lean_ctor_set(v_reuseFailAlloc_5289_, 4, v_traceState_5269_);
lean_ctor_set(v_reuseFailAlloc_5289_, 5, v_cache_5270_);
lean_ctor_set(v_reuseFailAlloc_5289_, 6, v_messages_5271_);
lean_ctor_set(v_reuseFailAlloc_5289_, 7, v___x_5284_);
lean_ctor_set(v_reuseFailAlloc_5289_, 8, v_snapshotTasks_5272_);
v___x_5286_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = lean_st_ref_set(v___y_5258_, v___x_5286_);
v___x_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5288_, 0, v_trees_5262_);
return v___x_5288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5294_);
lean_dec(v___y_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5297_, lean_object* v_mkInfoTree_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v_a_5306_, lean_object* v_a_x3f_5307_){
_start:
{
lean_object* v___x_5309_; lean_object* v_infoState_5310_; lean_object* v_trees_5311_; lean_object* v___x_5312_; 
v___x_5309_ = lean_st_ref_get(v___y_5297_);
v_infoState_5310_ = lean_ctor_get(v___x_5309_, 7);
lean_inc_ref(v_infoState_5310_);
lean_dec(v___x_5309_);
v_trees_5311_ = lean_ctor_get(v_infoState_5310_, 2);
lean_inc_ref(v_trees_5311_);
lean_dec_ref(v_infoState_5310_);
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5305_);
lean_inc(v___y_5304_);
lean_inc_ref(v___y_5303_);
lean_inc(v___y_5302_);
lean_inc_ref(v___y_5301_);
lean_inc(v___y_5300_);
lean_inc_ref(v___y_5299_);
v___x_5312_ = lean_apply_10(v_mkInfoTree_5298_, v_trees_5311_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5297_, lean_box(0));
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5351_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5351_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5351_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5317_; lean_object* v_infoState_5318_; lean_object* v_env_5319_; lean_object* v_nextMacroScope_5320_; lean_object* v_ngen_5321_; lean_object* v_auxDeclNGen_5322_; lean_object* v_traceState_5323_; lean_object* v_cache_5324_; lean_object* v_messages_5325_; lean_object* v_snapshotTasks_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5350_; 
v___x_5317_ = lean_st_ref_take(v___y_5297_);
v_infoState_5318_ = lean_ctor_get(v___x_5317_, 7);
v_env_5319_ = lean_ctor_get(v___x_5317_, 0);
v_nextMacroScope_5320_ = lean_ctor_get(v___x_5317_, 1);
v_ngen_5321_ = lean_ctor_get(v___x_5317_, 2);
v_auxDeclNGen_5322_ = lean_ctor_get(v___x_5317_, 3);
v_traceState_5323_ = lean_ctor_get(v___x_5317_, 4);
v_cache_5324_ = lean_ctor_get(v___x_5317_, 5);
v_messages_5325_ = lean_ctor_get(v___x_5317_, 6);
v_snapshotTasks_5326_ = lean_ctor_get(v___x_5317_, 8);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5328_ = v___x_5317_;
v_isShared_5329_ = v_isSharedCheck_5350_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_snapshotTasks_5326_);
lean_inc(v_infoState_5318_);
lean_inc(v_messages_5325_);
lean_inc(v_cache_5324_);
lean_inc(v_traceState_5323_);
lean_inc(v_auxDeclNGen_5322_);
lean_inc(v_ngen_5321_);
lean_inc(v_nextMacroScope_5320_);
lean_inc(v_env_5319_);
lean_dec(v___x_5317_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5350_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
uint8_t v_enabled_5330_; lean_object* v_assignment_5331_; lean_object* v_lazyAssignment_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5348_; 
v_enabled_5330_ = lean_ctor_get_uint8(v_infoState_5318_, sizeof(void*)*3);
v_assignment_5331_ = lean_ctor_get(v_infoState_5318_, 0);
v_lazyAssignment_5332_ = lean_ctor_get(v_infoState_5318_, 1);
v_isSharedCheck_5348_ = !lean_is_exclusive(v_infoState_5318_);
if (v_isSharedCheck_5348_ == 0)
{
lean_object* v_unused_5349_; 
v_unused_5349_ = lean_ctor_get(v_infoState_5318_, 2);
lean_dec(v_unused_5349_);
v___x_5334_ = v_infoState_5318_;
v_isShared_5335_ = v_isSharedCheck_5348_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_lazyAssignment_5332_);
lean_inc(v_assignment_5331_);
lean_dec(v_infoState_5318_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5348_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5336_; lean_object* v___x_5338_; 
v___x_5336_ = l_Lean_PersistentArray_push___redArg(v_a_5306_, v_a_5313_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 2, v___x_5336_);
v___x_5338_ = v___x_5334_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_assignment_5331_);
lean_ctor_set(v_reuseFailAlloc_5347_, 1, v_lazyAssignment_5332_);
lean_ctor_set(v_reuseFailAlloc_5347_, 2, v___x_5336_);
lean_ctor_set_uint8(v_reuseFailAlloc_5347_, sizeof(void*)*3, v_enabled_5330_);
v___x_5338_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5340_; 
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 7, v___x_5338_);
v___x_5340_ = v___x_5328_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_env_5319_);
lean_ctor_set(v_reuseFailAlloc_5346_, 1, v_nextMacroScope_5320_);
lean_ctor_set(v_reuseFailAlloc_5346_, 2, v_ngen_5321_);
lean_ctor_set(v_reuseFailAlloc_5346_, 3, v_auxDeclNGen_5322_);
lean_ctor_set(v_reuseFailAlloc_5346_, 4, v_traceState_5323_);
lean_ctor_set(v_reuseFailAlloc_5346_, 5, v_cache_5324_);
lean_ctor_set(v_reuseFailAlloc_5346_, 6, v_messages_5325_);
lean_ctor_set(v_reuseFailAlloc_5346_, 7, v___x_5338_);
lean_ctor_set(v_reuseFailAlloc_5346_, 8, v_snapshotTasks_5326_);
v___x_5340_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
v___x_5341_ = lean_st_ref_set(v___y_5297_, v___x_5340_);
v___x_5342_ = lean_box(0);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5342_);
v___x_5344_ = v___x_5315_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5342_);
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
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec_ref(v_a_5306_);
v_a_5352_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5312_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5312_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5360_, lean_object* v_mkInfoTree_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v_a_5369_, lean_object* v_a_x3f_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5360_, v_mkInfoTree_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v_a_5369_, v_a_x3f_5370_);
lean_dec(v_a_x3f_5370_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v___y_5360_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5373_, lean_object* v_mkInfoTree_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
lean_object* v___x_5384_; lean_object* v_infoState_5385_; uint8_t v_enabled_5386_; 
v___x_5384_ = lean_st_ref_get(v___y_5382_);
v_infoState_5385_ = lean_ctor_get(v___x_5384_, 7);
lean_inc_ref(v_infoState_5385_);
lean_dec(v___x_5384_);
v_enabled_5386_ = lean_ctor_get_uint8(v_infoState_5385_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5385_);
if (v_enabled_5386_ == 0)
{
lean_object* v___x_5387_; 
lean_dec_ref(v_mkInfoTree_5374_);
lean_inc(v___y_5382_);
lean_inc_ref(v___y_5381_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
lean_inc(v___y_5378_);
lean_inc_ref(v___y_5377_);
lean_inc(v___y_5376_);
lean_inc_ref(v___y_5375_);
v___x_5387_ = lean_apply_9(v_x_5373_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, lean_box(0));
return v___x_5387_;
}
else
{
lean_object* v___x_5388_; lean_object* v_a_5389_; lean_object* v_r_5390_; 
v___x_5388_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5382_);
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc(v_a_5389_);
lean_dec_ref(v___x_5388_);
lean_inc(v___y_5382_);
lean_inc_ref(v___y_5381_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
lean_inc(v___y_5378_);
lean_inc_ref(v___y_5377_);
lean_inc(v___y_5376_);
lean_inc_ref(v___y_5375_);
v_r_5390_ = lean_apply_9(v_x_5373_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, lean_box(0));
if (lean_obj_tag(v_r_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5415_; 
v_a_5391_ = lean_ctor_get(v_r_5390_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v_r_5390_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5393_ = v_r_5390_;
v_isShared_5394_ = v_isSharedCheck_5415_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v_r_5390_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5415_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5396_; 
lean_inc(v_a_5391_);
if (v_isShared_5394_ == 0)
{
lean_ctor_set_tag(v___x_5393_, 1);
v___x_5396_ = v___x_5393_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5391_);
v___x_5396_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5397_; 
v___x_5397_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5382_, v_mkInfoTree_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v_a_5389_, v___x_5396_);
lean_dec_ref(v___x_5396_);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5404_; 
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5404_ == 0)
{
lean_object* v_unused_5405_; 
v_unused_5405_ = lean_ctor_get(v___x_5397_, 0);
lean_dec(v_unused_5405_);
v___x_5399_ = v___x_5397_;
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
else
{
lean_dec(v___x_5397_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5402_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 0, v_a_5391_);
v___x_5402_ = v___x_5399_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5391_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_dec(v_a_5391_);
v_a_5406_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5397_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5397_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v_a_5416_ = lean_ctor_get(v_r_5390_, 0);
lean_inc(v_a_5416_);
lean_dec_ref(v_r_5390_);
v___x_5417_ = lean_box(0);
v___x_5418_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5382_, v_mkInfoTree_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v_a_5389_, v___x_5417_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5425_; 
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5425_ == 0)
{
lean_object* v_unused_5426_; 
v_unused_5426_ = lean_ctor_get(v___x_5418_, 0);
lean_dec(v_unused_5426_);
v___x_5420_ = v___x_5418_;
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
else
{
lean_dec(v___x_5418_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5423_; 
if (v_isShared_5421_ == 0)
{
lean_ctor_set_tag(v___x_5420_, 1);
lean_ctor_set(v___x_5420_, 0, v_a_5416_);
v___x_5423_ = v___x_5420_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5416_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
else
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5434_; 
lean_dec(v_a_5416_);
v_a_5427_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5429_ = v___x_5418_;
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5418_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5435_, lean_object* v_mkInfoTree_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5435_, v_mkInfoTree_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5447_, lean_object* v_trees_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v___x_5458_; 
lean_inc(v___y_5456_);
lean_inc_ref(v___y_5455_);
lean_inc(v___y_5454_);
lean_inc_ref(v___y_5453_);
lean_inc(v___y_5452_);
lean_inc_ref(v___y_5451_);
lean_inc(v___y_5450_);
lean_inc_ref(v___y_5449_);
v___x_5458_ = lean_apply_9(v_a_5447_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, lean_box(0));
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5467_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5461_ = v___x_5458_;
v_isShared_5462_ = v_isSharedCheck_5467_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5458_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5467_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5463_; lean_object* v___x_5465_; 
v___x_5463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5463_, 0, v_a_5459_);
lean_ctor_set(v___x_5463_, 1, v_trees_5448_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 0, v___x_5463_);
v___x_5465_ = v___x_5461_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec_ref(v_trees_5448_);
v_a_5468_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5458_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5458_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5476_, lean_object* v_trees_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5476_, v_trees_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
lean_dec(v___y_5485_);
lean_dec_ref(v___y_5484_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5488_, lean_object* v_ref_5489_, lean_object* v_tactic_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_){
_start:
{
lean_object* v___x_5500_; 
v___x_5500_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5488_, v___y_5492_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v___x_5501_; 
lean_dec_ref(v___x_5500_);
v___x_5501_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_object* v___x_5502_; 
lean_dec_ref(v___x_5501_);
v___x_5502_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5489_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___f_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref(v___x_5502_);
v___f_5504_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5504_, 0, v_a_5503_);
v___x_5505_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5505_, 0, v_tactic_5490_);
v___x_5506_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5505_, v___f_5504_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_);
return v___x_5506_;
}
else
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5514_; 
lean_dec(v_tactic_5490_);
v_a_5507_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5514_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5509_ = v___x_5502_;
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5502_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
else
{
lean_dec(v_tactic_5490_);
lean_dec(v_ref_5489_);
return v___x_5501_;
}
}
else
{
lean_dec(v_tactic_5490_);
lean_dec(v_ref_5489_);
return v___x_5500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5515_, lean_object* v_ref_5516_, lean_object* v_tactic_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5515_, v_ref_5516_, v_tactic_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
lean_dec(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
return v_res_5527_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = lean_box(1);
v___x_5529_ = l_Lean_MessageData_ofFormat(v___x_5528_);
return v___x_5529_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5534_ = l_Lean_MessageData_ofFormat(v___x_5533_);
return v___x_5534_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5535_, lean_object* v_x_5536_){
_start:
{
if (lean_obj_tag(v_x_5536_) == 0)
{
return v_x_5535_;
}
else
{
lean_object* v_head_5537_; lean_object* v_tail_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5560_; 
v_head_5537_ = lean_ctor_get(v_x_5536_, 0);
v_tail_5538_ = lean_ctor_get(v_x_5536_, 1);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_x_5536_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5540_ = v_x_5536_;
v_isShared_5541_ = v_isSharedCheck_5560_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_tail_5538_);
lean_inc(v_head_5537_);
lean_dec(v_x_5536_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5560_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v_before_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5558_; 
v_before_5542_ = lean_ctor_get(v_head_5537_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v_head_5537_);
if (v_isSharedCheck_5558_ == 0)
{
lean_object* v_unused_5559_; 
v_unused_5559_ = lean_ctor_get(v_head_5537_, 1);
lean_dec(v_unused_5559_);
v___x_5544_ = v_head_5537_;
v_isShared_5545_ = v_isSharedCheck_5558_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_before_5542_);
lean_dec(v_head_5537_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5558_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5546_; lean_object* v___x_5548_; 
v___x_5546_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5545_ == 0)
{
lean_ctor_set_tag(v___x_5544_, 7);
lean_ctor_set(v___x_5544_, 1, v___x_5546_);
lean_ctor_set(v___x_5544_, 0, v_x_5535_);
v___x_5548_ = v___x_5544_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_x_5535_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5549_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5541_ == 0)
{
lean_ctor_set_tag(v___x_5540_, 7);
lean_ctor_set(v___x_5540_, 1, v___x_5549_);
lean_ctor_set(v___x_5540_, 0, v___x_5548_);
v___x_5551_ = v___x_5540_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5552_ = l_Lean_MessageData_ofSyntax(v_before_5542_);
v___x_5553_ = l_Lean_indentD(v___x_5552_);
v___x_5554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5551_);
lean_ctor_set(v___x_5554_, 1, v___x_5553_);
v_x_5535_ = v___x_5554_;
v_x_5536_ = v_tail_5538_;
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
lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5564_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5565_ = l_Lean_MessageData_ofFormat(v___x_5564_);
return v___x_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5566_, lean_object* v_macroStack_5567_, lean_object* v___y_5568_){
_start:
{
lean_object* v_options_5570_; lean_object* v___x_5571_; uint8_t v___x_5572_; 
v_options_5570_ = lean_ctor_get(v___y_5568_, 2);
v___x_5571_ = l_Lean_Elab_pp_macroStack;
v___x_5572_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5570_, v___x_5571_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; 
lean_dec(v_macroStack_5567_);
v___x_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5573_, 0, v_msgData_5566_);
return v___x_5573_;
}
else
{
if (lean_obj_tag(v_macroStack_5567_) == 0)
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5574_, 0, v_msgData_5566_);
return v___x_5574_;
}
else
{
lean_object* v_head_5575_; lean_object* v_after_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5591_; 
v_head_5575_ = lean_ctor_get(v_macroStack_5567_, 0);
lean_inc(v_head_5575_);
v_after_5576_ = lean_ctor_get(v_head_5575_, 1);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_head_5575_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; 
v_unused_5592_ = lean_ctor_get(v_head_5575_, 0);
lean_dec(v_unused_5592_);
v___x_5578_ = v_head_5575_;
v_isShared_5579_ = v_isSharedCheck_5591_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_after_5576_);
lean_dec(v_head_5575_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5591_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5580_; lean_object* v___x_5582_; 
v___x_5580_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5579_ == 0)
{
lean_ctor_set_tag(v___x_5578_, 7);
lean_ctor_set(v___x_5578_, 1, v___x_5580_);
lean_ctor_set(v___x_5578_, 0, v_msgData_5566_);
v___x_5582_ = v___x_5578_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_msgData_5566_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5580_);
v___x_5582_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v_msgData_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5583_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5582_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = l_Lean_MessageData_ofSyntax(v_after_5576_);
v___x_5586_ = l_Lean_indentD(v___x_5585_);
v_msgData_5587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5587_, 0, v___x_5584_);
lean_ctor_set(v_msgData_5587_, 1, v___x_5586_);
v___x_5588_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5587_, v_macroStack_5567_);
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
return v___x_5589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5593_, lean_object* v_macroStack_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
lean_object* v_res_5597_; 
v_res_5597_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5593_, v_macroStack_5594_, v___y_5595_);
lean_dec_ref(v___y_5595_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v_ref_5606_; lean_object* v___x_5607_; lean_object* v_a_5608_; lean_object* v_macroStack_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5620_; 
v_ref_5606_ = lean_ctor_get(v___y_5603_, 5);
v___x_5607_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5598_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc(v_a_5608_);
lean_dec_ref(v___x_5607_);
v_macroStack_5609_ = lean_ctor_get(v___y_5599_, 1);
lean_inc_n(v_macroStack_5609_, 2);
v___x_5610_ = l_Lean_Elab_getBetterRef(v_ref_5606_, v_macroStack_5609_);
v___x_5611_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5608_, v_macroStack_5609_, v___y_5603_);
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5614_ = v___x_5611_;
v_isShared_5615_ = v_isSharedCheck_5620_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5620_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5616_; lean_object* v___x_5618_; 
v___x_5616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5610_);
lean_ctor_set(v___x_5616_, 1, v_a_5612_);
if (v_isShared_5615_ == 0)
{
lean_ctor_set_tag(v___x_5614_, 1);
lean_ctor_set(v___x_5614_, 0, v___x_5616_);
v___x_5618_ = v___x_5614_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5624_);
lean_dec(v___y_5623_);
lean_dec_ref(v___y_5622_);
return v_res_5629_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5631_; lean_object* v___x_5632_; 
v___x_5631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5632_ = l_Lean_stringToMessageData(v___x_5631_);
return v___x_5632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5633_, size_t v_sz_5634_, size_t v_i_5635_, lean_object* v_b_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_){
_start:
{
lean_object* v_a_5645_; uint8_t v___x_5649_; 
v___x_5649_ = lean_usize_dec_lt(v_i_5635_, v_sz_5634_);
if (v___x_5649_ == 0)
{
lean_object* v___x_5650_; 
v___x_5650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5650_, 0, v_b_5636_);
return v___x_5650_;
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5652_; 
v_a_5651_ = lean_array_uget_borrowed(v_as_5633_, v_i_5635_);
lean_inc(v_a_5651_);
v___x_5652_ = l_Lean_MVarId_getType(v_a_5651_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5654_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
lean_inc(v_a_5653_);
lean_dec_ref(v___x_5652_);
lean_inc(v_a_5651_);
v___x_5654_ = l_Lean_MVarId_getType(v_a_5651_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref(v___x_5654_);
v___x_5656_ = lean_box(0);
v___x_5657_ = l_Lean_getRecAppSyntax_x3f(v_a_5655_);
lean_dec(v_a_5655_);
if (lean_obj_tag(v___x_5657_) == 1)
{
lean_object* v_val_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; 
v_val_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_val_5658_);
lean_dec_ref(v___x_5657_);
v___x_5659_ = l_Lean_Expr_mdataExpr_x21(v_a_5653_);
lean_dec(v_a_5653_);
lean_inc(v_a_5651_);
v___x_5660_ = l_Lean_MVarId_setType___redArg(v_a_5651_, v___x_5659_, v___y_5640_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_fileName_5661_; lean_object* v_fileMap_5662_; lean_object* v_options_5663_; lean_object* v_currRecDepth_5664_; lean_object* v_maxRecDepth_5665_; lean_object* v_ref_5666_; lean_object* v_currNamespace_5667_; lean_object* v_openDecls_5668_; lean_object* v_initHeartbeats_5669_; lean_object* v_maxHeartbeats_5670_; lean_object* v_quotContext_5671_; lean_object* v_currMacroScope_5672_; uint8_t v_diag_5673_; lean_object* v_cancelTk_x3f_5674_; uint8_t v_suppressElabErrors_5675_; lean_object* v_inheritedTraceOptions_5676_; lean_object* v_ref_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
lean_dec_ref(v___x_5660_);
v_fileName_5661_ = lean_ctor_get(v___y_5641_, 0);
v_fileMap_5662_ = lean_ctor_get(v___y_5641_, 1);
v_options_5663_ = lean_ctor_get(v___y_5641_, 2);
v_currRecDepth_5664_ = lean_ctor_get(v___y_5641_, 3);
v_maxRecDepth_5665_ = lean_ctor_get(v___y_5641_, 4);
v_ref_5666_ = lean_ctor_get(v___y_5641_, 5);
v_currNamespace_5667_ = lean_ctor_get(v___y_5641_, 6);
v_openDecls_5668_ = lean_ctor_get(v___y_5641_, 7);
v_initHeartbeats_5669_ = lean_ctor_get(v___y_5641_, 8);
v_maxHeartbeats_5670_ = lean_ctor_get(v___y_5641_, 9);
v_quotContext_5671_ = lean_ctor_get(v___y_5641_, 10);
v_currMacroScope_5672_ = lean_ctor_get(v___y_5641_, 11);
v_diag_5673_ = lean_ctor_get_uint8(v___y_5641_, sizeof(void*)*14);
v_cancelTk_x3f_5674_ = lean_ctor_get(v___y_5641_, 12);
v_suppressElabErrors_5675_ = lean_ctor_get_uint8(v___y_5641_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5676_ = lean_ctor_get(v___y_5641_, 13);
v_ref_5677_ = l_Lean_replaceRef(v_val_5658_, v_ref_5666_);
lean_dec(v_val_5658_);
lean_inc_ref(v_inheritedTraceOptions_5676_);
lean_inc(v_cancelTk_x3f_5674_);
lean_inc(v_currMacroScope_5672_);
lean_inc(v_quotContext_5671_);
lean_inc(v_maxHeartbeats_5670_);
lean_inc(v_initHeartbeats_5669_);
lean_inc(v_openDecls_5668_);
lean_inc(v_currNamespace_5667_);
lean_inc(v_maxRecDepth_5665_);
lean_inc(v_currRecDepth_5664_);
lean_inc_ref(v_options_5663_);
lean_inc_ref(v_fileMap_5662_);
lean_inc_ref(v_fileName_5661_);
v___x_5678_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5678_, 0, v_fileName_5661_);
lean_ctor_set(v___x_5678_, 1, v_fileMap_5662_);
lean_ctor_set(v___x_5678_, 2, v_options_5663_);
lean_ctor_set(v___x_5678_, 3, v_currRecDepth_5664_);
lean_ctor_set(v___x_5678_, 4, v_maxRecDepth_5665_);
lean_ctor_set(v___x_5678_, 5, v_ref_5677_);
lean_ctor_set(v___x_5678_, 6, v_currNamespace_5667_);
lean_ctor_set(v___x_5678_, 7, v_openDecls_5668_);
lean_ctor_set(v___x_5678_, 8, v_initHeartbeats_5669_);
lean_ctor_set(v___x_5678_, 9, v_maxHeartbeats_5670_);
lean_ctor_set(v___x_5678_, 10, v_quotContext_5671_);
lean_ctor_set(v___x_5678_, 11, v_currMacroScope_5672_);
lean_ctor_set(v___x_5678_, 12, v_cancelTk_x3f_5674_);
lean_ctor_set(v___x_5678_, 13, v_inheritedTraceOptions_5676_);
lean_ctor_set_uint8(v___x_5678_, sizeof(void*)*14, v_diag_5673_);
lean_ctor_set_uint8(v___x_5678_, sizeof(void*)*14 + 1, v_suppressElabErrors_5675_);
lean_inc(v_a_5651_);
v___x_5679_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5651_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___x_5678_, v___y_5642_);
lean_dec_ref(v___x_5678_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_dec_ref(v___x_5679_);
v_a_5645_ = v___x_5656_;
goto v___jp_5644_;
}
else
{
return v___x_5679_;
}
}
else
{
lean_dec(v_val_5658_);
return v___x_5660_;
}
}
else
{
lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; 
lean_dec(v___x_5657_);
v___x_5680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5681_ = l_Lean_indentExpr(v_a_5653_);
v___x_5682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5680_);
lean_ctor_set(v___x_5682_, 1, v___x_5681_);
v___x_5683_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5682_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_dec_ref(v___x_5683_);
v_a_5645_ = v___x_5656_;
goto v___jp_5644_;
}
else
{
return v___x_5683_;
}
}
}
else
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5691_; 
lean_dec(v_a_5653_);
v_a_5684_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5691_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5691_ == 0)
{
v___x_5686_ = v___x_5654_;
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5654_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5689_; 
if (v_isShared_5687_ == 0)
{
v___x_5689_ = v___x_5686_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
}
else
{
lean_object* v_a_5692_; lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5699_; 
v_a_5692_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5694_ = v___x_5652_;
v_isShared_5695_ = v_isSharedCheck_5699_;
goto v_resetjp_5693_;
}
else
{
lean_inc(v_a_5692_);
lean_dec(v___x_5652_);
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
v___jp_5644_:
{
size_t v___x_5646_; size_t v___x_5647_; 
v___x_5646_ = ((size_t)1ULL);
v___x_5647_ = lean_usize_add(v_i_5635_, v___x_5646_);
v_i_5635_ = v___x_5647_;
v_b_5636_ = v_a_5645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5700_, lean_object* v_sz_5701_, lean_object* v_i_5702_, lean_object* v_b_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
size_t v_sz_boxed_5711_; size_t v_i_boxed_5712_; lean_object* v_res_5713_; 
v_sz_boxed_5711_ = lean_unbox_usize(v_sz_5701_);
lean_dec(v_sz_5701_);
v_i_boxed_5712_ = lean_unbox_usize(v_i_5702_);
lean_dec(v_i_5702_);
v_res_5713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5700_, v_sz_boxed_5711_, v_i_boxed_5712_, v_b_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec(v___y_5707_);
lean_dec_ref(v___y_5706_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec_ref(v_as_5700_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5714_, size_t v_i_5715_, size_t v_stop_5716_, lean_object* v_b_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
uint8_t v___x_5723_; 
v___x_5723_ = lean_usize_dec_eq(v_i_5715_, v_stop_5716_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___x_5724_ = lean_array_uget_borrowed(v_as_5714_, v_i_5715_);
lean_inc(v___x_5724_);
v___x_5725_ = l_Lean_MVarId_getType(v___x_5724_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref(v___x_5725_);
v___x_5727_ = l_Lean_Expr_mdataExpr_x21(v_a_5726_);
lean_dec(v_a_5726_);
lean_inc(v___x_5724_);
v___x_5728_ = l_Lean_MVarId_setType___redArg(v___x_5724_, v___x_5727_, v___y_5719_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; size_t v___x_5730_; size_t v___x_5731_; 
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
lean_inc(v_a_5729_);
lean_dec_ref(v___x_5728_);
v___x_5730_ = ((size_t)1ULL);
v___x_5731_ = lean_usize_add(v_i_5715_, v___x_5730_);
v_i_5715_ = v___x_5731_;
v_b_5717_ = v_a_5729_;
goto _start;
}
else
{
return v___x_5728_;
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
v_a_5733_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5725_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5725_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
else
{
lean_object* v___x_5741_; 
v___x_5741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5741_, 0, v_b_5717_);
return v___x_5741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5742_, lean_object* v_i_5743_, lean_object* v_stop_5744_, lean_object* v_b_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
size_t v_i_boxed_5751_; size_t v_stop_boxed_5752_; lean_object* v_res_5753_; 
v_i_boxed_5751_ = lean_unbox_usize(v_i_5743_);
lean_dec(v_i_5743_);
v_stop_boxed_5752_ = lean_unbox_usize(v_stop_5744_);
lean_dec(v_stop_5744_);
v_res_5753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5742_, v_i_boxed_5751_, v_stop_boxed_5752_, v_b_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec_ref(v_as_5742_);
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5754_, lean_object* v___x_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v___x_5763_; size_t v_sz_5764_; size_t v___x_5765_; lean_object* v___x_5766_; 
v___x_5763_ = lean_box(0);
v_sz_5764_ = lean_array_size(v___x_5755_);
v___x_5765_ = ((size_t)0ULL);
v___x_5766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5755_, v_sz_5764_, v___x_5765_, v___x_5763_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
lean_dec_ref(v___x_5755_);
if (lean_obj_tag(v___x_5766_) == 0)
{
lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5773_; 
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5766_);
if (v_isSharedCheck_5773_ == 0)
{
lean_object* v_unused_5774_; 
v_unused_5774_ = lean_ctor_get(v___x_5766_, 0);
lean_dec(v_unused_5774_);
v___x_5768_ = v___x_5766_;
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
else
{
lean_dec(v___x_5766_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5771_; 
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5763_);
v___x_5771_ = v___x_5768_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v___x_5763_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
else
{
return v___x_5766_;
}
}
else
{
lean_object* v_val_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5854_; 
v_val_5775_ = lean_ctor_get(v___x_5754_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5754_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5777_ = v___x_5754_;
v_isShared_5778_ = v_isSharedCheck_5854_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_val_5775_);
lean_dec(v___x_5754_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5854_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v_ref_5779_; lean_object* v_tactic_5780_; lean_object* v_fileName_5781_; lean_object* v_fileMap_5782_; lean_object* v_options_5783_; lean_object* v_currRecDepth_5784_; lean_object* v_maxRecDepth_5785_; lean_object* v_ref_5786_; lean_object* v_currNamespace_5787_; lean_object* v_openDecls_5788_; lean_object* v_initHeartbeats_5789_; lean_object* v_maxHeartbeats_5790_; lean_object* v_quotContext_5791_; lean_object* v_currMacroScope_5792_; uint8_t v_diag_5793_; lean_object* v_cancelTk_x3f_5794_; uint8_t v_suppressElabErrors_5795_; lean_object* v_inheritedTraceOptions_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v_ref_5799_; lean_object* v___x_5800_; lean_object* v___y_5827_; lean_object* v___y_5844_; uint8_t v___x_5845_; 
v_ref_5779_ = lean_ctor_get(v_val_5775_, 0);
lean_inc(v_ref_5779_);
v_tactic_5780_ = lean_ctor_get(v_val_5775_, 1);
lean_inc(v_tactic_5780_);
lean_dec(v_val_5775_);
v_fileName_5781_ = lean_ctor_get(v___y_5760_, 0);
v_fileMap_5782_ = lean_ctor_get(v___y_5760_, 1);
v_options_5783_ = lean_ctor_get(v___y_5760_, 2);
v_currRecDepth_5784_ = lean_ctor_get(v___y_5760_, 3);
v_maxRecDepth_5785_ = lean_ctor_get(v___y_5760_, 4);
v_ref_5786_ = lean_ctor_get(v___y_5760_, 5);
v_currNamespace_5787_ = lean_ctor_get(v___y_5760_, 6);
v_openDecls_5788_ = lean_ctor_get(v___y_5760_, 7);
v_initHeartbeats_5789_ = lean_ctor_get(v___y_5760_, 8);
v_maxHeartbeats_5790_ = lean_ctor_get(v___y_5760_, 9);
v_quotContext_5791_ = lean_ctor_get(v___y_5760_, 10);
v_currMacroScope_5792_ = lean_ctor_get(v___y_5760_, 11);
v_diag_5793_ = lean_ctor_get_uint8(v___y_5760_, sizeof(void*)*14);
v_cancelTk_x3f_5794_ = lean_ctor_get(v___y_5760_, 12);
v_suppressElabErrors_5795_ = lean_ctor_get_uint8(v___y_5760_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5796_ = lean_ctor_get(v___y_5760_, 13);
v___x_5797_ = lean_unsigned_to_nat(0u);
v___x_5798_ = lean_array_get_size(v___x_5755_);
v_ref_5799_ = l_Lean_replaceRef(v_ref_5779_, v_ref_5786_);
lean_inc_ref(v_inheritedTraceOptions_5796_);
lean_inc(v_cancelTk_x3f_5794_);
lean_inc(v_currMacroScope_5792_);
lean_inc(v_quotContext_5791_);
lean_inc(v_maxHeartbeats_5790_);
lean_inc(v_initHeartbeats_5789_);
lean_inc(v_openDecls_5788_);
lean_inc(v_currNamespace_5787_);
lean_inc(v_maxRecDepth_5785_);
lean_inc(v_currRecDepth_5784_);
lean_inc_ref(v_options_5783_);
lean_inc_ref(v_fileMap_5782_);
lean_inc_ref(v_fileName_5781_);
v___x_5800_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5800_, 0, v_fileName_5781_);
lean_ctor_set(v___x_5800_, 1, v_fileMap_5782_);
lean_ctor_set(v___x_5800_, 2, v_options_5783_);
lean_ctor_set(v___x_5800_, 3, v_currRecDepth_5784_);
lean_ctor_set(v___x_5800_, 4, v_maxRecDepth_5785_);
lean_ctor_set(v___x_5800_, 5, v_ref_5799_);
lean_ctor_set(v___x_5800_, 6, v_currNamespace_5787_);
lean_ctor_set(v___x_5800_, 7, v_openDecls_5788_);
lean_ctor_set(v___x_5800_, 8, v_initHeartbeats_5789_);
lean_ctor_set(v___x_5800_, 9, v_maxHeartbeats_5790_);
lean_ctor_set(v___x_5800_, 10, v_quotContext_5791_);
lean_ctor_set(v___x_5800_, 11, v_currMacroScope_5792_);
lean_ctor_set(v___x_5800_, 12, v_cancelTk_x3f_5794_);
lean_ctor_set(v___x_5800_, 13, v_inheritedTraceOptions_5796_);
lean_ctor_set_uint8(v___x_5800_, sizeof(void*)*14, v_diag_5793_);
lean_ctor_set_uint8(v___x_5800_, sizeof(void*)*14 + 1, v_suppressElabErrors_5795_);
v___x_5845_ = lean_nat_dec_lt(v___x_5797_, v___x_5798_);
if (v___x_5845_ == 0)
{
goto v___jp_5828_;
}
else
{
lean_object* v___x_5846_; uint8_t v___x_5847_; 
v___x_5846_ = lean_box(0);
v___x_5847_ = lean_nat_dec_le(v___x_5798_, v___x_5798_);
if (v___x_5847_ == 0)
{
if (v___x_5845_ == 0)
{
goto v___jp_5828_;
}
else
{
size_t v___x_5848_; size_t v___x_5849_; lean_object* v___x_5850_; 
v___x_5848_ = ((size_t)0ULL);
v___x_5849_ = lean_usize_of_nat(v___x_5798_);
v___x_5850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5755_, v___x_5848_, v___x_5849_, v___x_5846_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
v___y_5844_ = v___x_5850_;
goto v___jp_5843_;
}
}
else
{
size_t v___x_5851_; size_t v___x_5852_; lean_object* v___x_5853_; 
v___x_5851_ = ((size_t)0ULL);
v___x_5852_ = lean_usize_of_nat(v___x_5798_);
v___x_5853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5755_, v___x_5851_, v___x_5852_, v___x_5846_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
v___y_5844_ = v___x_5853_;
goto v___jp_5843_;
}
}
v___jp_5801_:
{
lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___f_5805_; lean_object* v___x_5806_; 
v___x_5802_ = lean_box(0);
v___x_5803_ = lean_array_get(v___x_5802_, v___x_5755_, v___x_5797_);
v___x_5804_ = lean_array_to_list(v___x_5755_);
v___f_5805_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5805_, 0, v___x_5804_);
lean_closure_set(v___f_5805_, 1, v_ref_5779_);
lean_closure_set(v___f_5805_, 2, v_tactic_5780_);
v___x_5806_ = l_Lean_Elab_Tactic_run(v___x_5803_, v___f_5805_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v_a_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5817_; 
v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5809_ = v___x_5806_;
v_isShared_5810_ = v_isSharedCheck_5817_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_a_5807_);
lean_dec(v___x_5806_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5817_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
uint8_t v___x_5811_; 
v___x_5811_ = l_List_isEmpty___redArg(v_a_5807_);
if (v___x_5811_ == 0)
{
lean_object* v___x_5812_; 
lean_del_object(v___x_5809_);
v___x_5812_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5807_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
lean_dec_ref(v___x_5800_);
return v___x_5812_;
}
else
{
lean_object* v___x_5813_; lean_object* v___x_5815_; 
lean_dec(v_a_5807_);
lean_dec_ref(v___x_5800_);
v___x_5813_ = lean_box(0);
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 0, v___x_5813_);
v___x_5815_ = v___x_5809_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
else
{
lean_object* v_a_5818_; lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5825_; 
lean_dec_ref(v___x_5800_);
v_a_5818_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5820_ = v___x_5806_;
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
else
{
lean_inc(v_a_5818_);
lean_dec(v___x_5806_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v___x_5823_; 
if (v_isShared_5821_ == 0)
{
v___x_5823_ = v___x_5820_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_a_5818_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
}
v___jp_5826_:
{
if (lean_obj_tag(v___y_5827_) == 0)
{
lean_dec_ref(v___y_5827_);
goto v___jp_5801_;
}
else
{
lean_dec_ref(v___x_5800_);
lean_dec(v_tactic_5780_);
lean_dec(v_ref_5779_);
lean_dec_ref(v___x_5755_);
return v___y_5827_;
}
}
v___jp_5828_:
{
uint8_t v___x_5829_; 
v___x_5829_ = lean_nat_dec_eq(v___x_5798_, v___x_5797_);
if (v___x_5829_ == 0)
{
uint8_t v___x_5830_; 
lean_del_object(v___x_5777_);
v___x_5830_ = lean_nat_dec_lt(v___x_5797_, v___x_5798_);
if (v___x_5830_ == 0)
{
goto v___jp_5801_;
}
else
{
lean_object* v___x_5831_; uint8_t v___x_5832_; 
v___x_5831_ = lean_box(0);
v___x_5832_ = lean_nat_dec_le(v___x_5798_, v___x_5798_);
if (v___x_5832_ == 0)
{
if (v___x_5830_ == 0)
{
goto v___jp_5801_;
}
else
{
size_t v___x_5833_; size_t v___x_5834_; lean_object* v___x_5835_; 
v___x_5833_ = ((size_t)0ULL);
v___x_5834_ = lean_usize_of_nat(v___x_5798_);
v___x_5835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5755_, v___x_5833_, v___x_5834_, v___x_5831_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
v___y_5827_ = v___x_5835_;
goto v___jp_5826_;
}
}
else
{
size_t v___x_5836_; size_t v___x_5837_; lean_object* v___x_5838_; 
v___x_5836_ = ((size_t)0ULL);
v___x_5837_ = lean_usize_of_nat(v___x_5798_);
v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5755_, v___x_5836_, v___x_5837_, v___x_5831_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___x_5800_, v___y_5761_);
v___y_5827_ = v___x_5838_;
goto v___jp_5826_;
}
}
}
else
{
lean_object* v___x_5839_; lean_object* v___x_5841_; 
lean_dec_ref(v___x_5800_);
lean_dec(v_tactic_5780_);
lean_dec(v_ref_5779_);
lean_dec_ref(v___x_5755_);
v___x_5839_ = lean_box(0);
if (v_isShared_5778_ == 0)
{
lean_ctor_set_tag(v___x_5777_, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5839_);
v___x_5841_ = v___x_5777_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
v___jp_5843_:
{
if (lean_obj_tag(v___y_5844_) == 0)
{
lean_dec_ref(v___y_5844_);
goto v___jp_5828_;
}
else
{
lean_dec_ref(v___x_5800_);
lean_dec(v_tactic_5780_);
lean_dec(v_ref_5779_);
lean_del_object(v___x_5777_);
lean_dec_ref(v___x_5755_);
return v___y_5844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5855_, lean_object* v___x_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_){
_start:
{
lean_object* v_res_5864_; 
v_res_5864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5855_, v___x_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
lean_dec(v___y_5862_);
lean_dec_ref(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
return v_res_5864_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5865_){
_start:
{
uint8_t v___x_5866_; 
v___x_5866_ = 0;
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5867_){
_start:
{
uint8_t v_res_5868_; lean_object* v_r_5869_; 
v_res_5868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5867_);
lean_dec(v_x_5867_);
v_r_5869_ = lean_box(v_res_5868_);
return v_r_5869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5876_, size_t v_sz_5877_, size_t v_i_5878_, lean_object* v_b_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_){
_start:
{
uint8_t v___x_5885_; 
v___x_5885_ = lean_usize_dec_lt(v_i_5878_, v_sz_5877_);
if (v___x_5885_ == 0)
{
lean_object* v___x_5886_; 
v___x_5886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5886_, 0, v_b_5879_);
return v___x_5886_;
}
else
{
lean_object* v_snd_5887_; lean_object* v_fst_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5959_; 
v_snd_5887_ = lean_ctor_get(v_b_5879_, 1);
v_fst_5888_ = lean_ctor_get(v_b_5879_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_b_5879_);
if (v_isSharedCheck_5959_ == 0)
{
v___x_5890_ = v_b_5879_;
v_isShared_5891_ = v_isSharedCheck_5959_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_snd_5887_);
lean_inc(v_fst_5888_);
lean_dec(v_b_5879_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5959_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v_array_5892_; lean_object* v_start_5893_; lean_object* v_stop_5894_; uint8_t v___x_5895_; 
v_array_5892_ = lean_ctor_get(v_snd_5887_, 0);
v_start_5893_ = lean_ctor_get(v_snd_5887_, 1);
v_stop_5894_ = lean_ctor_get(v_snd_5887_, 2);
v___x_5895_ = lean_nat_dec_lt(v_start_5893_, v_stop_5894_);
if (v___x_5895_ == 0)
{
lean_object* v___x_5897_; 
if (v_isShared_5891_ == 0)
{
v___x_5897_ = v___x_5890_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_snd_5887_);
v___x_5897_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
lean_object* v___x_5898_; 
v___x_5898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5897_);
return v___x_5898_;
}
}
else
{
lean_object* v___x_5901_; uint8_t v_isShared_5902_; uint8_t v_isSharedCheck_5955_; 
lean_inc(v_stop_5894_);
lean_inc(v_start_5893_);
lean_inc_ref(v_array_5892_);
v_isSharedCheck_5955_ = !lean_is_exclusive(v_snd_5887_);
if (v_isSharedCheck_5955_ == 0)
{
lean_object* v_unused_5956_; lean_object* v_unused_5957_; lean_object* v_unused_5958_; 
v_unused_5956_ = lean_ctor_get(v_snd_5887_, 2);
lean_dec(v_unused_5956_);
v_unused_5957_ = lean_ctor_get(v_snd_5887_, 1);
lean_dec(v_unused_5957_);
v_unused_5958_ = lean_ctor_get(v_snd_5887_, 0);
lean_dec(v_unused_5958_);
v___x_5901_ = v_snd_5887_;
v_isShared_5902_ = v_isSharedCheck_5955_;
goto v_resetjp_5900_;
}
else
{
lean_dec(v_snd_5887_);
v___x_5901_ = lean_box(0);
v_isShared_5902_ = v_isSharedCheck_5955_;
goto v_resetjp_5900_;
}
v_resetjp_5900_:
{
lean_object* v_array_5903_; lean_object* v_start_5904_; lean_object* v_stop_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5910_; 
v_array_5903_ = lean_ctor_get(v_fst_5888_, 0);
v_start_5904_ = lean_ctor_get(v_fst_5888_, 1);
v_stop_5905_ = lean_ctor_get(v_fst_5888_, 2);
v___x_5906_ = lean_array_fget(v_array_5892_, v_start_5893_);
v___x_5907_ = lean_unsigned_to_nat(1u);
v___x_5908_ = lean_nat_add(v_start_5893_, v___x_5907_);
lean_dec(v_start_5893_);
if (v_isShared_5902_ == 0)
{
lean_ctor_set(v___x_5901_, 1, v___x_5908_);
v___x_5910_ = v___x_5901_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_array_5892_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v___x_5908_);
lean_ctor_set(v_reuseFailAlloc_5954_, 2, v_stop_5894_);
v___x_5910_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
uint8_t v___x_5911_; 
v___x_5911_ = lean_nat_dec_lt(v_start_5904_, v_stop_5905_);
if (v___x_5911_ == 0)
{
lean_object* v___x_5913_; 
lean_dec(v___x_5906_);
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 1, v___x_5910_);
v___x_5913_ = v___x_5890_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v___x_5910_);
v___x_5913_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
lean_object* v___x_5914_; 
v___x_5914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
return v___x_5914_;
}
}
else
{
lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5950_; 
lean_inc(v_stop_5905_);
lean_inc(v_start_5904_);
lean_inc_ref(v_array_5903_);
v_isSharedCheck_5950_ = !lean_is_exclusive(v_fst_5888_);
if (v_isSharedCheck_5950_ == 0)
{
lean_object* v_unused_5951_; lean_object* v_unused_5952_; lean_object* v_unused_5953_; 
v_unused_5951_ = lean_ctor_get(v_fst_5888_, 2);
lean_dec(v_unused_5951_);
v_unused_5952_ = lean_ctor_get(v_fst_5888_, 1);
lean_dec(v_unused_5952_);
v_unused_5953_ = lean_ctor_get(v_fst_5888_, 0);
lean_dec(v_unused_5953_);
v___x_5917_ = v_fst_5888_;
v_isShared_5918_ = v_isSharedCheck_5950_;
goto v_resetjp_5916_;
}
else
{
lean_dec(v_fst_5888_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5950_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
lean_object* v___f_5919_; lean_object* v_a_5920_; lean_object* v___x_5921_; lean_object* v___y_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; uint8_t v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___f_5919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5920_ = lean_array_uget_borrowed(v_as_5876_, v_i_5878_);
v___x_5921_ = lean_array_fget_borrowed(v_array_5903_, v_start_5904_);
lean_inc(v___x_5921_);
v___y_5922_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5922_, 0, v___x_5906_);
lean_closure_set(v___y_5922_, 1, v___x_5921_);
lean_inc(v_a_5920_);
v___x_5923_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5923_, 0, lean_box(0));
lean_closure_set(v___x_5923_, 1, v_a_5920_);
lean_closure_set(v___x_5923_, 2, v___y_5922_);
v___x_5924_ = lean_box(0);
v___x_5925_ = lean_box(0);
v___x_5926_ = lean_box(1);
v___x_5927_ = 0;
v___x_5928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5929_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5929_, 0, v___x_5924_);
lean_ctor_set(v___x_5929_, 1, v___x_5925_);
lean_ctor_set(v___x_5929_, 2, v___x_5924_);
lean_ctor_set(v___x_5929_, 3, v___f_5919_);
lean_ctor_set(v___x_5929_, 4, v___x_5926_);
lean_ctor_set(v___x_5929_, 5, v___x_5926_);
lean_ctor_set(v___x_5929_, 6, v___x_5924_);
lean_ctor_set(v___x_5929_, 7, v___x_5928_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8, v___x_5911_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 1, v___x_5911_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 2, v___x_5911_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 3, v___x_5911_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 4, v___x_5927_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 5, v___x_5927_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 6, v___x_5927_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 7, v___x_5927_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 8, v___x_5911_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 9, v___x_5927_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*8 + 10, v___x_5911_);
v___x_5930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5931_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5923_, v___x_5929_, v___x_5930_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
if (lean_obj_tag(v___x_5931_) == 0)
{
lean_object* v___x_5932_; lean_object* v___x_5934_; 
lean_dec_ref(v___x_5931_);
v___x_5932_ = lean_nat_add(v_start_5904_, v___x_5907_);
lean_dec(v_start_5904_);
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 1, v___x_5932_);
v___x_5934_ = v___x_5917_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_array_5903_);
lean_ctor_set(v_reuseFailAlloc_5941_, 1, v___x_5932_);
lean_ctor_set(v_reuseFailAlloc_5941_, 2, v_stop_5905_);
v___x_5934_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
lean_object* v___x_5936_; 
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 1, v___x_5910_);
lean_ctor_set(v___x_5890_, 0, v___x_5934_);
v___x_5936_ = v___x_5890_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5934_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v___x_5910_);
v___x_5936_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
size_t v___x_5937_; size_t v___x_5938_; 
v___x_5937_ = ((size_t)1ULL);
v___x_5938_ = lean_usize_add(v_i_5878_, v___x_5937_);
v_i_5878_ = v___x_5938_;
v_b_5879_ = v___x_5936_;
goto _start;
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_del_object(v___x_5917_);
lean_dec_ref(v___x_5910_);
lean_dec(v_stop_5905_);
lean_dec(v_start_5904_);
lean_dec_ref(v_array_5903_);
lean_del_object(v___x_5890_);
v_a_5942_ = lean_ctor_get(v___x_5931_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5931_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5931_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5931_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5960_, lean_object* v_sz_5961_, lean_object* v_i_5962_, lean_object* v_b_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_){
_start:
{
size_t v_sz_boxed_5969_; size_t v_i_boxed_5970_; lean_object* v_res_5971_; 
v_sz_boxed_5969_ = lean_unbox_usize(v_sz_5961_);
lean_dec(v_sz_5961_);
v_i_boxed_5970_ = lean_unbox_usize(v_i_5962_);
lean_dec(v_i_5962_);
v_res_5971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5960_, v_sz_boxed_5969_, v_i_boxed_5970_, v_b_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
lean_dec(v___y_5967_);
lean_dec_ref(v___y_5966_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
lean_dec_ref(v_as_5960_);
return v_res_5971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5972_, lean_object* v_decrTactics_5973_, lean_object* v_argsPacker_5974_, lean_object* v_funNames_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_){
_start:
{
lean_object* v___x_5981_; 
lean_inc_ref(v_value_5972_);
v___x_5981_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5972_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
if (lean_obj_tag(v___x_5981_) == 0)
{
lean_object* v_a_5982_; lean_object* v___x_5983_; 
v_a_5982_ = lean_ctor_get(v___x_5981_, 0);
lean_inc(v_a_5982_);
lean_dec_ref(v___x_5981_);
v___x_5983_ = l_Lean_Elab_WF_assignSubsumed(v_a_5982_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
lean_dec(v_a_5982_);
if (lean_obj_tag(v___x_5983_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
v_a_5984_ = lean_ctor_get(v___x_5983_, 0);
lean_inc(v_a_5984_);
lean_dec_ref(v___x_5983_);
v___x_5985_ = lean_array_get_size(v_decrTactics_5973_);
v___x_5986_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5974_, v___x_5985_, v_a_5984_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
lean_dec(v_a_5984_);
if (lean_obj_tag(v___x_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; size_t v_sz_5993_; size_t v___x_5994_; lean_object* v___x_5995_; 
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
lean_inc(v_a_5987_);
lean_dec_ref(v___x_5986_);
v___x_5988_ = lean_unsigned_to_nat(0u);
v___x_5989_ = lean_array_get_size(v_a_5987_);
v___x_5990_ = l_Array_toSubarray___redArg(v_a_5987_, v___x_5988_, v___x_5989_);
v___x_5991_ = l_Array_toSubarray___redArg(v_decrTactics_5973_, v___x_5988_, v___x_5985_);
v___x_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5990_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
v_sz_5993_ = lean_array_size(v_funNames_5975_);
v___x_5994_ = ((size_t)0ULL);
v___x_5995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5975_, v_sz_5993_, v___x_5994_, v___x_5992_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
if (lean_obj_tag(v___x_5995_) == 0)
{
lean_object* v___x_5996_; 
lean_dec_ref(v___x_5995_);
v___x_5996_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5972_, v___y_5977_);
return v___x_5996_;
}
else
{
lean_object* v_a_5997_; lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6004_; 
lean_dec_ref(v_value_5972_);
v_a_5997_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5999_ = v___x_5995_;
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
else
{
lean_inc(v_a_5997_);
lean_dec(v___x_5995_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6002_; 
if (v_isShared_6000_ == 0)
{
v___x_6002_ = v___x_5999_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_a_5997_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
else
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_dec_ref(v_decrTactics_5973_);
lean_dec_ref(v_value_5972_);
v_a_6005_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___x_5986_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_5986_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_6008_ == 0)
{
v___x_6010_ = v___x_6007_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
v___x_6010_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
return v___x_6010_;
}
}
}
}
else
{
lean_object* v_a_6013_; lean_object* v___x_6015_; uint8_t v_isShared_6016_; uint8_t v_isSharedCheck_6020_; 
lean_dec_ref(v_decrTactics_5973_);
lean_dec_ref(v_value_5972_);
v_a_6013_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_6020_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_6020_ == 0)
{
v___x_6015_ = v___x_5983_;
v_isShared_6016_ = v_isSharedCheck_6020_;
goto v_resetjp_6014_;
}
else
{
lean_inc(v_a_6013_);
lean_dec(v___x_5983_);
v___x_6015_ = lean_box(0);
v_isShared_6016_ = v_isSharedCheck_6020_;
goto v_resetjp_6014_;
}
v_resetjp_6014_:
{
lean_object* v___x_6018_; 
if (v_isShared_6016_ == 0)
{
v___x_6018_ = v___x_6015_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6019_; 
v_reuseFailAlloc_6019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6019_, 0, v_a_6013_);
v___x_6018_ = v_reuseFailAlloc_6019_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
return v___x_6018_;
}
}
}
}
else
{
lean_object* v_a_6021_; lean_object* v___x_6023_; uint8_t v_isShared_6024_; uint8_t v_isSharedCheck_6028_; 
lean_dec_ref(v_decrTactics_5973_);
lean_dec_ref(v_value_5972_);
v_a_6021_ = lean_ctor_get(v___x_5981_, 0);
v_isSharedCheck_6028_ = !lean_is_exclusive(v___x_5981_);
if (v_isSharedCheck_6028_ == 0)
{
v___x_6023_ = v___x_5981_;
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
else
{
lean_inc(v_a_6021_);
lean_dec(v___x_5981_);
v___x_6023_ = lean_box(0);
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
v_resetjp_6022_:
{
lean_object* v___x_6026_; 
if (v_isShared_6024_ == 0)
{
v___x_6026_ = v___x_6023_;
goto v_reusejp_6025_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
v___x_6026_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6025_;
}
v_reusejp_6025_:
{
return v___x_6026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6029_, lean_object* v_decrTactics_6030_, lean_object* v_argsPacker_6031_, lean_object* v_funNames_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_){
_start:
{
lean_object* v_res_6038_; 
v_res_6038_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6029_, v_decrTactics_6030_, v_argsPacker_6031_, v_funNames_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
lean_dec(v___y_6036_);
lean_dec_ref(v___y_6035_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec_ref(v_funNames_6032_);
lean_dec_ref(v_argsPacker_6031_);
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6039_, uint8_t v_isExporting_6040_, lean_object* v___x_6041_, lean_object* v___y_6042_, lean_object* v___x_6043_, lean_object* v_a_x3f_6044_){
_start:
{
lean_object* v___x_6046_; lean_object* v_env_6047_; lean_object* v_nextMacroScope_6048_; lean_object* v_ngen_6049_; lean_object* v_auxDeclNGen_6050_; lean_object* v_traceState_6051_; lean_object* v_messages_6052_; lean_object* v_infoState_6053_; lean_object* v_snapshotTasks_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6079_; 
v___x_6046_ = lean_st_ref_take(v___y_6039_);
v_env_6047_ = lean_ctor_get(v___x_6046_, 0);
v_nextMacroScope_6048_ = lean_ctor_get(v___x_6046_, 1);
v_ngen_6049_ = lean_ctor_get(v___x_6046_, 2);
v_auxDeclNGen_6050_ = lean_ctor_get(v___x_6046_, 3);
v_traceState_6051_ = lean_ctor_get(v___x_6046_, 4);
v_messages_6052_ = lean_ctor_get(v___x_6046_, 6);
v_infoState_6053_ = lean_ctor_get(v___x_6046_, 7);
v_snapshotTasks_6054_ = lean_ctor_get(v___x_6046_, 8);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6046_);
if (v_isSharedCheck_6079_ == 0)
{
lean_object* v_unused_6080_; 
v_unused_6080_ = lean_ctor_get(v___x_6046_, 5);
lean_dec(v_unused_6080_);
v___x_6056_ = v___x_6046_;
v_isShared_6057_ = v_isSharedCheck_6079_;
goto v_resetjp_6055_;
}
else
{
lean_inc(v_snapshotTasks_6054_);
lean_inc(v_infoState_6053_);
lean_inc(v_messages_6052_);
lean_inc(v_traceState_6051_);
lean_inc(v_auxDeclNGen_6050_);
lean_inc(v_ngen_6049_);
lean_inc(v_nextMacroScope_6048_);
lean_inc(v_env_6047_);
lean_dec(v___x_6046_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6079_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
lean_object* v___x_6058_; lean_object* v___x_6060_; 
v___x_6058_ = l_Lean_Environment_setExporting(v_env_6047_, v_isExporting_6040_);
if (v_isShared_6057_ == 0)
{
lean_ctor_set(v___x_6056_, 5, v___x_6041_);
lean_ctor_set(v___x_6056_, 0, v___x_6058_);
v___x_6060_ = v___x_6056_;
goto v_reusejp_6059_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6058_);
lean_ctor_set(v_reuseFailAlloc_6078_, 1, v_nextMacroScope_6048_);
lean_ctor_set(v_reuseFailAlloc_6078_, 2, v_ngen_6049_);
lean_ctor_set(v_reuseFailAlloc_6078_, 3, v_auxDeclNGen_6050_);
lean_ctor_set(v_reuseFailAlloc_6078_, 4, v_traceState_6051_);
lean_ctor_set(v_reuseFailAlloc_6078_, 5, v___x_6041_);
lean_ctor_set(v_reuseFailAlloc_6078_, 6, v_messages_6052_);
lean_ctor_set(v_reuseFailAlloc_6078_, 7, v_infoState_6053_);
lean_ctor_set(v_reuseFailAlloc_6078_, 8, v_snapshotTasks_6054_);
v___x_6060_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6059_;
}
v_reusejp_6059_:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v_mctx_6063_; lean_object* v_zetaDeltaFVarIds_6064_; lean_object* v_postponed_6065_; lean_object* v_diag_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6076_; 
v___x_6061_ = lean_st_ref_set(v___y_6039_, v___x_6060_);
v___x_6062_ = lean_st_ref_take(v___y_6042_);
v_mctx_6063_ = lean_ctor_get(v___x_6062_, 0);
v_zetaDeltaFVarIds_6064_ = lean_ctor_get(v___x_6062_, 2);
v_postponed_6065_ = lean_ctor_get(v___x_6062_, 3);
v_diag_6066_ = lean_ctor_get(v___x_6062_, 4);
v_isSharedCheck_6076_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6076_ == 0)
{
lean_object* v_unused_6077_; 
v_unused_6077_ = lean_ctor_get(v___x_6062_, 1);
lean_dec(v_unused_6077_);
v___x_6068_ = v___x_6062_;
v_isShared_6069_ = v_isSharedCheck_6076_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_diag_6066_);
lean_inc(v_postponed_6065_);
lean_inc(v_zetaDeltaFVarIds_6064_);
lean_inc(v_mctx_6063_);
lean_dec(v___x_6062_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6076_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6069_ == 0)
{
lean_ctor_set(v___x_6068_, 1, v___x_6043_);
v___x_6071_ = v___x_6068_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_mctx_6063_);
lean_ctor_set(v_reuseFailAlloc_6075_, 1, v___x_6043_);
lean_ctor_set(v_reuseFailAlloc_6075_, 2, v_zetaDeltaFVarIds_6064_);
lean_ctor_set(v_reuseFailAlloc_6075_, 3, v_postponed_6065_);
lean_ctor_set(v_reuseFailAlloc_6075_, 4, v_diag_6066_);
v___x_6071_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6072_ = lean_st_ref_set(v___y_6042_, v___x_6071_);
v___x_6073_ = lean_box(0);
v___x_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
return v___x_6074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6081_, lean_object* v_isExporting_6082_, lean_object* v___x_6083_, lean_object* v___y_6084_, lean_object* v___x_6085_, lean_object* v_a_x3f_6086_, lean_object* v___y_6087_){
_start:
{
uint8_t v_isExporting_boxed_6088_; lean_object* v_res_6089_; 
v_isExporting_boxed_6088_ = lean_unbox(v_isExporting_6082_);
v_res_6089_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6081_, v_isExporting_boxed_6088_, v___x_6083_, v___y_6084_, v___x_6085_, v_a_x3f_6086_);
lean_dec(v_a_x3f_6086_);
lean_dec(v___y_6084_);
lean_dec(v___y_6081_);
return v_res_6089_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6090_; 
v___x_6090_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6090_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; 
v___x_6091_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
return v___x_6092_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; 
v___x_6093_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
return v___x_6094_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6096_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
lean_ctor_set(v___x_6096_, 2, v___x_6095_);
lean_ctor_set(v___x_6096_, 3, v___x_6095_);
lean_ctor_set(v___x_6096_, 4, v___x_6095_);
lean_ctor_set(v___x_6096_, 5, v___x_6095_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6097_, uint8_t v_isExporting_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v___x_6104_; lean_object* v_env_6105_; uint8_t v_isExporting_6106_; lean_object* v___x_6107_; lean_object* v_env_6108_; lean_object* v_nextMacroScope_6109_; lean_object* v_ngen_6110_; lean_object* v_auxDeclNGen_6111_; lean_object* v_traceState_6112_; lean_object* v_messages_6113_; lean_object* v_infoState_6114_; lean_object* v_snapshotTasks_6115_; lean_object* v___x_6117_; uint8_t v_isShared_6118_; uint8_t v_isSharedCheck_6169_; 
v___x_6104_ = lean_st_ref_get(v___y_6102_);
v_env_6105_ = lean_ctor_get(v___x_6104_, 0);
lean_inc_ref(v_env_6105_);
lean_dec(v___x_6104_);
v_isExporting_6106_ = lean_ctor_get_uint8(v_env_6105_, sizeof(void*)*8);
lean_dec_ref(v_env_6105_);
v___x_6107_ = lean_st_ref_take(v___y_6102_);
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
v___x_6119_ = l_Lean_Environment_setExporting(v_env_6108_, v_isExporting_6098_);
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
v___x_6123_ = lean_st_ref_set(v___y_6102_, v___x_6122_);
v___x_6124_ = lean_st_ref_take(v___y_6100_);
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
v___x_6135_ = lean_st_ref_set(v___y_6100_, v___x_6134_);
lean_inc(v___y_6102_);
lean_inc_ref(v___y_6101_);
lean_inc(v___y_6100_);
lean_inc_ref(v___y_6099_);
v_r_6136_ = lean_apply_5(v_x_6097_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_, lean_box(0));
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
v___x_6143_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6102_, v_isExporting_6106_, v___x_6120_, v___y_6100_, v___x_6132_, v___x_6142_);
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
lean_dec_ref(v_r_6136_);
v___x_6155_ = lean_box(0);
v___x_6156_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6102_, v_isExporting_6106_, v___x_6120_, v___y_6100_, v___x_6132_, v___x_6155_);
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6171_, lean_object* v_isExporting_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_){
_start:
{
uint8_t v_isExporting_boxed_6178_; lean_object* v_res_6179_; 
v_isExporting_boxed_6178_ = lean_unbox(v_isExporting_6172_);
v_res_6179_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6171_, v_isExporting_boxed_6178_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
lean_dec(v___y_6176_);
lean_dec_ref(v___y_6175_);
lean_dec(v___y_6174_);
lean_dec_ref(v___y_6173_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6180_, uint8_t v_when_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_){
_start:
{
if (v_when_6181_ == 0)
{
lean_object* v___x_6187_; 
lean_inc(v___y_6185_);
lean_inc_ref(v___y_6184_);
lean_inc(v___y_6183_);
lean_inc_ref(v___y_6182_);
v___x_6187_ = lean_apply_5(v_x_6180_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, lean_box(0));
return v___x_6187_;
}
else
{
uint8_t v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = 0;
v___x_6189_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6180_, v___x_6188_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_);
return v___x_6189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6190_, lean_object* v_when_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_){
_start:
{
uint8_t v_when_boxed_6197_; lean_object* v_res_6198_; 
v_when_boxed_6197_ = lean_unbox(v_when_6191_);
v_res_6198_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6190_, v_when_boxed_6197_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6199_, lean_object* v_argsPacker_6200_, lean_object* v_decrTactics_6201_, lean_object* v_value_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_){
_start:
{
lean_object* v___f_6208_; uint8_t v___x_6209_; lean_object* v___x_6210_; 
v___f_6208_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6208_, 0, v_value_6202_);
lean_closure_set(v___f_6208_, 1, v_decrTactics_6201_);
lean_closure_set(v___f_6208_, 2, v_argsPacker_6200_);
lean_closure_set(v___f_6208_, 3, v_funNames_6199_);
v___x_6209_ = 1;
v___x_6210_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6208_, v___x_6209_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6211_, lean_object* v_argsPacker_6212_, lean_object* v_decrTactics_6213_, lean_object* v_value_6214_, lean_object* v_a_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_){
_start:
{
lean_object* v_res_6220_; 
v_res_6220_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6211_, v_argsPacker_6212_, v_decrTactics_6213_, v_value_6214_, v_a_6215_, v_a_6216_, v_a_6217_, v_a_6218_);
lean_dec(v_a_6218_);
lean_dec_ref(v_a_6217_);
lean_dec(v_a_6216_);
lean_dec_ref(v_a_6215_);
return v_res_6220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6221_, lean_object* v_msg_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_){
_start:
{
lean_object* v___x_6230_; 
v___x_6230_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
return v___x_6230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6231_, lean_object* v_msg_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_){
_start:
{
lean_object* v_res_6240_; 
v_res_6240_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6231_, v_msg_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
lean_dec(v___y_6238_);
lean_dec_ref(v___y_6237_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_){
_start:
{
lean_object* v___x_6250_; 
v___x_6250_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6248_);
return v___x_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_){
_start:
{
lean_object* v_res_6260_; 
v_res_6260_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_);
lean_dec(v___y_6258_);
lean_dec_ref(v___y_6257_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
lean_dec(v___y_6254_);
lean_dec_ref(v___y_6253_);
lean_dec(v___y_6252_);
lean_dec_ref(v___y_6251_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6261_, lean_object* v_x_6262_, lean_object* v_mkInfoTree_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_){
_start:
{
lean_object* v___x_6273_; 
v___x_6273_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6262_, v_mkInfoTree_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_);
return v___x_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6274_, lean_object* v_x_6275_, lean_object* v_mkInfoTree_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
lean_object* v_res_6286_; 
v_res_6286_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6274_, v_x_6275_, v_mkInfoTree_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6282_);
lean_dec_ref(v___y_6281_);
lean_dec(v___y_6280_);
lean_dec_ref(v___y_6279_);
lean_dec(v___y_6278_);
lean_dec_ref(v___y_6277_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6287_, size_t v_i_6288_, size_t v_stop_6289_, lean_object* v_b_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_){
_start:
{
lean_object* v___x_6298_; 
v___x_6298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6287_, v_i_6288_, v_stop_6289_, v_b_6290_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
return v___x_6298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6299_, lean_object* v_i_6300_, lean_object* v_stop_6301_, lean_object* v_b_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_){
_start:
{
size_t v_i_boxed_6310_; size_t v_stop_boxed_6311_; lean_object* v_res_6312_; 
v_i_boxed_6310_ = lean_unbox_usize(v_i_6300_);
lean_dec(v_i_6300_);
v_stop_boxed_6311_ = lean_unbox_usize(v_stop_6301_);
lean_dec(v_stop_6301_);
v_res_6312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6299_, v_i_boxed_6310_, v_stop_boxed_6311_, v_b_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_, v___y_6308_);
lean_dec(v___y_6308_);
lean_dec_ref(v___y_6307_);
lean_dec(v___y_6306_);
lean_dec_ref(v___y_6305_);
lean_dec(v___y_6304_);
lean_dec_ref(v___y_6303_);
lean_dec_ref(v_as_6299_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6313_, lean_object* v_x_6314_, uint8_t v_isExporting_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_){
_start:
{
lean_object* v___x_6321_; 
v___x_6321_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6314_, v_isExporting_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_);
return v___x_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6322_, lean_object* v_x_6323_, lean_object* v_isExporting_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_){
_start:
{
uint8_t v_isExporting_boxed_6330_; lean_object* v_res_6331_; 
v_isExporting_boxed_6330_ = lean_unbox(v_isExporting_6324_);
v_res_6331_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6322_, v_x_6323_, v_isExporting_boxed_6330_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
lean_dec(v___y_6326_);
lean_dec_ref(v___y_6325_);
return v_res_6331_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6332_, lean_object* v_x_6333_, uint8_t v_when_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6333_, v_when_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_);
return v___x_6340_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6341_, lean_object* v_x_6342_, lean_object* v_when_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_){
_start:
{
uint8_t v_when_boxed_6349_; lean_object* v_res_6350_; 
v_when_boxed_6349_ = lean_unbox(v_when_6343_);
v_res_6350_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6341_, v_x_6342_, v_when_boxed_6349_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_);
lean_dec(v___y_6347_);
lean_dec_ref(v___y_6346_);
lean_dec(v___y_6345_);
lean_dec_ref(v___y_6344_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6351_, lean_object* v_macroStack_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_){
_start:
{
lean_object* v___x_6360_; 
v___x_6360_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6351_, v_macroStack_6352_, v___y_6357_);
return v___x_6360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6361_, lean_object* v_macroStack_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_){
_start:
{
lean_object* v_res_6370_; 
v_res_6370_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6361_, v_macroStack_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_, v___y_6368_);
lean_dec(v___y_6368_);
lean_dec_ref(v___y_6367_);
lean_dec(v___y_6366_);
lean_dec_ref(v___y_6365_);
lean_dec(v___y_6364_);
lean_dec_ref(v___y_6363_);
return v_res_6370_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6377_ = lean_box(0);
v___x_6378_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6379_ = l_Lean_mkConst(v___x_6378_, v___x_6377_);
return v___x_6379_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; 
v___x_6384_ = lean_box(0);
v___x_6385_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6386_ = l_Lean_mkConst(v___x_6385_, v___x_6384_);
return v___x_6386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_){
_start:
{
lean_object* v___x_6393_; 
v___x_6393_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6387_, v_a_6389_);
if (lean_obj_tag(v___x_6393_) == 0)
{
lean_object* v_a_6394_; lean_object* v___x_6396_; uint8_t v_isShared_6397_; uint8_t v_isSharedCheck_6461_; 
v_a_6394_ = lean_ctor_get(v___x_6393_, 0);
v_isSharedCheck_6461_ = !lean_is_exclusive(v___x_6393_);
if (v_isSharedCheck_6461_ == 0)
{
v___x_6396_ = v___x_6393_;
v_isShared_6397_ = v_isSharedCheck_6461_;
goto v_resetjp_6395_;
}
else
{
lean_inc(v_a_6394_);
lean_dec(v___x_6393_);
v___x_6396_ = lean_box(0);
v_isShared_6397_ = v_isSharedCheck_6461_;
goto v_resetjp_6395_;
}
v_resetjp_6395_:
{
lean_object* v___x_6403_; uint8_t v___x_6404_; 
v___x_6403_ = l_Lean_Expr_cleanupAnnotations(v_a_6394_);
v___x_6404_ = l_Lean_Expr_isApp(v___x_6403_);
if (v___x_6404_ == 0)
{
lean_dec_ref(v___x_6403_);
goto v___jp_6398_;
}
else
{
lean_object* v_arg_6405_; lean_object* v___x_6406_; uint8_t v___x_6407_; 
v_arg_6405_ = lean_ctor_get(v___x_6403_, 1);
lean_inc_ref(v_arg_6405_);
v___x_6406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6403_);
v___x_6407_ = l_Lean_Expr_isApp(v___x_6406_);
if (v___x_6407_ == 0)
{
lean_dec_ref(v___x_6406_);
lean_dec_ref(v_arg_6405_);
goto v___jp_6398_;
}
else
{
lean_object* v_arg_6408_; lean_object* v___x_6409_; uint8_t v___x_6410_; 
v_arg_6408_ = lean_ctor_get(v___x_6406_, 1);
lean_inc_ref(v_arg_6408_);
v___x_6409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6406_);
v___x_6410_ = l_Lean_Expr_isApp(v___x_6409_);
if (v___x_6410_ == 0)
{
lean_dec_ref(v___x_6409_);
lean_dec_ref(v_arg_6408_);
lean_dec_ref(v_arg_6405_);
goto v___jp_6398_;
}
else
{
lean_object* v_arg_6411_; lean_object* v___x_6412_; uint8_t v___x_6413_; 
v_arg_6411_ = lean_ctor_get(v___x_6409_, 1);
lean_inc_ref(v_arg_6411_);
v___x_6412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6409_);
v___x_6413_ = l_Lean_Expr_isApp(v___x_6412_);
if (v___x_6413_ == 0)
{
lean_dec_ref(v___x_6412_);
lean_dec_ref(v_arg_6411_);
lean_dec_ref(v_arg_6408_);
lean_dec_ref(v_arg_6405_);
goto v___jp_6398_;
}
else
{
lean_object* v___x_6414_; lean_object* v___x_6415_; uint8_t v___x_6416_; 
v___x_6414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6412_);
v___x_6415_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6416_ = l_Lean_Expr_isConstOf(v___x_6414_, v___x_6415_);
lean_dec_ref(v___x_6414_);
if (v___x_6416_ == 0)
{
lean_dec_ref(v_arg_6411_);
lean_dec_ref(v_arg_6408_);
lean_dec_ref(v_arg_6405_);
goto v___jp_6398_;
}
else
{
lean_object* v___x_6417_; lean_object* v___x_6418_; 
lean_del_object(v___x_6396_);
v___x_6417_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6418_ = l_Lean_Meta_isExprDefEq(v_arg_6411_, v___x_6417_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
if (lean_obj_tag(v___x_6418_) == 0)
{
lean_object* v_a_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6452_; 
v_a_6419_ = lean_ctor_get(v___x_6418_, 0);
v_isSharedCheck_6452_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6452_ == 0)
{
v___x_6421_ = v___x_6418_;
v_isShared_6422_ = v_isSharedCheck_6452_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_a_6419_);
lean_dec(v___x_6418_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6452_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
uint8_t v___x_6423_; 
v___x_6423_ = lean_unbox(v_a_6419_);
lean_dec(v_a_6419_);
if (v___x_6423_ == 0)
{
lean_object* v___x_6424_; lean_object* v___x_6426_; 
lean_dec_ref(v_arg_6408_);
lean_dec_ref(v_arg_6405_);
v___x_6424_ = lean_box(0);
if (v_isShared_6422_ == 0)
{
lean_ctor_set(v___x_6421_, 0, v___x_6424_);
v___x_6426_ = v___x_6421_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6427_; 
v_reuseFailAlloc_6427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6427_, 0, v___x_6424_);
v___x_6426_ = v_reuseFailAlloc_6427_;
goto v_reusejp_6425_;
}
v_reusejp_6425_:
{
return v___x_6426_;
}
}
else
{
lean_object* v___x_6428_; lean_object* v___x_6429_; 
lean_del_object(v___x_6421_);
v___x_6428_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6429_ = l_Lean_Meta_isExprDefEq(v_arg_6405_, v___x_6428_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
if (lean_obj_tag(v___x_6429_) == 0)
{
lean_object* v_a_6430_; lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6443_; 
v_a_6430_ = lean_ctor_get(v___x_6429_, 0);
v_isSharedCheck_6443_ = !lean_is_exclusive(v___x_6429_);
if (v_isSharedCheck_6443_ == 0)
{
v___x_6432_ = v___x_6429_;
v_isShared_6433_ = v_isSharedCheck_6443_;
goto v_resetjp_6431_;
}
else
{
lean_inc(v_a_6430_);
lean_dec(v___x_6429_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6443_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
uint8_t v___x_6434_; 
v___x_6434_ = lean_unbox(v_a_6430_);
lean_dec(v_a_6430_);
if (v___x_6434_ == 0)
{
lean_object* v___x_6435_; lean_object* v___x_6437_; 
lean_dec_ref(v_arg_6408_);
v___x_6435_ = lean_box(0);
if (v_isShared_6433_ == 0)
{
lean_ctor_set(v___x_6432_, 0, v___x_6435_);
v___x_6437_ = v___x_6432_;
goto v_reusejp_6436_;
}
else
{
lean_object* v_reuseFailAlloc_6438_; 
v_reuseFailAlloc_6438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6438_, 0, v___x_6435_);
v___x_6437_ = v_reuseFailAlloc_6438_;
goto v_reusejp_6436_;
}
v_reusejp_6436_:
{
return v___x_6437_;
}
}
else
{
lean_object* v___x_6439_; lean_object* v___x_6441_; 
v___x_6439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6439_, 0, v_arg_6408_);
if (v_isShared_6433_ == 0)
{
lean_ctor_set(v___x_6432_, 0, v___x_6439_);
v___x_6441_ = v___x_6432_;
goto v_reusejp_6440_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v___x_6439_);
v___x_6441_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6440_;
}
v_reusejp_6440_:
{
return v___x_6441_;
}
}
}
}
else
{
lean_object* v_a_6444_; lean_object* v___x_6446_; uint8_t v_isShared_6447_; uint8_t v_isSharedCheck_6451_; 
lean_dec_ref(v_arg_6408_);
v_a_6444_ = lean_ctor_get(v___x_6429_, 0);
v_isSharedCheck_6451_ = !lean_is_exclusive(v___x_6429_);
if (v_isSharedCheck_6451_ == 0)
{
v___x_6446_ = v___x_6429_;
v_isShared_6447_ = v_isSharedCheck_6451_;
goto v_resetjp_6445_;
}
else
{
lean_inc(v_a_6444_);
lean_dec(v___x_6429_);
v___x_6446_ = lean_box(0);
v_isShared_6447_ = v_isSharedCheck_6451_;
goto v_resetjp_6445_;
}
v_resetjp_6445_:
{
lean_object* v___x_6449_; 
if (v_isShared_6447_ == 0)
{
v___x_6449_ = v___x_6446_;
goto v_reusejp_6448_;
}
else
{
lean_object* v_reuseFailAlloc_6450_; 
v_reuseFailAlloc_6450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6450_, 0, v_a_6444_);
v___x_6449_ = v_reuseFailAlloc_6450_;
goto v_reusejp_6448_;
}
v_reusejp_6448_:
{
return v___x_6449_;
}
}
}
}
}
}
else
{
lean_object* v_a_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6460_; 
lean_dec_ref(v_arg_6408_);
lean_dec_ref(v_arg_6405_);
v_a_6453_ = lean_ctor_get(v___x_6418_, 0);
v_isSharedCheck_6460_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6460_ == 0)
{
v___x_6455_ = v___x_6418_;
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_a_6453_);
lean_dec(v___x_6418_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6458_; 
if (v_isShared_6456_ == 0)
{
v___x_6458_ = v___x_6455_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
v___x_6458_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
return v___x_6458_;
}
}
}
}
}
}
}
}
v___jp_6398_:
{
lean_object* v___x_6399_; lean_object* v___x_6401_; 
v___x_6399_ = lean_box(0);
if (v_isShared_6397_ == 0)
{
lean_ctor_set(v___x_6396_, 0, v___x_6399_);
v___x_6401_ = v___x_6396_;
goto v_reusejp_6400_;
}
else
{
lean_object* v_reuseFailAlloc_6402_; 
v_reuseFailAlloc_6402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6402_, 0, v___x_6399_);
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
else
{
lean_object* v_a_6462_; lean_object* v___x_6464_; uint8_t v_isShared_6465_; uint8_t v_isSharedCheck_6469_; 
v_a_6462_ = lean_ctor_get(v___x_6393_, 0);
v_isSharedCheck_6469_ = !lean_is_exclusive(v___x_6393_);
if (v_isSharedCheck_6469_ == 0)
{
v___x_6464_ = v___x_6393_;
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
else
{
lean_inc(v_a_6462_);
lean_dec(v___x_6393_);
v___x_6464_ = lean_box(0);
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
v_resetjp_6463_:
{
lean_object* v___x_6467_; 
if (v_isShared_6465_ == 0)
{
v___x_6467_ = v___x_6464_;
goto v_reusejp_6466_;
}
else
{
lean_object* v_reuseFailAlloc_6468_; 
v_reuseFailAlloc_6468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6468_, 0, v_a_6462_);
v___x_6467_ = v_reuseFailAlloc_6468_;
goto v_reusejp_6466_;
}
v_reusejp_6466_:
{
return v___x_6467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6470_, lean_object* v_a_6471_, lean_object* v_a_6472_, lean_object* v_a_6473_, lean_object* v_a_6474_, lean_object* v_a_6475_){
_start:
{
lean_object* v_res_6476_; 
v_res_6476_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6470_, v_a_6471_, v_a_6472_, v_a_6473_, v_a_6474_);
lean_dec(v_a_6474_);
lean_dec_ref(v_a_6473_);
lean_dec(v_a_6472_);
lean_dec_ref(v_a_6471_);
return v_res_6476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6477_, lean_object* v_maxFVars_x3f_6478_, lean_object* v_k_6479_, uint8_t v_cleanupAnnotations_6480_, uint8_t v_whnfType_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_){
_start:
{
lean_object* v___f_6489_; lean_object* v___x_6490_; 
lean_inc(v___y_6483_);
lean_inc_ref(v___y_6482_);
v___f_6489_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6489_, 0, v_k_6479_);
lean_closure_set(v___f_6489_, 1, v___y_6482_);
lean_closure_set(v___f_6489_, 2, v___y_6483_);
v___x_6490_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6477_, v_maxFVars_x3f_6478_, v___f_6489_, v_cleanupAnnotations_6480_, v_whnfType_6481_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_);
if (lean_obj_tag(v___x_6490_) == 0)
{
return v___x_6490_;
}
else
{
lean_object* v_a_6491_; lean_object* v___x_6493_; uint8_t v_isShared_6494_; uint8_t v_isSharedCheck_6498_; 
v_a_6491_ = lean_ctor_get(v___x_6490_, 0);
v_isSharedCheck_6498_ = !lean_is_exclusive(v___x_6490_);
if (v_isSharedCheck_6498_ == 0)
{
v___x_6493_ = v___x_6490_;
v_isShared_6494_ = v_isSharedCheck_6498_;
goto v_resetjp_6492_;
}
else
{
lean_inc(v_a_6491_);
lean_dec(v___x_6490_);
v___x_6493_ = lean_box(0);
v_isShared_6494_ = v_isSharedCheck_6498_;
goto v_resetjp_6492_;
}
v_resetjp_6492_:
{
lean_object* v___x_6496_; 
if (v_isShared_6494_ == 0)
{
v___x_6496_ = v___x_6493_;
goto v_reusejp_6495_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_a_6491_);
v___x_6496_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6495_;
}
v_reusejp_6495_:
{
return v___x_6496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6499_, lean_object* v_maxFVars_x3f_6500_, lean_object* v_k_6501_, lean_object* v_cleanupAnnotations_6502_, lean_object* v_whnfType_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6511_; uint8_t v_whnfType_boxed_6512_; lean_object* v_res_6513_; 
v_cleanupAnnotations_boxed_6511_ = lean_unbox(v_cleanupAnnotations_6502_);
v_whnfType_boxed_6512_ = lean_unbox(v_whnfType_6503_);
v_res_6513_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6499_, v_maxFVars_x3f_6500_, v_k_6501_, v_cleanupAnnotations_boxed_6511_, v_whnfType_boxed_6512_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_, v___y_6508_, v___y_6509_);
lean_dec(v___y_6509_);
lean_dec_ref(v___y_6508_);
lean_dec(v___y_6507_);
lean_dec_ref(v___y_6506_);
lean_dec(v___y_6505_);
lean_dec_ref(v___y_6504_);
return v_res_6513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6514_, lean_object* v_type_6515_, lean_object* v_maxFVars_x3f_6516_, lean_object* v_k_6517_, uint8_t v_cleanupAnnotations_6518_, uint8_t v_whnfType_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_){
_start:
{
lean_object* v___x_6527_; 
v___x_6527_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6515_, v_maxFVars_x3f_6516_, v_k_6517_, v_cleanupAnnotations_6518_, v_whnfType_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_);
return v___x_6527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6528_, lean_object* v_type_6529_, lean_object* v_maxFVars_x3f_6530_, lean_object* v_k_6531_, lean_object* v_cleanupAnnotations_6532_, lean_object* v_whnfType_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6541_; uint8_t v_whnfType_boxed_6542_; lean_object* v_res_6543_; 
v_cleanupAnnotations_boxed_6541_ = lean_unbox(v_cleanupAnnotations_6532_);
v_whnfType_boxed_6542_ = lean_unbox(v_whnfType_6533_);
v_res_6543_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6528_, v_type_6529_, v_maxFVars_x3f_6530_, v_k_6531_, v_cleanupAnnotations_boxed_6541_, v_whnfType_boxed_6542_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
lean_dec(v___y_6537_);
lean_dec_ref(v___y_6536_);
lean_dec(v___y_6535_);
lean_dec_ref(v___y_6534_);
return v_res_6543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6544_, lean_object* v_x_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_){
_start:
{
lean_object* v_keyedConfig_6553_; uint8_t v_trackZetaDelta_6554_; lean_object* v_zetaDeltaSet_6555_; lean_object* v_localInstances_6556_; lean_object* v_defEqCtx_x3f_6557_; lean_object* v_synthPendingDepth_6558_; lean_object* v_canUnfold_x3f_6559_; uint8_t v_univApprox_6560_; uint8_t v_inTypeClassResolution_6561_; uint8_t v_cacheInferType_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
v_keyedConfig_6553_ = lean_ctor_get(v___y_6548_, 0);
v_trackZetaDelta_6554_ = lean_ctor_get_uint8(v___y_6548_, sizeof(void*)*7);
v_zetaDeltaSet_6555_ = lean_ctor_get(v___y_6548_, 1);
v_localInstances_6556_ = lean_ctor_get(v___y_6548_, 3);
v_defEqCtx_x3f_6557_ = lean_ctor_get(v___y_6548_, 4);
v_synthPendingDepth_6558_ = lean_ctor_get(v___y_6548_, 5);
v_canUnfold_x3f_6559_ = lean_ctor_get(v___y_6548_, 6);
v_univApprox_6560_ = lean_ctor_get_uint8(v___y_6548_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6561_ = lean_ctor_get_uint8(v___y_6548_, sizeof(void*)*7 + 2);
v_cacheInferType_6562_ = lean_ctor_get_uint8(v___y_6548_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_6559_);
lean_inc(v_synthPendingDepth_6558_);
lean_inc(v_defEqCtx_x3f_6557_);
lean_inc_ref(v_localInstances_6556_);
lean_inc(v_zetaDeltaSet_6555_);
lean_inc_ref(v_keyedConfig_6553_);
v___x_6563_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6563_, 0, v_keyedConfig_6553_);
lean_ctor_set(v___x_6563_, 1, v_zetaDeltaSet_6555_);
lean_ctor_set(v___x_6563_, 2, v_lctx_6544_);
lean_ctor_set(v___x_6563_, 3, v_localInstances_6556_);
lean_ctor_set(v___x_6563_, 4, v_defEqCtx_x3f_6557_);
lean_ctor_set(v___x_6563_, 5, v_synthPendingDepth_6558_);
lean_ctor_set(v___x_6563_, 6, v_canUnfold_x3f_6559_);
lean_ctor_set_uint8(v___x_6563_, sizeof(void*)*7, v_trackZetaDelta_6554_);
lean_ctor_set_uint8(v___x_6563_, sizeof(void*)*7 + 1, v_univApprox_6560_);
lean_ctor_set_uint8(v___x_6563_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6561_);
lean_ctor_set_uint8(v___x_6563_, sizeof(void*)*7 + 3, v_cacheInferType_6562_);
lean_inc(v___y_6551_);
lean_inc_ref(v___y_6550_);
lean_inc(v___y_6549_);
lean_inc(v___y_6547_);
lean_inc_ref(v___y_6546_);
v___x_6564_ = lean_apply_7(v_x_6545_, v___y_6546_, v___y_6547_, v___x_6563_, v___y_6549_, v___y_6550_, v___y_6551_, lean_box(0));
if (lean_obj_tag(v___x_6564_) == 0)
{
lean_object* v_a_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6572_; 
v_a_6565_ = lean_ctor_get(v___x_6564_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6564_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6567_ = v___x_6564_;
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_a_6565_);
lean_dec(v___x_6564_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
lean_object* v___x_6570_; 
if (v_isShared_6568_ == 0)
{
v___x_6570_ = v___x_6567_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_a_6565_);
v___x_6570_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
return v___x_6570_;
}
}
}
else
{
return v___x_6564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6573_, lean_object* v_x_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_){
_start:
{
lean_object* v_res_6582_; 
v_res_6582_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6573_, v_x_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_);
lean_dec(v___y_6580_);
lean_dec_ref(v___y_6579_);
lean_dec(v___y_6578_);
lean_dec_ref(v___y_6577_);
lean_dec(v___y_6576_);
lean_dec_ref(v___y_6575_);
return v_res_6582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6583_, lean_object* v_lctx_6584_, lean_object* v_x_6585_, lean_object* v___y_6586_, lean_object* v___y_6587_, lean_object* v___y_6588_, lean_object* v___y_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_){
_start:
{
lean_object* v___x_6593_; 
v___x_6593_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6584_, v_x_6585_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_);
return v___x_6593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6594_, lean_object* v_lctx_6595_, lean_object* v_x_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6594_, v_lctx_6595_, v_x_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_);
lean_dec(v___y_6602_);
lean_dec_ref(v___y_6601_);
lean_dec(v___y_6600_);
lean_dec_ref(v___y_6599_);
lean_dec(v___y_6598_);
lean_dec_ref(v___y_6597_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6621_, lean_object* v___x_6622_, lean_object* v_wfRel_6623_, lean_object* v_x_6624_, lean_object* v_type_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; 
v___x_6633_ = lean_unsigned_to_nat(0u);
v___x_6634_ = lean_array_get_borrowed(v___x_6621_, v_x_6624_, v___x_6633_);
v___x_6635_ = l_Lean_Expr_fvarId_x21(v___x_6634_);
v___x_6636_ = l_Lean_FVarId_getUserName___redArg(v___x_6635_, v___y_6628_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6636_) == 0)
{
lean_object* v_a_6637_; lean_object* v___x_6638_; 
v_a_6637_ = lean_ctor_get(v___x_6636_, 0);
lean_inc(v_a_6637_);
lean_dec_ref(v___x_6636_);
lean_inc(v___y_6631_);
lean_inc_ref(v___y_6630_);
lean_inc(v___y_6629_);
lean_inc_ref(v___y_6628_);
lean_inc(v___x_6634_);
v___x_6638_ = lean_infer_type(v___x_6634_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6638_) == 0)
{
lean_object* v_a_6639_; lean_object* v___x_6640_; 
v_a_6639_ = lean_ctor_get(v___x_6638_, 0);
lean_inc_n(v_a_6639_, 2);
lean_dec_ref(v___x_6638_);
v___x_6640_ = l_Lean_Meta_getLevel(v_a_6639_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6640_) == 0)
{
lean_object* v_a_6641_; lean_object* v___x_6642_; 
v_a_6641_ = lean_ctor_get(v___x_6640_, 0);
lean_inc(v_a_6641_);
lean_dec_ref(v___x_6640_);
lean_inc_ref(v_type_6625_);
v___x_6642_ = l_Lean_Meta_getLevel(v_type_6625_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; uint8_t v___x_6646_; uint8_t v___x_6647_; uint8_t v___x_6648_; lean_object* v___x_6649_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
lean_inc(v_a_6643_);
lean_dec_ref(v___x_6642_);
v___x_6644_ = lean_mk_empty_array_with_capacity(v___x_6622_);
lean_inc(v___x_6634_);
lean_inc_ref(v___x_6644_);
v___x_6645_ = lean_array_push(v___x_6644_, v___x_6634_);
v___x_6646_ = 0;
v___x_6647_ = 1;
v___x_6648_ = 1;
v___x_6649_ = l_Lean_Meta_mkLambdaFVars(v___x_6645_, v_type_6625_, v___x_6646_, v___x_6647_, v___x_6646_, v___x_6647_, v___x_6648_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
lean_dec_ref(v___x_6645_);
if (lean_obj_tag(v___x_6649_) == 0)
{
lean_object* v_a_6650_; lean_object* v___x_6651_; 
v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
lean_inc(v_a_6650_);
lean_dec_ref(v___x_6649_);
lean_inc_ref(v_wfRel_6623_);
v___x_6651_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6623_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6651_) == 0)
{
lean_object* v_a_6652_; lean_object* v___x_6654_; uint8_t v_isShared_6655_; uint8_t v_isSharedCheck_6696_; 
v_a_6652_ = lean_ctor_get(v___x_6651_, 0);
v_isSharedCheck_6696_ = !lean_is_exclusive(v___x_6651_);
if (v_isSharedCheck_6696_ == 0)
{
v___x_6654_ = v___x_6651_;
v_isShared_6655_ = v_isSharedCheck_6696_;
goto v_resetjp_6653_;
}
else
{
lean_inc(v_a_6652_);
lean_dec(v___x_6651_);
v___x_6654_ = lean_box(0);
v_isShared_6655_ = v_isSharedCheck_6696_;
goto v_resetjp_6653_;
}
v_resetjp_6653_:
{
if (lean_obj_tag(v_a_6652_) == 1)
{
lean_object* v_val_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6665_; 
lean_dec_ref(v___x_6644_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_val_6656_ = lean_ctor_get(v_a_6652_, 0);
lean_inc(v_val_6656_);
lean_dec_ref(v_a_6652_);
v___x_6657_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6658_ = lean_box(0);
v___x_6659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6659_, 0, v_a_6643_);
lean_ctor_set(v___x_6659_, 1, v___x_6658_);
v___x_6660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6660_, 0, v_a_6641_);
lean_ctor_set(v___x_6660_, 1, v___x_6659_);
v___x_6661_ = l_Lean_mkConst(v___x_6657_, v___x_6660_);
v___x_6662_ = l_Lean_mkApp3(v___x_6661_, v_a_6639_, v_a_6650_, v_val_6656_);
v___x_6663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6663_, 0, v___x_6662_);
lean_ctor_set(v___x_6663_, 1, v_a_6637_);
if (v_isShared_6655_ == 0)
{
lean_ctor_set(v___x_6654_, 0, v___x_6663_);
v___x_6665_ = v___x_6654_;
goto v_reusejp_6664_;
}
else
{
lean_object* v_reuseFailAlloc_6666_; 
v_reuseFailAlloc_6666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6666_, 0, v___x_6663_);
v___x_6665_ = v_reuseFailAlloc_6666_;
goto v_reusejp_6664_;
}
v_reusejp_6664_:
{
return v___x_6665_;
}
}
else
{
lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; 
lean_del_object(v___x_6654_);
lean_dec(v_a_6652_);
v___x_6667_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6623_);
v___x_6668_ = l_Lean_mkProj(v___x_6667_, v___x_6633_, v_wfRel_6623_);
v___x_6669_ = l_Lean_mkProj(v___x_6667_, v___x_6622_, v_wfRel_6623_);
v___x_6670_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6671_ = lean_array_push(v___x_6644_, v___x_6669_);
v___x_6672_ = l_Lean_Meta_mkAppM(v___x_6670_, v___x_6671_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
if (lean_obj_tag(v___x_6672_) == 0)
{
lean_object* v_a_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6687_; 
v_a_6673_ = lean_ctor_get(v___x_6672_, 0);
v_isSharedCheck_6687_ = !lean_is_exclusive(v___x_6672_);
if (v_isSharedCheck_6687_ == 0)
{
v___x_6675_ = v___x_6672_;
v_isShared_6676_ = v_isSharedCheck_6687_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_a_6673_);
lean_dec(v___x_6672_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6687_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6685_; 
v___x_6677_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6678_ = lean_box(0);
v___x_6679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6679_, 0, v_a_6643_);
lean_ctor_set(v___x_6679_, 1, v___x_6678_);
v___x_6680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6680_, 0, v_a_6641_);
lean_ctor_set(v___x_6680_, 1, v___x_6679_);
v___x_6681_ = l_Lean_mkConst(v___x_6677_, v___x_6680_);
v___x_6682_ = l_Lean_mkApp4(v___x_6681_, v_a_6639_, v_a_6650_, v___x_6668_, v_a_6673_);
v___x_6683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6683_, 0, v___x_6682_);
lean_ctor_set(v___x_6683_, 1, v_a_6637_);
if (v_isShared_6676_ == 0)
{
lean_ctor_set(v___x_6675_, 0, v___x_6683_);
v___x_6685_ = v___x_6675_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v___x_6683_);
v___x_6685_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
return v___x_6685_;
}
}
}
else
{
lean_object* v_a_6688_; lean_object* v___x_6690_; uint8_t v_isShared_6691_; uint8_t v_isSharedCheck_6695_; 
lean_dec_ref(v___x_6668_);
lean_dec(v_a_6650_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec(v_a_6639_);
lean_dec(v_a_6637_);
v_a_6688_ = lean_ctor_get(v___x_6672_, 0);
v_isSharedCheck_6695_ = !lean_is_exclusive(v___x_6672_);
if (v_isSharedCheck_6695_ == 0)
{
v___x_6690_ = v___x_6672_;
v_isShared_6691_ = v_isSharedCheck_6695_;
goto v_resetjp_6689_;
}
else
{
lean_inc(v_a_6688_);
lean_dec(v___x_6672_);
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
}
}
else
{
lean_object* v_a_6697_; lean_object* v___x_6699_; uint8_t v_isShared_6700_; uint8_t v_isSharedCheck_6704_; 
lean_dec(v_a_6650_);
lean_dec_ref(v___x_6644_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec(v_a_6639_);
lean_dec(v_a_6637_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6697_ = lean_ctor_get(v___x_6651_, 0);
v_isSharedCheck_6704_ = !lean_is_exclusive(v___x_6651_);
if (v_isSharedCheck_6704_ == 0)
{
v___x_6699_ = v___x_6651_;
v_isShared_6700_ = v_isSharedCheck_6704_;
goto v_resetjp_6698_;
}
else
{
lean_inc(v_a_6697_);
lean_dec(v___x_6651_);
v___x_6699_ = lean_box(0);
v_isShared_6700_ = v_isSharedCheck_6704_;
goto v_resetjp_6698_;
}
v_resetjp_6698_:
{
lean_object* v___x_6702_; 
if (v_isShared_6700_ == 0)
{
v___x_6702_ = v___x_6699_;
goto v_reusejp_6701_;
}
else
{
lean_object* v_reuseFailAlloc_6703_; 
v_reuseFailAlloc_6703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6703_, 0, v_a_6697_);
v___x_6702_ = v_reuseFailAlloc_6703_;
goto v_reusejp_6701_;
}
v_reusejp_6701_:
{
return v___x_6702_;
}
}
}
}
else
{
lean_object* v_a_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6712_; 
lean_dec_ref(v___x_6644_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec(v_a_6639_);
lean_dec(v_a_6637_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6705_ = lean_ctor_get(v___x_6649_, 0);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6649_);
if (v_isSharedCheck_6712_ == 0)
{
v___x_6707_ = v___x_6649_;
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_a_6705_);
lean_dec(v___x_6649_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v___x_6710_; 
if (v_isShared_6708_ == 0)
{
v___x_6710_ = v___x_6707_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_a_6705_);
v___x_6710_ = v_reuseFailAlloc_6711_;
goto v_reusejp_6709_;
}
v_reusejp_6709_:
{
return v___x_6710_;
}
}
}
}
else
{
lean_object* v_a_6713_; lean_object* v___x_6715_; uint8_t v_isShared_6716_; uint8_t v_isSharedCheck_6720_; 
lean_dec(v_a_6641_);
lean_dec(v_a_6639_);
lean_dec(v_a_6637_);
lean_dec_ref(v_type_6625_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6713_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6720_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6715_ = v___x_6642_;
v_isShared_6716_ = v_isSharedCheck_6720_;
goto v_resetjp_6714_;
}
else
{
lean_inc(v_a_6713_);
lean_dec(v___x_6642_);
v___x_6715_ = lean_box(0);
v_isShared_6716_ = v_isSharedCheck_6720_;
goto v_resetjp_6714_;
}
v_resetjp_6714_:
{
lean_object* v___x_6718_; 
if (v_isShared_6716_ == 0)
{
v___x_6718_ = v___x_6715_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6719_; 
v_reuseFailAlloc_6719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_a_6713_);
v___x_6718_ = v_reuseFailAlloc_6719_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
return v___x_6718_;
}
}
}
}
else
{
lean_object* v_a_6721_; lean_object* v___x_6723_; uint8_t v_isShared_6724_; uint8_t v_isSharedCheck_6728_; 
lean_dec(v_a_6639_);
lean_dec(v_a_6637_);
lean_dec_ref(v_type_6625_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6721_ = lean_ctor_get(v___x_6640_, 0);
v_isSharedCheck_6728_ = !lean_is_exclusive(v___x_6640_);
if (v_isSharedCheck_6728_ == 0)
{
v___x_6723_ = v___x_6640_;
v_isShared_6724_ = v_isSharedCheck_6728_;
goto v_resetjp_6722_;
}
else
{
lean_inc(v_a_6721_);
lean_dec(v___x_6640_);
v___x_6723_ = lean_box(0);
v_isShared_6724_ = v_isSharedCheck_6728_;
goto v_resetjp_6722_;
}
v_resetjp_6722_:
{
lean_object* v___x_6726_; 
if (v_isShared_6724_ == 0)
{
v___x_6726_ = v___x_6723_;
goto v_reusejp_6725_;
}
else
{
lean_object* v_reuseFailAlloc_6727_; 
v_reuseFailAlloc_6727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6727_, 0, v_a_6721_);
v___x_6726_ = v_reuseFailAlloc_6727_;
goto v_reusejp_6725_;
}
v_reusejp_6725_:
{
return v___x_6726_;
}
}
}
}
else
{
lean_object* v_a_6729_; lean_object* v___x_6731_; uint8_t v_isShared_6732_; uint8_t v_isSharedCheck_6736_; 
lean_dec(v_a_6637_);
lean_dec_ref(v_type_6625_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6729_ = lean_ctor_get(v___x_6638_, 0);
v_isSharedCheck_6736_ = !lean_is_exclusive(v___x_6638_);
if (v_isSharedCheck_6736_ == 0)
{
v___x_6731_ = v___x_6638_;
v_isShared_6732_ = v_isSharedCheck_6736_;
goto v_resetjp_6730_;
}
else
{
lean_inc(v_a_6729_);
lean_dec(v___x_6638_);
v___x_6731_ = lean_box(0);
v_isShared_6732_ = v_isSharedCheck_6736_;
goto v_resetjp_6730_;
}
v_resetjp_6730_:
{
lean_object* v___x_6734_; 
if (v_isShared_6732_ == 0)
{
v___x_6734_ = v___x_6731_;
goto v_reusejp_6733_;
}
else
{
lean_object* v_reuseFailAlloc_6735_; 
v_reuseFailAlloc_6735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_a_6729_);
v___x_6734_ = v_reuseFailAlloc_6735_;
goto v_reusejp_6733_;
}
v_reusejp_6733_:
{
return v___x_6734_;
}
}
}
}
else
{
lean_object* v_a_6737_; lean_object* v___x_6739_; uint8_t v_isShared_6740_; uint8_t v_isSharedCheck_6744_; 
lean_dec_ref(v_type_6625_);
lean_dec_ref(v_wfRel_6623_);
lean_dec(v___x_6622_);
v_a_6737_ = lean_ctor_get(v___x_6636_, 0);
v_isSharedCheck_6744_ = !lean_is_exclusive(v___x_6636_);
if (v_isSharedCheck_6744_ == 0)
{
v___x_6739_ = v___x_6636_;
v_isShared_6740_ = v_isSharedCheck_6744_;
goto v_resetjp_6738_;
}
else
{
lean_inc(v_a_6737_);
lean_dec(v___x_6636_);
v___x_6739_ = lean_box(0);
v_isShared_6740_ = v_isSharedCheck_6744_;
goto v_resetjp_6738_;
}
v_resetjp_6738_:
{
lean_object* v___x_6742_; 
if (v_isShared_6740_ == 0)
{
v___x_6742_ = v___x_6739_;
goto v_reusejp_6741_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v_a_6737_);
v___x_6742_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6741_;
}
v_reusejp_6741_:
{
return v___x_6742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6745_, lean_object* v___x_6746_, lean_object* v_wfRel_6747_, lean_object* v_x_6748_, lean_object* v_type_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_){
_start:
{
lean_object* v_res_6757_; 
v_res_6757_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6745_, v___x_6746_, v_wfRel_6747_, v_x_6748_, v_type_6749_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_);
lean_dec(v___y_6755_);
lean_dec_ref(v___y_6754_);
lean_dec(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec(v___y_6751_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v_x_6748_);
lean_dec_ref(v___x_6745_);
return v_res_6757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6758_, lean_object* v_declName_6759_, lean_object* v_x_6760_, lean_object* v_F_6761_, lean_object* v_val_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_){
_start:
{
lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6770_ = lean_array_get_size(v_prefixArgs_6758_);
v___x_6771_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6771_, 0, v_declName_6759_);
lean_closure_set(v___x_6771_, 1, v___x_6770_);
v___x_6772_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6760_, v_F_6761_, v_val_6762_, v___x_6771_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
return v___x_6772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6773_, lean_object* v_declName_6774_, lean_object* v_x_6775_, lean_object* v_F_6776_, lean_object* v_val_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_){
_start:
{
lean_object* v_res_6785_; 
v_res_6785_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6773_, v_declName_6774_, v_x_6775_, v_F_6776_, v_val_6777_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_);
lean_dec(v___y_6783_);
lean_dec_ref(v___y_6782_);
lean_dec(v___y_6781_);
lean_dec_ref(v___y_6780_);
lean_dec(v___y_6779_);
lean_dec_ref(v___y_6778_);
lean_dec_ref(v_prefixArgs_6773_);
return v_res_6785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6786_, lean_object* v___x_6787_, lean_object* v___x_6788_, lean_object* v___f_6789_, lean_object* v_funNames_6790_, lean_object* v_argsPacker_6791_, lean_object* v_decrTactics_6792_, uint8_t v___x_6793_, lean_object* v_fst_6794_, lean_object* v_prefixArgs_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_){
_start:
{
lean_object* v___x_6803_; 
lean_inc_ref(v___x_6787_);
lean_inc_ref(v___x_6786_);
v___x_6803_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6786_, v___x_6787_, v___x_6788_, v___f_6789_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
if (lean_obj_tag(v___x_6803_) == 0)
{
lean_object* v_a_6804_; lean_object* v___x_6805_; 
v_a_6804_ = lean_ctor_get(v___x_6803_, 0);
lean_inc(v_a_6804_);
lean_dec_ref(v___x_6803_);
v___x_6805_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6790_, v_argsPacker_6791_, v_decrTactics_6792_, v_a_6804_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
if (lean_obj_tag(v___x_6805_) == 0)
{
lean_object* v_a_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; uint8_t v___x_6811_; uint8_t v___x_6812_; lean_object* v___x_6813_; 
v_a_6806_ = lean_ctor_get(v___x_6805_, 0);
lean_inc(v_a_6806_);
lean_dec_ref(v___x_6805_);
v___x_6807_ = lean_unsigned_to_nat(2u);
v___x_6808_ = lean_mk_empty_array_with_capacity(v___x_6807_);
v___x_6809_ = lean_array_push(v___x_6808_, v___x_6786_);
v___x_6810_ = lean_array_push(v___x_6809_, v___x_6787_);
v___x_6811_ = 1;
v___x_6812_ = 1;
v___x_6813_ = l_Lean_Meta_mkLambdaFVars(v___x_6810_, v_a_6806_, v___x_6793_, v___x_6811_, v___x_6793_, v___x_6811_, v___x_6812_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
lean_dec_ref(v___x_6810_);
if (lean_obj_tag(v___x_6813_) == 0)
{
lean_object* v_a_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; 
v_a_6814_ = lean_ctor_get(v___x_6813_, 0);
lean_inc(v_a_6814_);
lean_dec_ref(v___x_6813_);
v___x_6815_ = l_Lean_Expr_app___override(v_fst_6794_, v_a_6814_);
v___x_6816_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6795_, v___x_6815_, v___x_6793_, v___x_6811_, v___x_6793_, v___x_6811_, v___x_6812_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
return v___x_6816_;
}
else
{
lean_dec_ref(v_fst_6794_);
return v___x_6813_;
}
}
else
{
lean_dec_ref(v_fst_6794_);
lean_dec_ref(v___x_6787_);
lean_dec_ref(v___x_6786_);
return v___x_6805_;
}
}
else
{
lean_dec_ref(v_fst_6794_);
lean_dec_ref(v_decrTactics_6792_);
lean_dec_ref(v_argsPacker_6791_);
lean_dec_ref(v_funNames_6790_);
lean_dec_ref(v___x_6787_);
lean_dec_ref(v___x_6786_);
return v___x_6803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6817_ = _args[0];
lean_object* v___x_6818_ = _args[1];
lean_object* v___x_6819_ = _args[2];
lean_object* v___f_6820_ = _args[3];
lean_object* v_funNames_6821_ = _args[4];
lean_object* v_argsPacker_6822_ = _args[5];
lean_object* v_decrTactics_6823_ = _args[6];
lean_object* v___x_6824_ = _args[7];
lean_object* v_fst_6825_ = _args[8];
lean_object* v_prefixArgs_6826_ = _args[9];
lean_object* v___y_6827_ = _args[10];
lean_object* v___y_6828_ = _args[11];
lean_object* v___y_6829_ = _args[12];
lean_object* v___y_6830_ = _args[13];
lean_object* v___y_6831_ = _args[14];
lean_object* v___y_6832_ = _args[15];
lean_object* v___y_6833_ = _args[16];
_start:
{
uint8_t v___x_5940__boxed_6834_; lean_object* v_res_6835_; 
v___x_5940__boxed_6834_ = lean_unbox(v___x_6824_);
v_res_6835_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6817_, v___x_6818_, v___x_6819_, v___f_6820_, v_funNames_6821_, v_argsPacker_6822_, v_decrTactics_6823_, v___x_5940__boxed_6834_, v_fst_6825_, v_prefixArgs_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec_ref(v_prefixArgs_6826_);
return v_res_6835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6836_, lean_object* v_snd_6837_, lean_object* v___x_6838_, lean_object* v_prefixArgs_6839_, lean_object* v_value_6840_, lean_object* v___f_6841_, lean_object* v_funNames_6842_, lean_object* v_argsPacker_6843_, lean_object* v_decrTactics_6844_, uint8_t v___x_6845_, lean_object* v_fst_6846_, lean_object* v_xs_6847_, lean_object* v_x_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_){
_start:
{
lean_object* v_lctx_6856_; lean_object* v___x_6857_; lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v___f_6865_; lean_object* v___x_6866_; 
v_lctx_6856_ = lean_ctor_get(v___y_6851_, 2);
v___x_6857_ = lean_unsigned_to_nat(0u);
v___x_6858_ = lean_array_get_borrowed(v___x_6836_, v_xs_6847_, v___x_6857_);
v___x_6859_ = l_Lean_Expr_fvarId_x21(v___x_6858_);
lean_inc_ref(v_lctx_6856_);
v___x_6860_ = l_Lean_LocalContext_setUserName(v_lctx_6856_, v___x_6859_, v_snd_6837_);
v___x_6861_ = lean_array_get_borrowed(v___x_6836_, v_xs_6847_, v___x_6838_);
lean_inc_n(v___x_6858_, 2);
lean_inc_ref(v_prefixArgs_6839_);
v___x_6862_ = lean_array_push(v_prefixArgs_6839_, v___x_6858_);
v___x_6863_ = l_Lean_Expr_beta(v_value_6840_, v___x_6862_);
v___x_6864_ = lean_box(v___x_6845_);
lean_inc(v___x_6861_);
v___f_6865_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6865_, 0, v___x_6858_);
lean_closure_set(v___f_6865_, 1, v___x_6861_);
lean_closure_set(v___f_6865_, 2, v___x_6863_);
lean_closure_set(v___f_6865_, 3, v___f_6841_);
lean_closure_set(v___f_6865_, 4, v_funNames_6842_);
lean_closure_set(v___f_6865_, 5, v_argsPacker_6843_);
lean_closure_set(v___f_6865_, 6, v_decrTactics_6844_);
lean_closure_set(v___f_6865_, 7, v___x_6864_);
lean_closure_set(v___f_6865_, 8, v_fst_6846_);
lean_closure_set(v___f_6865_, 9, v_prefixArgs_6839_);
v___x_6866_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6860_, v___f_6865_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_);
return v___x_6866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6867_ = _args[0];
lean_object* v_snd_6868_ = _args[1];
lean_object* v___x_6869_ = _args[2];
lean_object* v_prefixArgs_6870_ = _args[3];
lean_object* v_value_6871_ = _args[4];
lean_object* v___f_6872_ = _args[5];
lean_object* v_funNames_6873_ = _args[6];
lean_object* v_argsPacker_6874_ = _args[7];
lean_object* v_decrTactics_6875_ = _args[8];
lean_object* v___x_6876_ = _args[9];
lean_object* v_fst_6877_ = _args[10];
lean_object* v_xs_6878_ = _args[11];
lean_object* v_x_6879_ = _args[12];
lean_object* v___y_6880_ = _args[13];
lean_object* v___y_6881_ = _args[14];
lean_object* v___y_6882_ = _args[15];
lean_object* v___y_6883_ = _args[16];
lean_object* v___y_6884_ = _args[17];
lean_object* v___y_6885_ = _args[18];
lean_object* v___y_6886_ = _args[19];
_start:
{
uint8_t v___x_6010__boxed_6887_; lean_object* v_res_6888_; 
v___x_6010__boxed_6887_ = lean_unbox(v___x_6876_);
v_res_6888_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6867_, v_snd_6868_, v___x_6869_, v_prefixArgs_6870_, v_value_6871_, v___f_6872_, v_funNames_6873_, v_argsPacker_6874_, v_decrTactics_6875_, v___x_6010__boxed_6887_, v_fst_6877_, v_xs_6878_, v_x_6879_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
lean_dec(v___y_6885_);
lean_dec_ref(v___y_6884_);
lean_dec(v___y_6883_);
lean_dec_ref(v___y_6882_);
lean_dec(v___y_6881_);
lean_dec_ref(v___y_6880_);
lean_dec_ref(v_x_6879_);
lean_dec_ref(v_xs_6878_);
lean_dec(v___x_6869_);
lean_dec_ref(v___x_6867_);
return v_res_6888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6893_, lean_object* v_prefixArgs_6894_, lean_object* v_argsPacker_6895_, lean_object* v_wfRel_6896_, lean_object* v_funNames_6897_, lean_object* v_decrTactics_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_){
_start:
{
lean_object* v_declName_6906_; lean_object* v_type_6907_; lean_object* v_value_6908_; lean_object* v___x_6909_; 
v_declName_6906_ = lean_ctor_get(v_preDef_6893_, 3);
lean_inc(v_declName_6906_);
v_type_6907_ = lean_ctor_get(v_preDef_6893_, 6);
lean_inc_ref(v_type_6907_);
v_value_6908_ = lean_ctor_get(v_preDef_6893_, 7);
lean_inc_ref(v_value_6908_);
lean_dec_ref(v_preDef_6893_);
v___x_6909_ = l_Lean_Meta_instantiateForall(v_type_6907_, v_prefixArgs_6894_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
if (lean_obj_tag(v___x_6909_) == 0)
{
lean_object* v_a_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___f_6913_; lean_object* v___x_6914_; uint8_t v___x_6915_; lean_object* v___x_6916_; 
v_a_6910_ = lean_ctor_get(v___x_6909_, 0);
lean_inc(v_a_6910_);
lean_dec_ref(v___x_6909_);
v___x_6911_ = l_Lean_instInhabitedExpr;
v___x_6912_ = lean_unsigned_to_nat(1u);
v___f_6913_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6913_, 0, v___x_6911_);
lean_closure_set(v___f_6913_, 1, v___x_6912_);
lean_closure_set(v___f_6913_, 2, v_wfRel_6896_);
v___x_6914_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6915_ = 0;
v___x_6916_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6910_, v___x_6914_, v___f_6913_, v___x_6915_, v___x_6915_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
if (lean_obj_tag(v___x_6916_) == 0)
{
lean_object* v_a_6917_; lean_object* v_fst_6918_; lean_object* v_snd_6919_; lean_object* v___x_6920_; 
v_a_6917_ = lean_ctor_get(v___x_6916_, 0);
lean_inc(v_a_6917_);
lean_dec_ref(v___x_6916_);
v_fst_6918_ = lean_ctor_get(v_a_6917_, 0);
lean_inc_n(v_fst_6918_, 2);
v_snd_6919_ = lean_ctor_get(v_a_6917_, 1);
lean_inc(v_snd_6919_);
lean_dec(v_a_6917_);
lean_inc(v_a_6904_);
lean_inc_ref(v_a_6903_);
lean_inc(v_a_6902_);
lean_inc_ref(v_a_6901_);
v___x_6920_ = lean_infer_type(v_fst_6918_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v_a_6921_; lean_object* v___x_6922_; 
v_a_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_a_6921_);
lean_dec_ref(v___x_6920_);
lean_inc(v_a_6904_);
lean_inc_ref(v_a_6903_);
lean_inc(v_a_6902_);
lean_inc_ref(v_a_6901_);
v___x_6922_ = lean_whnf(v_a_6921_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
if (lean_obj_tag(v___x_6922_) == 0)
{
lean_object* v_a_6923_; lean_object* v___f_6924_; lean_object* v___x_6925_; lean_object* v___f_6926_; lean_object* v___x_6927_; lean_object* v___x_6928_; lean_object* v___x_6929_; 
v_a_6923_ = lean_ctor_get(v___x_6922_, 0);
lean_inc(v_a_6923_);
lean_dec_ref(v___x_6922_);
lean_inc_ref(v_prefixArgs_6894_);
v___f_6924_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6924_, 0, v_prefixArgs_6894_);
lean_closure_set(v___f_6924_, 1, v_declName_6906_);
v___x_6925_ = lean_box(v___x_6915_);
v___f_6926_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6926_, 0, v___x_6911_);
lean_closure_set(v___f_6926_, 1, v_snd_6919_);
lean_closure_set(v___f_6926_, 2, v___x_6912_);
lean_closure_set(v___f_6926_, 3, v_prefixArgs_6894_);
lean_closure_set(v___f_6926_, 4, v_value_6908_);
lean_closure_set(v___f_6926_, 5, v___f_6924_);
lean_closure_set(v___f_6926_, 6, v_funNames_6897_);
lean_closure_set(v___f_6926_, 7, v_argsPacker_6895_);
lean_closure_set(v___f_6926_, 8, v_decrTactics_6898_);
lean_closure_set(v___f_6926_, 9, v___x_6925_);
lean_closure_set(v___f_6926_, 10, v_fst_6918_);
v___x_6927_ = l_Lean_Expr_bindingDomain_x21(v_a_6923_);
lean_dec(v_a_6923_);
v___x_6928_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6929_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6927_, v___x_6928_, v___f_6926_, v___x_6915_, v___x_6915_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
return v___x_6929_;
}
else
{
lean_dec(v_snd_6919_);
lean_dec(v_fst_6918_);
lean_dec_ref(v_value_6908_);
lean_dec(v_declName_6906_);
lean_dec_ref(v_decrTactics_6898_);
lean_dec_ref(v_funNames_6897_);
lean_dec_ref(v_argsPacker_6895_);
lean_dec_ref(v_prefixArgs_6894_);
return v___x_6922_;
}
}
else
{
lean_dec(v_snd_6919_);
lean_dec(v_fst_6918_);
lean_dec_ref(v_value_6908_);
lean_dec(v_declName_6906_);
lean_dec_ref(v_decrTactics_6898_);
lean_dec_ref(v_funNames_6897_);
lean_dec_ref(v_argsPacker_6895_);
lean_dec_ref(v_prefixArgs_6894_);
return v___x_6920_;
}
}
else
{
lean_object* v_a_6930_; lean_object* v___x_6932_; uint8_t v_isShared_6933_; uint8_t v_isSharedCheck_6937_; 
lean_dec_ref(v_value_6908_);
lean_dec(v_declName_6906_);
lean_dec_ref(v_decrTactics_6898_);
lean_dec_ref(v_funNames_6897_);
lean_dec_ref(v_argsPacker_6895_);
lean_dec_ref(v_prefixArgs_6894_);
v_a_6930_ = lean_ctor_get(v___x_6916_, 0);
v_isSharedCheck_6937_ = !lean_is_exclusive(v___x_6916_);
if (v_isSharedCheck_6937_ == 0)
{
v___x_6932_ = v___x_6916_;
v_isShared_6933_ = v_isSharedCheck_6937_;
goto v_resetjp_6931_;
}
else
{
lean_inc(v_a_6930_);
lean_dec(v___x_6916_);
v___x_6932_ = lean_box(0);
v_isShared_6933_ = v_isSharedCheck_6937_;
goto v_resetjp_6931_;
}
v_resetjp_6931_:
{
lean_object* v___x_6935_; 
if (v_isShared_6933_ == 0)
{
v___x_6935_ = v___x_6932_;
goto v_reusejp_6934_;
}
else
{
lean_object* v_reuseFailAlloc_6936_; 
v_reuseFailAlloc_6936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6936_, 0, v_a_6930_);
v___x_6935_ = v_reuseFailAlloc_6936_;
goto v_reusejp_6934_;
}
v_reusejp_6934_:
{
return v___x_6935_;
}
}
}
}
else
{
lean_dec_ref(v_value_6908_);
lean_dec(v_declName_6906_);
lean_dec_ref(v_decrTactics_6898_);
lean_dec_ref(v_funNames_6897_);
lean_dec_ref(v_wfRel_6896_);
lean_dec_ref(v_argsPacker_6895_);
lean_dec_ref(v_prefixArgs_6894_);
return v___x_6909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6938_, lean_object* v_prefixArgs_6939_, lean_object* v_argsPacker_6940_, lean_object* v_wfRel_6941_, lean_object* v_funNames_6942_, lean_object* v_decrTactics_6943_, lean_object* v_a_6944_, lean_object* v_a_6945_, lean_object* v_a_6946_, lean_object* v_a_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_, lean_object* v_a_6950_){
_start:
{
lean_object* v_res_6951_; 
v_res_6951_ = l_Lean_Elab_WF_mkFix(v_preDef_6938_, v_prefixArgs_6939_, v_argsPacker_6940_, v_wfRel_6941_, v_funNames_6942_, v_decrTactics_6943_, v_a_6944_, v_a_6945_, v_a_6946_, v_a_6947_, v_a_6948_, v_a_6949_);
lean_dec(v_a_6949_);
lean_dec_ref(v_a_6948_);
lean_dec(v_a_6947_);
lean_dec_ref(v_a_6946_);
lean_dec(v_a_6945_);
lean_dec_ref(v_a_6944_);
return v_res_6951_;
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
