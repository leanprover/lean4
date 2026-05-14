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
lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_370_; 
v_ref_323_ = lean_ctor_get(v___y_320_, 5);
v___x_324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_370_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_370_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_370_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v_traceState_330_; lean_object* v_env_331_; lean_object* v_nextMacroScope_332_; lean_object* v_ngen_333_; lean_object* v_auxDeclNGen_334_; lean_object* v_cache_335_; lean_object* v_messages_336_; lean_object* v_infoState_337_; lean_object* v_snapshotTasks_338_; lean_object* v_newDecls_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_369_; 
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
v_newDecls_339_ = lean_ctor_get(v___x_329_, 9);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_369_ == 0)
{
v___x_341_ = v___x_329_;
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_newDecls_339_);
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
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint64_t v_tid_343_; lean_object* v_traces_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_tid_343_ = lean_ctor_get_uint64(v_traceState_330_, sizeof(void*)*1);
v_traces_344_ = lean_ctor_get(v_traceState_330_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_traceState_330_);
if (v_isSharedCheck_368_ == 0)
{
v___x_346_ = v_traceState_330_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_traces_344_);
lean_dec(v_traceState_330_);
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
lean_ctor_set(v___x_352_, 0, v_cls_316_);
lean_ctor_set(v___x_352_, 1, v___x_348_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set_float(v___x_352_, sizeof(void*)*3, v___x_349_);
lean_ctor_set_float(v___x_352_, sizeof(void*)*3 + 8, v___x_349_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*3 + 16, v___x_350_);
v___x_353_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_354_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v_a_325_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
lean_inc(v_ref_323_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_ref_323_);
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
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_env_331_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_nextMacroScope_332_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_ngen_333_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_auxDeclNGen_334_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_cache_335_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_messages_336_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_infoState_337_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v_snapshotTasks_338_);
lean_ctor_set(v_reuseFailAlloc_366_, 9, v_newDecls_339_);
v___x_360_ = v_reuseFailAlloc_366_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_361_ = lean_st_ref_set(v___y_321_, v___x_360_);
v___x_362_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_362_);
v___x_364_ = v___x_327_;
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
v_ref_510_ = lean_ctor_get(v___y_507_, 5);
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
lean_dec_ref(v___x_636_);
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
lean_dec_ref(v___x_646_);
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
lean_dec_ref(v___x_563_);
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
lean_dec_ref(v___x_565_);
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
lean_dec_ref(v___x_573_);
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
v___x_672_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v_fileName_820_; lean_object* v_fileMap_821_; lean_object* v_options_822_; lean_object* v_currRecDepth_823_; lean_object* v_maxRecDepth_824_; lean_object* v_ref_825_; lean_object* v_currNamespace_826_; lean_object* v_openDecls_827_; lean_object* v_initHeartbeats_828_; lean_object* v_maxHeartbeats_829_; lean_object* v_quotContext_830_; lean_object* v_currMacroScope_831_; uint8_t v_diag_832_; lean_object* v_cancelTk_x3f_833_; uint8_t v_suppressElabErrors_834_; lean_object* v_inheritedTraceOptions_835_; lean_object* v_ref_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_fileName_820_ = lean_ctor_get(v___y_817_, 0);
v_fileMap_821_ = lean_ctor_get(v___y_817_, 1);
v_options_822_ = lean_ctor_get(v___y_817_, 2);
v_currRecDepth_823_ = lean_ctor_get(v___y_817_, 3);
v_maxRecDepth_824_ = lean_ctor_get(v___y_817_, 4);
v_ref_825_ = lean_ctor_get(v___y_817_, 5);
v_currNamespace_826_ = lean_ctor_get(v___y_817_, 6);
v_openDecls_827_ = lean_ctor_get(v___y_817_, 7);
v_initHeartbeats_828_ = lean_ctor_get(v___y_817_, 8);
v_maxHeartbeats_829_ = lean_ctor_get(v___y_817_, 9);
v_quotContext_830_ = lean_ctor_get(v___y_817_, 10);
v_currMacroScope_831_ = lean_ctor_get(v___y_817_, 11);
v_diag_832_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*14);
v_cancelTk_x3f_833_ = lean_ctor_get(v___y_817_, 12);
v_suppressElabErrors_834_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_835_ = lean_ctor_get(v___y_817_, 13);
v_ref_836_ = l_Lean_replaceRef(v_ref_809_, v_ref_825_);
lean_inc_ref(v_inheritedTraceOptions_835_);
lean_inc(v_cancelTk_x3f_833_);
lean_inc(v_currMacroScope_831_);
lean_inc(v_quotContext_830_);
lean_inc(v_maxHeartbeats_829_);
lean_inc(v_initHeartbeats_828_);
lean_inc(v_openDecls_827_);
lean_inc(v_currNamespace_826_);
lean_inc(v_maxRecDepth_824_);
lean_inc(v_currRecDepth_823_);
lean_inc_ref(v_options_822_);
lean_inc_ref(v_fileMap_821_);
lean_inc_ref(v_fileName_820_);
v___x_837_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_837_, 0, v_fileName_820_);
lean_ctor_set(v___x_837_, 1, v_fileMap_821_);
lean_ctor_set(v___x_837_, 2, v_options_822_);
lean_ctor_set(v___x_837_, 3, v_currRecDepth_823_);
lean_ctor_set(v___x_837_, 4, v_maxRecDepth_824_);
lean_ctor_set(v___x_837_, 5, v_ref_836_);
lean_ctor_set(v___x_837_, 6, v_currNamespace_826_);
lean_ctor_set(v___x_837_, 7, v_openDecls_827_);
lean_ctor_set(v___x_837_, 8, v_initHeartbeats_828_);
lean_ctor_set(v___x_837_, 9, v_maxHeartbeats_829_);
lean_ctor_set(v___x_837_, 10, v_quotContext_830_);
lean_ctor_set(v___x_837_, 11, v_currMacroScope_831_);
lean_ctor_set(v___x_837_, 12, v_cancelTk_x3f_833_);
lean_ctor_set(v___x_837_, 13, v_inheritedTraceOptions_835_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*14, v_diag_832_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*14 + 1, v_suppressElabErrors_834_);
v___x_838_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_810_, v___y_815_, v___y_816_, v___x_837_, v___y_818_);
lean_dec_ref(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_839_, v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v_ref_839_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_851_, lean_object* v_msg_852_, lean_object* v_declHint_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_865_; 
v___x_863_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_852_, v_declHint_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___x_865_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_851_, v_a_864_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_866_, lean_object* v_msg_867_, lean_object* v_declHint_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_866_, v_msg_867_, v_declHint_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v_ref_866_);
return v_res_878_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_885_, lean_object* v_constName_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_896_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_897_ = 0;
lean_inc(v_constName_886_);
v___x_898_ = l_Lean_MessageData_ofConstName(v_constName_886_, v___x_897_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_885_, v___x_901_, v_constName_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_903_, lean_object* v_constName_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_903_, v_constName_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v_ref_903_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_ref_925_; lean_object* v___x_926_; 
v_ref_925_ = lean_ctor_get(v___y_922_, 5);
v___x_926_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_925_, v_constName_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_env_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v___x_948_ = lean_st_ref_get(v___y_946_);
v_env_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_env_949_);
lean_dec(v___x_948_);
v___x_950_ = 0;
lean_inc(v_constName_938_);
v___x_951_ = l_Lean_Environment_find_x3f(v_env_949_, v_constName_938_, v___x_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_952_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_constName_938_);
v_val_953_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 0);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_953_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_env_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_st_ref_get(v___y_973_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v___x_977_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_976_, v_declName_972_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_979_, v___y_980_);
lean_dec(v___y_980_);
return v_res_982_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_instMonadEIO(lean_box(0));
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_toApplicative_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1095_; 
v___x_1000_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_1001_ = l_StateRefT_x27_instMonad___redArg(v___x_1000_);
v_toApplicative_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1001_, 1);
lean_dec(v_unused_1096_);
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1095_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_toApplicative_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1095_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_toFunctor_1006_; lean_object* v_toSeq_1007_; lean_object* v_toSeqLeft_1008_; lean_object* v_toSeqRight_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1093_; 
v_toFunctor_1006_ = lean_ctor_get(v_toApplicative_1002_, 0);
v_toSeq_1007_ = lean_ctor_get(v_toApplicative_1002_, 2);
v_toSeqLeft_1008_ = lean_ctor_get(v_toApplicative_1002_, 3);
v_toSeqRight_1009_ = lean_ctor_get(v_toApplicative_1002_, 4);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_toApplicative_1002_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_toApplicative_1002_, 1);
lean_dec(v_unused_1094_);
v___x_1011_ = v_toApplicative_1002_;
v_isShared_1012_ = v_isSharedCheck_1093_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_toSeqRight_1009_);
lean_inc(v_toSeqLeft_1008_);
lean_inc(v_toSeq_1007_);
lean_inc(v_toFunctor_1006_);
lean_dec(v_toApplicative_1002_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1093_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___x_1022_; 
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1014_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1006_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toFunctor_1006_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___f_1015_);
lean_ctor_set(v___x_1017_, 1, v___f_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqRight_1009_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeqLeft_1008_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toSeq_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v___f_1018_);
lean_ctor_set(v___x_1011_, 3, v___f_1019_);
lean_ctor_set(v___x_1011_, 2, v___f_1020_);
lean_ctor_set(v___x_1011_, 1, v___f_1013_);
lean_ctor_set(v___x_1011_, 0, v___x_1017_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___f_1020_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v___f_1018_);
v___x_1022_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___f_1014_);
lean_ctor_set(v___x_1004_, 0, v___x_1022_);
v___x_1024_ = v___x_1004_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___f_1014_);
v___x_1024_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v_toApplicative_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1089_; 
v___x_1025_ = l_StateRefT_x27_instMonad___redArg(v___x_1024_);
v_toApplicative_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1025_, 1);
lean_dec(v_unused_1090_);
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1089_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_toApplicative_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1089_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_toFunctor_1030_; lean_object* v_toSeq_1031_; lean_object* v_toSeqLeft_1032_; lean_object* v_toSeqRight_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1087_; 
v_toFunctor_1030_ = lean_ctor_get(v_toApplicative_1026_, 0);
v_toSeq_1031_ = lean_ctor_get(v_toApplicative_1026_, 2);
v_toSeqLeft_1032_ = lean_ctor_get(v_toApplicative_1026_, 3);
v_toSeqRight_1033_ = lean_ctor_get(v_toApplicative_1026_, 4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_toApplicative_1026_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_dec(v_unused_1088_);
v___x_1035_ = v_toApplicative_1026_;
v_isShared_1036_ = v_isSharedCheck_1087_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_toSeqRight_1033_);
lean_inc(v_toSeqLeft_1032_);
lean_inc(v_toSeq_1031_);
lean_inc(v_toFunctor_1030_);
lean_dec(v_toApplicative_1026_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1087_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1046_; 
v___f_1037_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1038_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1030_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toFunctor_1030_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toFunctor_1030_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___f_1039_);
lean_ctor_set(v___x_1041_, 1, v___f_1040_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeqRight_1033_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toSeqLeft_1032_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toSeq_1031_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 4, v___f_1042_);
lean_ctor_set(v___x_1035_, 3, v___f_1043_);
lean_ctor_set(v___x_1035_, 2, v___f_1044_);
lean_ctor_set(v___x_1035_, 1, v___f_1037_);
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1046_ = v___x_1035_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v___f_1044_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___f_1042_);
v___x_1046_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___f_1038_);
lean_ctor_set(v___x_1028_, 0, v___x_1046_);
v___x_1048_ = v___x_1028_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___f_1038_);
v___x_1048_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v_toApplicative_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1083_; 
v___x_1049_ = l_StateRefT_x27_instMonad___redArg(v___x_1048_);
v_toApplicative_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1049_, 1);
lean_dec(v_unused_1084_);
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1083_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_toApplicative_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1083_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_toFunctor_1054_; lean_object* v_toSeq_1055_; lean_object* v_toSeqLeft_1056_; lean_object* v_toSeqRight_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1081_; 
v_toFunctor_1054_ = lean_ctor_get(v_toApplicative_1050_, 0);
v_toSeq_1055_ = lean_ctor_get(v_toApplicative_1050_, 2);
v_toSeqLeft_1056_ = lean_ctor_get(v_toApplicative_1050_, 3);
v_toSeqRight_1057_ = lean_ctor_get(v_toApplicative_1050_, 4);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_toApplicative_1050_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_toApplicative_1050_, 1);
lean_dec(v_unused_1082_);
v___x_1059_ = v_toApplicative_1050_;
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_toSeqRight_1057_);
lean_inc(v_toSeqLeft_1056_);
lean_inc(v_toSeq_1055_);
lean_inc(v_toFunctor_1054_);
lean_dec(v_toApplicative_1050_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1070_; 
v___f_1061_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1062_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1054_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toFunctor_1054_);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1064_, 0, v_toFunctor_1054_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___f_1063_);
lean_ctor_set(v___x_1065_, 1, v___f_1064_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toSeqRight_1057_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toSeqLeft_1056_);
v___f_1068_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1068_, 0, v_toSeq_1055_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v___f_1066_);
lean_ctor_set(v___x_1059_, 3, v___f_1067_);
lean_ctor_set(v___x_1059_, 2, v___f_1068_);
lean_ctor_set(v___x_1059_, 1, v___f_1061_);
lean_ctor_set(v___x_1059_, 0, v___x_1065_);
v___x_1070_ = v___x_1059_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1061_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v___f_1068_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v___f_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v___f_1066_);
v___x_1070_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___f_1062_);
lean_ctor_set(v___x_1052_, 0, v___x_1070_);
v___x_1072_ = v___x_1052_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___f_1062_);
v___x_1072_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_58772__overap_1077_; lean_object* v___x_1078_; 
v___x_1073_ = l_StateRefT_x27_instMonad___redArg(v___x_1072_);
v___x_1074_ = l_StateRefT_x27_instMonad___redArg(v___x_1073_);
v___x_1075_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1076_ = l_instInhabitedOfMonad___redArg(v___x_1074_, v___x_1075_);
v___x_58772__overap_1077_ = lean_panic_fn_borrowed(v___x_1076_, v_msg_990_);
lean_dec(v___x_1076_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_992_);
lean_inc(v___y_991_);
v___x_1078_ = lean_apply_9(v___x_58772__overap_1077_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, lean_box(0));
return v___x_1078_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___y_1098_);
return v_res_1107_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1112_ = lean_unsigned_to_nat(53u);
v___x_1113_ = lean_unsigned_to_nat(62u);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1116_ = l_mkPanicMessageWithDecl(v___x_1115_, v___x_1114_, v___x_1113_, v___x_1112_, v___x_1111_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1117_, size_t v_i_1118_, lean_object* v_bs_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_lt(v_i_1118_, v_sz_1117_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_bs_1119_);
return v___x_1130_;
}
else
{
lean_object* v_v_1131_; lean_object* v___x_1132_; 
v_v_1131_ = lean_array_uget_borrowed(v_bs_1119_, v_i_1118_);
lean_inc(v_v_1131_);
v___x_1132_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1131_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v_bs_x27_1135_; lean_object* v_a_1137_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v_bs_x27_1135_ = lean_array_uset(v_bs_1119_, v_i_1118_, v___x_1134_);
if (lean_obj_tag(v_a_1133_) == 6)
{
lean_object* v_val_1142_; lean_object* v_numFields_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_val_1142_ = lean_ctor_get(v_a_1133_, 0);
lean_inc_ref(v_val_1142_);
lean_dec_ref(v_a_1133_);
v_numFields_1143_ = lean_ctor_get(v_val_1142_, 4);
lean_inc(v_numFields_1143_);
lean_dec_ref(v_val_1142_);
v___x_1144_ = 0;
v___x_1145_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1145_, 0, v_numFields_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1134_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*2, v___x_1144_);
v_a_1137_ = v___x_1145_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v_a_1133_);
v___x_1146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1147_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1146_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1147_);
v_a_1137_ = v_a_1148_;
goto v___jp_1136_;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_bs_x27_1135_);
v_a_1149_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1147_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
v___jp_1136_:
{
size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_add(v_i_1118_, v___x_1138_);
v___x_1140_ = lean_array_uset(v_bs_x27_1135_, v_i_1118_, v_a_1137_);
v_i_1118_ = v___x_1139_;
v_bs_1119_ = v___x_1140_;
goto _start;
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_bs_1119_);
v_a_1157_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1132_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1132_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1165_, lean_object* v_i_1166_, lean_object* v_bs_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
size_t v_sz_boxed_1177_; size_t v_i_boxed_1178_; lean_object* v_res_1179_; 
v_sz_boxed_1177_ = lean_unbox_usize(v_sz_1165_);
lean_dec(v_sz_1165_);
v_i_boxed_1178_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1177_, v_i_boxed_1178_, v_bs_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v___y_1168_);
return v_res_1179_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1180_; lean_object* v_dummy_1181_; 
v___x_1180_ = lean_box(0);
v_dummy_1181_ = l_Lean_Expr_sort___override(v___x_1180_);
return v_dummy_1181_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_unsigned_to_nat(16u);
v___x_1184_ = lean_mk_array(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1190_, uint8_t v_alsoCasesOn_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_Expr_isApp(v_e_1190_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v_e_1190_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Expr_getAppFn(v_e_1190_);
if (lean_obj_tag(v___x_1207_) == 4)
{
lean_object* v_declName_1208_; lean_object* v_us_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1365_; 
v_declName_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_n(v_declName_1208_, 2);
v_us_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc(v_us_1209_);
lean_dec_ref(v___x_1207_);
v___x_1210_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1208_, v___y_1199_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1365_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1365_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
if (lean_obj_tag(v_a_1211_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1257_; 
v_val_1215_ = lean_ctor_get(v_a_1211_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_a_1211_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1217_ = v_a_1211_;
v_isShared_1218_ = v_isSharedCheck_1257_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v_a_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1257_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_dummy_1219_; lean_object* v_nargs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_args_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v_dummy_1219_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1220_ = l_Lean_Expr_getAppNumArgs(v_e_1190_);
lean_inc(v_nargs_1220_);
v___x_1221_ = lean_mk_array(v_nargs_1220_, v_dummy_1219_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v_nargs_1220_, v___x_1222_);
lean_dec(v_nargs_1220_);
v_args_1224_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1190_, v___x_1221_, v___x_1223_);
v___x_1225_ = lean_array_get_size(v_args_1224_);
v___x_1226_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1215_);
v___x_1227_ = lean_nat_dec_lt(v___x_1225_, v___x_1226_);
lean_dec(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v_numParams_1228_; lean_object* v_numDiscrs_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_numParams_1228_ = lean_ctor_get(v_val_1215_, 0);
v_numDiscrs_1229_ = lean_ctor_get(v_val_1215_, 1);
v___x_1230_ = lean_array_mk(v_us_1209_);
v___x_1231_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1228_);
v___x_1232_ = l_Array_extract___redArg(v_args_1224_, v___x_1231_, v_numParams_1228_);
v___x_1233_ = l_Lean_instInhabitedExpr;
v___x_1234_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1215_);
v___x_1235_ = lean_array_get(v___x_1233_, v_args_1224_, v___x_1234_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_nat_add(v_numParams_1228_, v___x_1222_);
v___x_1237_ = lean_nat_add(v___x_1236_, v_numDiscrs_1229_);
lean_inc(v___x_1237_);
lean_inc_ref_n(v_args_1224_, 2);
v___x_1238_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1236_, v___x_1237_);
v___x_1239_ = l_Subarray_copy___redArg(v___x_1238_);
v___x_1240_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1215_);
v___x_1241_ = lean_nat_add(v___x_1237_, v___x_1240_);
lean_dec(v___x_1240_);
lean_inc(v___x_1241_);
v___x_1242_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1237_, v___x_1241_);
v___x_1243_ = l_Subarray_copy___redArg(v___x_1242_);
v___x_1244_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1241_, v___x_1225_);
v___x_1245_ = l_Subarray_copy___redArg(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1246_, 0, v_val_1215_);
lean_ctor_set(v___x_1246_, 1, v_declName_1208_);
lean_ctor_set(v___x_1246_, 2, v___x_1230_);
lean_ctor_set(v___x_1246_, 3, v___x_1232_);
lean_ctor_set(v___x_1246_, 4, v___x_1235_);
lean_ctor_set(v___x_1246_, 5, v___x_1239_);
lean_ctor_set(v___x_1246_, 6, v___x_1243_);
lean_ctor_set(v___x_1246_, 7, v___x_1245_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1246_);
v___x_1248_ = v___x_1217_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1248_);
v___x_1250_ = v___x_1213_;
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
else
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec_ref(v_args_1224_);
lean_del_object(v___x_1217_);
lean_dec(v_val_1215_);
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
v___x_1253_ = lean_box(0);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1253_);
v___x_1255_ = v___x_1213_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v___x_1258_; 
lean_del_object(v___x_1213_);
lean_dec(v_a_1211_);
v___x_1258_ = lean_st_ref_get(v___y_1199_);
if (v_alsoCasesOn_1191_ == 0)
{
lean_dec(v___x_1258_);
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
lean_dec_ref(v_e_1190_);
goto v___jp_1201_;
}
else
{
lean_object* v_env_1259_; uint8_t v___x_1260_; 
v_env_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_env_1259_);
lean_dec(v___x_1258_);
lean_inc(v_declName_1208_);
v___x_1260_ = l_Lean_isCasesOnRecursor(v_env_1259_, v_declName_1208_);
if (v___x_1260_ == 0)
{
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
lean_dec_ref(v_e_1190_);
goto v___jp_1201_;
}
else
{
lean_object* v_indName_1261_; lean_object* v___x_1262_; 
v_indName_1261_ = l_Lean_Name_getPrefix(v_declName_1208_);
v___x_1262_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1261_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1356_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1356_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1356_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
if (lean_obj_tag(v_a_1263_) == 5)
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1351_; 
v_val_1267_ = lean_ctor_get(v_a_1263_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1263_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1269_ = v_a_1263_;
v_isShared_1270_ = v_isSharedCheck_1351_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v_a_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1351_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_toConstantVal_1271_; lean_object* v_numParams_1272_; lean_object* v_numIndices_1273_; lean_object* v_ctors_1274_; lean_object* v_nargs_1275_; lean_object* v_dummy_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_args_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_toConstantVal_1271_ = lean_ctor_get(v_val_1267_, 0);
lean_inc_ref(v_toConstantVal_1271_);
v_numParams_1272_ = lean_ctor_get(v_val_1267_, 1);
lean_inc(v_numParams_1272_);
v_numIndices_1273_ = lean_ctor_get(v_val_1267_, 2);
lean_inc(v_numIndices_1273_);
v_ctors_1274_ = lean_ctor_get(v_val_1267_, 4);
lean_inc(v_ctors_1274_);
v_nargs_1275_ = l_Lean_Expr_getAppNumArgs(v_e_1190_);
v_dummy_1276_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1275_);
v___x_1277_ = lean_mk_array(v_nargs_1275_, v_dummy_1276_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_sub(v_nargs_1275_, v___x_1278_);
lean_dec(v_nargs_1275_);
v_args_1280_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1190_, v___x_1277_, v___x_1279_);
v___x_1281_ = lean_nat_add(v_numParams_1272_, v___x_1278_);
v___x_1282_ = lean_nat_add(v___x_1281_, v_numIndices_1273_);
v___x_1283_ = lean_nat_add(v___x_1282_, v___x_1278_);
lean_dec(v___x_1282_);
v___x_1284_ = l_Lean_InductiveVal_numCtors(v_val_1267_);
lean_dec_ref(v_val_1267_);
v___x_1285_ = lean_nat_add(v___x_1283_, v___x_1284_);
lean_dec(v___x_1284_);
v___x_1286_ = lean_array_get_size(v_args_1280_);
v___x_1287_ = lean_nat_dec_le(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec(v___x_1285_);
lean_dec(v___x_1283_);
lean_dec(v___x_1281_);
lean_dec_ref(v_args_1280_);
lean_dec(v_ctors_1274_);
lean_dec(v_numIndices_1273_);
lean_dec(v_numParams_1272_);
lean_dec_ref(v_toConstantVal_1271_);
lean_del_object(v___x_1269_);
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
v___x_1288_ = lean_box(0);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1288_);
v___x_1290_ = v___x_1265_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
lean_object* v___x_1292_; lean_object* v_params_1293_; lean_object* v___x_1294_; lean_object* v_motive_1295_; lean_object* v_discrs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_discrInfos_1299_; lean_object* v_alts_1300_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v_lower_1342_; lean_object* v_upper_1343_; uint8_t v___x_1350_; 
lean_del_object(v___x_1265_);
v___x_1292_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1272_);
lean_inc_ref_n(v_args_1280_, 3);
v_params_1293_ = l_Array_toSubarray___redArg(v_args_1280_, v___x_1292_, v_numParams_1272_);
v___x_1294_ = l_Lean_instInhabitedExpr;
v_motive_1295_ = lean_array_get(v___x_1294_, v_args_1280_, v_numParams_1272_);
lean_dec(v_numParams_1272_);
lean_inc(v___x_1283_);
v_discrs_1296_ = l_Array_toSubarray___redArg(v_args_1280_, v___x_1281_, v___x_1283_);
v___x_1297_ = lean_nat_add(v_numIndices_1273_, v___x_1278_);
lean_dec(v_numIndices_1273_);
v___x_1298_ = lean_box(0);
v_discrInfos_1299_ = lean_mk_array(v___x_1297_, v___x_1298_);
lean_inc(v___x_1285_);
v_alts_1300_ = l_Array_toSubarray___redArg(v_args_1280_, v___x_1283_, v___x_1285_);
v___x_1350_ = lean_nat_dec_le(v___x_1285_, v___x_1292_);
if (v___x_1350_ == 0)
{
v_lower_1342_ = v___x_1285_;
v_upper_1343_ = v___x_1286_;
goto v___jp_1341_;
}
else
{
lean_dec(v___x_1285_);
v_lower_1342_ = v___x_1292_;
v_upper_1343_ = v___x_1286_;
goto v___jp_1341_;
}
v___jp_1301_:
{
lean_object* v___x_1304_; size_t v_sz_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_array_mk(v_ctors_1274_);
v_sz_1305_ = lean_array_size(v___x_1304_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1305_, v___x_1306_, v___x_1304_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1332_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1332_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1332_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_start_1312_; lean_object* v_stop_1313_; lean_object* v_start_1314_; lean_object* v_stop_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_start_1312_ = lean_ctor_get(v_params_1293_, 1);
lean_inc(v_start_1312_);
v_stop_1313_ = lean_ctor_get(v_params_1293_, 2);
lean_inc(v_stop_1313_);
v_start_1314_ = lean_ctor_get(v_discrs_1296_, 1);
lean_inc(v_start_1314_);
v_stop_1315_ = lean_ctor_get(v_discrs_1296_, 2);
lean_inc(v_stop_1315_);
v___x_1316_ = lean_nat_sub(v_stop_1313_, v_start_1312_);
lean_dec(v_start_1312_);
lean_dec(v_stop_1313_);
v___x_1317_ = lean_nat_sub(v_stop_1315_, v_start_1314_);
lean_dec(v_start_1314_);
lean_dec(v_stop_1315_);
v___x_1318_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1319_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1316_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v_a_1308_);
lean_ctor_set(v___x_1319_, 3, v___y_1303_);
lean_ctor_set(v___x_1319_, 4, v_discrInfos_1299_);
lean_ctor_set(v___x_1319_, 5, v___x_1318_);
v___x_1320_ = lean_array_mk(v_us_1209_);
v___x_1321_ = l_Subarray_copy___redArg(v_params_1293_);
v___x_1322_ = l_Subarray_copy___redArg(v_discrs_1296_);
v___x_1323_ = l_Subarray_copy___redArg(v_alts_1300_);
v___x_1324_ = l_Subarray_copy___redArg(v___y_1302_);
v___x_1325_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1319_);
lean_ctor_set(v___x_1325_, 1, v_declName_1208_);
lean_ctor_set(v___x_1325_, 2, v___x_1320_);
lean_ctor_set(v___x_1325_, 3, v___x_1321_);
lean_ctor_set(v___x_1325_, 4, v_motive_1295_);
lean_ctor_set(v___x_1325_, 5, v___x_1322_);
lean_ctor_set(v___x_1325_, 6, v___x_1323_);
lean_ctor_set(v___x_1325_, 7, v___x_1324_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
lean_ctor_set(v___x_1269_, 0, v___x_1325_);
v___x_1327_ = v___x_1269_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1327_);
v___x_1329_ = v___x_1310_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_alts_1300_);
lean_dec_ref(v_discrInfos_1299_);
lean_dec_ref(v_discrs_1296_);
lean_dec(v_motive_1295_);
lean_dec_ref(v_params_1293_);
lean_del_object(v___x_1269_);
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
v_a_1333_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1307_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1307_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
v___jp_1341_:
{
lean_object* v_levelParams_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_levelParams_1344_ = lean_ctor_get(v_toConstantVal_1271_, 1);
lean_inc(v_levelParams_1344_);
lean_dec_ref(v_toConstantVal_1271_);
v___x_1345_ = l_Array_toSubarray___redArg(v_args_1280_, v_lower_1342_, v_upper_1343_);
v___x_1346_ = l_List_lengthTR___redArg(v_levelParams_1344_);
lean_dec(v_levelParams_1344_);
v___x_1347_ = l_List_lengthTR___redArg(v_us_1209_);
v___x_1348_ = lean_nat_dec_eq(v___x_1346_, v___x_1347_);
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1302_ = v___x_1345_;
v___y_1303_ = v___x_1349_;
goto v___jp_1301_;
}
else
{
v___y_1302_ = v___x_1345_;
v___y_1303_ = v___x_1298_;
goto v___jp_1301_;
}
}
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_dec(v_a_1263_);
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
lean_dec_ref(v_e_1190_);
v___x_1352_ = lean_box(0);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1352_);
v___x_1354_ = v___x_1265_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_us_1209_);
lean_dec(v_declName_1208_);
lean_dec_ref(v_e_1190_);
v_a_1357_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1262_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1262_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
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
lean_dec_ref(v___x_1207_);
lean_dec_ref(v_e_1190_);
goto v___jp_1201_;
}
}
v___jp_1201_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1366_, lean_object* v_alsoCasesOn_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1377_; lean_object* v_res_1378_; 
v_alsoCasesOn_boxed_1377_ = lean_unbox(v_alsoCasesOn_1367_);
v_res_1378_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1366_, v_alsoCasesOn_boxed_1377_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec(v___y_1368_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v_b_1384_, lean_object* v_c_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc(v___y_1380_);
v___x_1391_ = lean_apply_11(v_k_1379_, v_b_1384_, v_c_1385_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, lean_box(0));
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v_b_1397_, lean_object* v_c_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v_b_1397_, v_c_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec(v___y_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1405_, lean_object* v_maxFVars_1406_, lean_object* v_k_1407_, uint8_t v_cleanupAnnotations_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___f_1418_; uint8_t v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc(v___y_1410_);
lean_inc(v___y_1409_);
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1418_, 0, v_k_1407_);
lean_closure_set(v___f_1418_, 1, v___y_1409_);
lean_closure_set(v___f_1418_, 2, v___y_1410_);
lean_closure_set(v___f_1418_, 3, v___y_1411_);
lean_closure_set(v___f_1418_, 4, v___y_1412_);
v___x_1419_ = 1;
v___x_1420_ = 0;
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_maxFVars_1406_);
v___x_1422_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1405_, v___x_1419_, v___x_1420_, v___x_1419_, v___x_1420_, v___x_1421_, v___f_1418_, v_cleanupAnnotations_1408_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec_ref(v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
return v___x_1422_;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1431_, lean_object* v_maxFVars_1432_, lean_object* v_k_1433_, lean_object* v_cleanupAnnotations_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1444_; lean_object* v_res_1445_; 
v_cleanupAnnotations_boxed_1444_ = lean_unbox(v_cleanupAnnotations_1434_);
v_res_1445_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1431_, v_maxFVars_1432_, v_k_1433_, v_cleanupAnnotations_boxed_1444_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec(v___y_1435_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc(v___y_1447_);
v___x_1457_ = lean_apply_10(v_k_1446_, v_b_1451_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, lean_box(0));
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v_b_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1470_, lean_object* v_type_1471_, lean_object* v_val_1472_, lean_object* v_k_1473_, uint8_t v_nondep_1474_, uint8_t v_kind_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___f_1485_; lean_object* v___x_1486_; 
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc(v___y_1476_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1485_, 0, v_k_1473_);
lean_closure_set(v___f_1485_, 1, v___y_1476_);
lean_closure_set(v___f_1485_, 2, v___y_1477_);
lean_closure_set(v___f_1485_, 3, v___y_1478_);
lean_closure_set(v___f_1485_, 4, v___y_1479_);
v___x_1486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1470_, v_type_1471_, v_val_1472_, v___f_1485_, v_nondep_1474_, v_kind_1475_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1486_) == 0)
{
return v___x_1486_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1495_, lean_object* v_type_1496_, lean_object* v_val_1497_, lean_object* v_k_1498_, lean_object* v_nondep_1499_, lean_object* v_kind_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_nondep_boxed_1510_; uint8_t v_kind_boxed_1511_; lean_object* v_res_1512_; 
v_nondep_boxed_1510_ = lean_unbox(v_nondep_1499_);
v_kind_boxed_1511_ = lean_unbox(v_kind_1500_);
v_res_1512_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1495_, v_type_1496_, v_val_1497_, v_k_1498_, v_nondep_boxed_1510_, v_kind_boxed_1511_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1513_, uint8_t v_usedLetOnly_1514_, lean_object* v_x_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1522_);
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v_x_1515_);
v___x_1525_ = lean_apply_10(v_k_1513_, v_x_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, lean_box(0));
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
v___x_1529_ = lean_array_push(v___x_1528_, v_x_1515_);
v___x_1530_ = 0;
v___x_1531_ = 1;
v___x_1532_ = l_Lean_Meta_mkLetFVars(v___x_1529_, v_a_1526_, v_usedLetOnly_1514_, v___x_1530_, v___x_1531_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec_ref(v___x_1529_);
return v___x_1532_;
}
else
{
lean_dec_ref(v_x_1515_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1533_, lean_object* v_usedLetOnly_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v_usedLetOnly_boxed_1545_; lean_object* v_res_1546_; 
v_usedLetOnly_boxed_1545_ = lean_unbox(v_usedLetOnly_1534_);
v_res_1546_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1533_, v_usedLetOnly_boxed_1545_, v_x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v___y_1536_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1547_, lean_object* v_type_1548_, lean_object* v_val_1549_, lean_object* v_k_1550_, uint8_t v_nondep_1551_, uint8_t v_kind_1552_, uint8_t v_usedLetOnly_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_box(v_usedLetOnly_1553_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1564_, 0, v_k_1550_);
lean_closure_set(v___f_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1547_, v_type_1548_, v_val_1549_, v___f_1564_, v_nondep_1551_, v_kind_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1566_, lean_object* v_type_1567_, lean_object* v_val_1568_, lean_object* v_k_1569_, lean_object* v_nondep_1570_, lean_object* v_kind_1571_, lean_object* v_usedLetOnly_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_nondep_boxed_1582_; uint8_t v_kind_boxed_1583_; uint8_t v_usedLetOnly_boxed_1584_; lean_object* v_res_1585_; 
v_nondep_boxed_1582_ = lean_unbox(v_nondep_1570_);
v_kind_boxed_1583_ = lean_unbox(v_kind_1571_);
v_usedLetOnly_boxed_1584_ = lean_unbox(v_usedLetOnly_1572_);
v_res_1585_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1566_, v_type_1567_, v_val_1568_, v_k_1569_, v_nondep_boxed_1582_, v_kind_boxed_1583_, v_usedLetOnly_boxed_1584_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec(v___y_1573_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1586_, uint8_t v_bi_1587_, lean_object* v_type_1588_, lean_object* v_k_1589_, uint8_t v_kind_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; 
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc(v___y_1591_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1600_, 0, v_k_1589_);
lean_closure_set(v___f_1600_, 1, v___y_1591_);
lean_closure_set(v___f_1600_, 2, v___y_1592_);
lean_closure_set(v___f_1600_, 3, v___y_1593_);
lean_closure_set(v___f_1600_, 4, v___y_1594_);
v___x_1601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1586_, v_bi_1587_, v_type_1588_, v___f_1600_, v_kind_1590_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
return v___x_1601_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1610_, lean_object* v_bi_1611_, lean_object* v_type_1612_, lean_object* v_k_1613_, lean_object* v_kind_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_bi_boxed_1624_; uint8_t v_kind_boxed_1625_; lean_object* v_res_1626_; 
v_bi_boxed_1624_ = lean_unbox(v_bi_1611_);
v_kind_boxed_1625_ = lean_unbox(v_kind_1614_);
v_res_1626_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1610_, v_bi_boxed_1624_, v_type_1612_, v_k_1613_, v_kind_boxed_1625_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc(v___y_1628_);
v___x_1637_ = lean_apply_9(v_k_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, lean_box(0));
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v___y_1639_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1649_, uint8_t v_allowLevelAssignments_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___f_1660_; lean_object* v___x_1661_; 
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc(v___y_1651_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1660_, 0, v_k_1649_);
lean_closure_set(v___f_1660_, 1, v___y_1651_);
lean_closure_set(v___f_1660_, 2, v___y_1652_);
lean_closure_set(v___f_1660_, 3, v___y_1653_);
lean_closure_set(v___f_1660_, 4, v___y_1654_);
v___x_1661_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1650_, v___f_1660_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1661_) == 0)
{
return v___x_1661_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1670_, lean_object* v_allowLevelAssignments_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1681_; lean_object* v_res_1682_; 
v_allowLevelAssignments_boxed_1681_ = lean_unbox(v_allowLevelAssignments_1671_);
v_res_1682_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1670_, v_allowLevelAssignments_boxed_1681_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1683_, lean_object* v_x_1684_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_box(0);
return v___x_1685_;
}
else
{
lean_object* v_key_1686_; lean_object* v_value_1687_; lean_object* v_tail_1688_; uint8_t v___x_1689_; 
v_key_1686_ = lean_ctor_get(v_x_1684_, 0);
v_value_1687_ = lean_ctor_get(v_x_1684_, 1);
v_tail_1688_ = lean_ctor_get(v_x_1684_, 2);
v___x_1689_ = lean_expr_eqv(v_key_1686_, v_a_1683_);
if (v___x_1689_ == 0)
{
v_x_1684_ = v_tail_1688_;
goto _start;
}
else
{
lean_object* v___x_1691_; 
lean_inc(v_value_1687_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_value_1687_);
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec_ref(v_a_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_buckets_1697_; lean_object* v___x_1698_; uint64_t v___x_1699_; uint64_t v___x_1700_; uint64_t v___x_1701_; uint64_t v_fold_1702_; uint64_t v___x_1703_; uint64_t v___x_1704_; uint64_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_buckets_1697_ = lean_ctor_get(v_m_1695_, 1);
v___x_1698_ = lean_array_get_size(v_buckets_1697_);
v___x_1699_ = l_Lean_Expr_hash(v_a_1696_);
v___x_1700_ = 32ULL;
v___x_1701_ = lean_uint64_shift_right(v___x_1699_, v___x_1700_);
v_fold_1702_ = lean_uint64_xor(v___x_1699_, v___x_1701_);
v___x_1703_ = 16ULL;
v___x_1704_ = lean_uint64_shift_right(v_fold_1702_, v___x_1703_);
v___x_1705_ = lean_uint64_xor(v_fold_1702_, v___x_1704_);
v___x_1706_ = lean_uint64_to_usize(v___x_1705_);
v___x_1707_ = lean_usize_of_nat(v___x_1698_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_sub(v___x_1707_, v___x_1708_);
v___x_1710_ = lean_usize_land(v___x_1706_, v___x_1709_);
v___x_1711_ = lean_array_uget_borrowed(v_buckets_1697_, v___x_1710_);
v___x_1712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1696_, v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1713_, v_a_1714_);
lean_dec_ref(v_a_1714_);
lean_dec_ref(v_m_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
lean_object* v_name_1718_; lean_object* v_defValue_1719_; lean_object* v_map_1720_; lean_object* v___x_1721_; 
v_name_1718_ = lean_ctor_get(v_opt_1717_, 0);
v_defValue_1719_ = lean_ctor_get(v_opt_1717_, 1);
v_map_1720_ = lean_ctor_get(v_opts_1716_, 0);
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1720_, v_name_1718_);
if (lean_obj_tag(v___x_1721_) == 0)
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_unbox(v_defValue_1719_);
return v___x_1722_;
}
else
{
lean_object* v_val_1723_; 
v_val_1723_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1723_);
lean_dec_ref(v___x_1721_);
if (lean_obj_tag(v_val_1723_) == 1)
{
uint8_t v_v_1724_; 
v_v_1724_ = lean_ctor_get_uint8(v_val_1723_, 0);
lean_dec_ref(v_val_1723_);
return v_v_1724_;
}
else
{
uint8_t v___x_1725_; 
lean_dec(v_val_1723_);
v___x_1725_ = lean_unbox(v_defValue_1719_);
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1726_, lean_object* v_opt_1727_){
_start:
{
uint8_t v_res_1728_; lean_object* v_r_1729_; 
v_res_1728_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1726_, v_opt_1727_);
lean_dec_ref(v_opt_1727_);
lean_dec_ref(v_opts_1726_);
v_r_1729_ = lean_box(v_res_1728_);
return v_r_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1730_, lean_object* v_b_1731_){
_start:
{
lean_object* v_array_1732_; lean_object* v_start_1733_; lean_object* v_stop_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1747_; 
v_array_1732_ = lean_ctor_get(v_a_1730_, 0);
v_start_1733_ = lean_ctor_get(v_a_1730_, 1);
v_stop_1734_ = lean_ctor_get(v_a_1730_, 2);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1736_ = v_a_1730_;
v_isShared_1737_ = v_isSharedCheck_1747_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_stop_1734_);
lean_inc(v_start_1733_);
lean_inc(v_array_1732_);
lean_dec(v_a_1730_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1747_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_lt(v_start_1733_, v_stop_1734_);
if (v___x_1738_ == 0)
{
lean_del_object(v___x_1736_);
lean_dec(v_stop_1734_);
lean_dec(v_start_1733_);
lean_dec_ref(v_array_1732_);
return v_b_1731_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_start_1733_, v___x_1739_);
lean_inc_ref(v_array_1732_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1740_);
v___x_1742_ = v___x_1736_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_array_1732_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_stop_1734_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_array_fget(v_array_1732_, v_start_1733_);
lean_dec(v_start_1733_);
lean_dec_ref(v_array_1732_);
v___x_1744_ = lean_array_push(v_b_1731_, v___x_1743_);
v_a_1730_ = v___x_1742_;
v_b_1731_ = v___x_1744_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1748_, lean_object* v_recFnName_1749_, lean_object* v_fixedPrefixSize_1750_, lean_object* v_F_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_expr_instantiate1(v_body_1748_, v_x_1752_);
v___x_1763_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1749_, v_fixedPrefixSize_1750_, v_F_1751_, v___x_1762_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; uint8_t v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_array_push(v___x_1766_, v_x_1752_);
v___x_1768_ = 0;
v___x_1769_ = 1;
v___x_1770_ = 1;
v___x_1771_ = l_Lean_Meta_mkLambdaFVars(v___x_1767_, v_a_1764_, v___x_1768_, v___x_1769_, v___x_1768_, v___x_1769_, v___x_1770_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec_ref(v___x_1767_);
return v___x_1771_;
}
else
{
lean_dec_ref(v_x_1752_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1772_, lean_object* v_recFnName_1773_, lean_object* v_fixedPrefixSize_1774_, lean_object* v_F_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1772_, v_recFnName_1773_, v_fixedPrefixSize_1774_, v_F_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v_body_1772_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1787_, lean_object* v_recFnName_1788_, lean_object* v_fixedPrefixSize_1789_, lean_object* v_F_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_expr_instantiate1(v_body_1787_, v_x_1791_);
v___x_1802_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1788_, v_fixedPrefixSize_1789_, v_F_1790_, v___x_1801_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; uint8_t v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_mk_empty_array_with_capacity(v___x_1804_);
v___x_1806_ = lean_array_push(v___x_1805_, v_x_1791_);
v___x_1807_ = 0;
v___x_1808_ = 1;
v___x_1809_ = 1;
v___x_1810_ = l_Lean_Meta_mkForallFVars(v___x_1806_, v_a_1803_, v___x_1807_, v___x_1808_, v___x_1808_, v___x_1809_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec_ref(v___x_1806_);
return v___x_1810_;
}
else
{
lean_dec_ref(v_x_1791_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1811_, lean_object* v_recFnName_1812_, lean_object* v_fixedPrefixSize_1813_, lean_object* v_F_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1811_, v_recFnName_1812_, v_fixedPrefixSize_1813_, v_F_1814_, v_x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v_body_1811_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1826_, lean_object* v_recFnName_1827_, lean_object* v_fixedPrefixSize_1828_, lean_object* v_F_1829_, lean_object* v_x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1826_, v_recFnName_1827_, v_fixedPrefixSize_1828_, v_F_1829_, v_x_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v_x_1830_);
lean_dec_ref(v_body_1826_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1843_, lean_object* v_fixedPrefixSize_1844_, lean_object* v_F_1845_, size_t v_sz_1846_, size_t v_i_1847_, lean_object* v_bs_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_lt(v_i_1847_, v_sz_1846_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec_ref(v_F_1845_);
lean_dec(v_fixedPrefixSize_1844_);
lean_dec(v_recFnName_1843_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_bs_1848_);
return v___x_1859_;
}
else
{
lean_object* v_v_1860_; lean_object* v___x_1861_; 
v_v_1860_ = lean_array_uget_borrowed(v_bs_1848_, v_i_1847_);
lean_inc(v_v_1860_);
lean_inc_ref(v_F_1845_);
lean_inc(v_fixedPrefixSize_1844_);
lean_inc(v_recFnName_1843_);
v___x_1861_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1843_, v_fixedPrefixSize_1844_, v_F_1845_, v_v_1860_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v_bs_x27_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(0u);
v_bs_x27_1864_ = lean_array_uset(v_bs_1848_, v_i_1847_, v___x_1863_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1847_, v___x_1865_);
v___x_1867_ = lean_array_uset(v_bs_x27_1864_, v_i_1847_, v_a_1862_);
v_i_1847_ = v___x_1866_;
v_bs_1848_ = v___x_1867_;
goto _start;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_bs_1848_);
lean_dec_ref(v_F_1845_);
lean_dec(v_fixedPrefixSize_1844_);
lean_dec(v_recFnName_1843_);
v_a_1869_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1861_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1861_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_cls_1884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1885_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1886_ = l_Lean_Name_append(v___x_1885_, v_cls_1884_);
return v___x_1886_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1890_, lean_object* v_fixedPrefixSize_1891_, lean_object* v_F_1892_, lean_object* v_e_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1915_ = l_Lean_Expr_getAppNumArgs(v_e_1893_);
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_fixedPrefixSize_1891_, v___x_1916_);
v___x_1918_ = lean_nat_dec_lt(v___x_1915_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v_dummy_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_args_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_dummy_1919_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1915_);
v___x_1920_ = lean_mk_array(v___x_1915_, v_dummy_1919_);
v___x_1921_ = lean_nat_sub(v___x_1915_, v___x_1916_);
lean_dec(v___x_1915_);
v_args_1922_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1893_, v___x_1920_, v___x_1921_);
v___x_1923_ = l_Lean_instInhabitedExpr;
v___x_1924_ = lean_array_get(v___x_1923_, v_args_1922_, v_fixedPrefixSize_1891_);
lean_inc_ref(v_F_1892_);
lean_inc(v_fixedPrefixSize_1891_);
lean_inc(v_recFnName_1890_);
v___x_1925_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1890_, v_fixedPrefixSize_1891_, v_F_1892_, v___x_1924_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
lean_inc_ref(v_F_1892_);
v___x_1927_ = l_Lean_Expr_app___override(v_F_1892_, v_a_1926_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc_ref(v___x_1927_);
v___x_1928_ = lean_infer_type(v___x_1927_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
v___x_1930_ = lean_whnf(v_a_1929_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = l_Lean_Expr_bindingDomain_x21(v_a_1931_);
lean_dec(v_a_1931_);
v___x_1933_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1932_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v_lower_1937_; lean_object* v_upper_1938_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = l_Lean_Expr_app___override(v___x_1927_, v_a_1934_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_get_size(v_args_1922_);
v___x_1964_ = lean_nat_dec_le(v___x_1917_, v___x_1962_);
if (v___x_1964_ == 0)
{
v_lower_1937_ = v___x_1917_;
v_upper_1938_ = v___x_1963_;
goto v___jp_1936_;
}
else
{
lean_dec(v___x_1917_);
v_lower_1937_ = v___x_1962_;
v_upper_1938_ = v___x_1963_;
goto v___jp_1936_;
}
v___jp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; size_t v_sz_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1939_ = l_Array_toSubarray___redArg(v_args_1922_, v_lower_1937_, v_upper_1938_);
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1941_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1939_, v___x_1940_);
v_sz_1942_ = lean_array_size(v___x_1941_);
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1890_, v_fixedPrefixSize_1891_, v_F_1892_, v_sz_1942_, v___x_1943_, v___x_1941_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1953_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = l_Lean_mkAppN(v___x_1935_, v_a_1945_);
lean_dec(v_a_1945_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1949_);
v___x_1951_ = v___x_1947_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v___x_1935_);
v_a_1954_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1944_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1944_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1927_);
lean_dec_ref(v_args_1922_);
lean_dec(v___x_1917_);
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
return v___x_1933_;
}
}
else
{
lean_dec_ref(v___x_1927_);
lean_dec_ref(v_args_1922_);
lean_dec(v___x_1917_);
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
return v___x_1930_;
}
}
else
{
lean_dec_ref(v___x_1927_);
lean_dec_ref(v_args_1922_);
lean_dec(v___x_1917_);
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
return v___x_1928_;
}
}
else
{
lean_dec_ref(v_args_1922_);
lean_dec(v___x_1917_);
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
return v___x_1925_;
}
}
else
{
lean_object* v_options_1965_; uint8_t v_hasTrace_1966_; 
lean_dec(v___x_1917_);
lean_dec(v___x_1915_);
v_options_1965_ = lean_ctor_get(v_a_1900_, 2);
v_hasTrace_1966_ = lean_ctor_get_uint8(v_options_1965_, sizeof(void*)*1);
if (v_hasTrace_1966_ == 0)
{
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
goto v___jp_1903_;
}
else
{
lean_object* v_inheritedTraceOptions_1967_; lean_object* v_cls_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_inheritedTraceOptions_1967_ = lean_ctor_get(v_a_1900_, 13);
v_cls_1968_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1967_, v_options_1965_, v___x_1969_);
if (v___x_1970_ == 0)
{
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1893_);
v___x_1972_ = l_Lean_indentExpr(v_e_1893_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1968_, v___x_1973_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_dec_ref(v___x_1974_);
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
v___jp_1903_:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_etaExpand(v_e_1893_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1890_, v_fixedPrefixSize_1891_, v_F_1892_, v_a_1913_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1914_;
}
else
{
lean_dec_ref(v_F_1892_);
lean_dec(v_fixedPrefixSize_1891_);
lean_dec(v_recFnName_1890_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1983_, lean_object* v_fixedPrefixSize_1984_, lean_object* v_F_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 5)
{
lean_object* v_fn_1998_; lean_object* v_arg_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_fn_1998_ = lean_ctor_get(v_x_1986_, 0);
lean_inc_ref(v_fn_1998_);
v_arg_1999_ = lean_ctor_get(v_x_1986_, 1);
lean_inc_ref(v_arg_1999_);
lean_dec_ref(v_x_1986_);
v___x_2000_ = lean_array_set(v_x_1987_, v_x_1988_, v_arg_1999_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_sub(v_x_1988_, v___x_2001_);
lean_dec(v_x_1988_);
v_x_1986_ = v_fn_1998_;
v_x_1987_ = v___x_2000_;
v_x_1988_ = v___x_2002_;
goto _start;
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_x_1988_);
lean_inc_ref(v_F_1985_);
lean_inc(v_fixedPrefixSize_1984_);
lean_inc(v_recFnName_1983_);
v___x_2004_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1983_, v_fixedPrefixSize_1984_, v_F_1985_, v_x_1986_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v_sz_2006_ = lean_array_size(v_x_1987_);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1983_, v_fixedPrefixSize_1984_, v_F_1985_, v_sz_2006_, v___x_2007_, v_x_1987_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = l_Lean_mkAppN(v_a_2005_, v_a_2009_);
lean_dec(v_a_2009_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2013_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_a_2005_);
v_a_2018_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2008_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2008_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_F_1985_);
lean_dec(v_fixedPrefixSize_1984_);
lean_dec(v_recFnName_1983_);
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2026_, lean_object* v_fixedPrefixSize_2027_, lean_object* v_F_2028_, lean_object* v_e_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
uint8_t v___x_2039_; 
v___x_2039_ = l_Lean_Expr_isAppOf(v_e_2029_, v_recFnName_2026_);
if (v___x_2039_ == 0)
{
lean_object* v_dummy_2040_; lean_object* v_nargs_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_dummy_2040_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2041_ = l_Lean_Expr_getAppNumArgs(v_e_2029_);
lean_inc(v_nargs_2041_);
v___x_2042_ = lean_mk_array(v_nargs_2041_, v_dummy_2040_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_sub(v_nargs_2041_, v___x_2043_);
lean_dec(v_nargs_2041_);
v___x_2045_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2026_, v_fixedPrefixSize_2027_, v_F_2028_, v_e_2029_, v___x_2042_, v___x_2044_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2026_, v_fixedPrefixSize_2027_, v_F_2028_, v_e_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
return v___x_2046_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2053_, lean_object* v_b_2054_, lean_object* v_recFnName_2055_, lean_object* v_fixedPrefixSize_2056_, uint8_t v___x_2057_, lean_object* v___x_2058_, lean_object* v_a_2059_, lean_object* v_e_2060_, lean_object* v_xs_2061_, lean_object* v_altBody_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_array_get_size(v_xs_2061_);
v___x_2080_ = lean_nat_dec_eq(v___x_2079_, v___x_2058_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_altBody_2062_);
lean_dec(v_fixedPrefixSize_2056_);
lean_dec(v_recFnName_2055_);
v___x_2081_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2082_ = l_Lean_indentExpr(v_a_2059_);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_indentExpr(v_e_2060_);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2087_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_dec_ref(v_e_2060_);
lean_dec_ref(v_a_2059_);
goto v___jp_2072_;
}
v___jp_2072_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_array_get_borrowed(v___x_2053_, v_xs_2061_, v_b_2054_);
lean_inc(v___x_2073_);
v___x_2074_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2055_, v_fixedPrefixSize_2056_, v___x_2073_, v_altBody_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = 0;
v___x_2077_ = 1;
v___x_2078_ = l_Lean_Meta_mkLambdaFVars(v_xs_2061_, v_a_2075_, v___x_2076_, v___x_2057_, v___x_2076_, v___x_2057_, v___x_2077_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2078_;
}
else
{
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2097_ = _args[0];
lean_object* v_b_2098_ = _args[1];
lean_object* v_recFnName_2099_ = _args[2];
lean_object* v_fixedPrefixSize_2100_ = _args[3];
lean_object* v___x_2101_ = _args[4];
lean_object* v___x_2102_ = _args[5];
lean_object* v_a_2103_ = _args[6];
lean_object* v_e_2104_ = _args[7];
lean_object* v_xs_2105_ = _args[8];
lean_object* v_altBody_2106_ = _args[9];
lean_object* v___y_2107_ = _args[10];
lean_object* v___y_2108_ = _args[11];
lean_object* v___y_2109_ = _args[12];
lean_object* v___y_2110_ = _args[13];
lean_object* v___y_2111_ = _args[14];
lean_object* v___y_2112_ = _args[15];
lean_object* v___y_2113_ = _args[16];
lean_object* v___y_2114_ = _args[17];
lean_object* v___y_2115_ = _args[18];
_start:
{
uint8_t v___x_67174__boxed_2116_; lean_object* v_res_2117_; 
v___x_67174__boxed_2116_ = lean_unbox(v___x_2101_);
v_res_2117_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2097_, v_b_2098_, v_recFnName_2099_, v_fixedPrefixSize_2100_, v___x_67174__boxed_2116_, v___x_2102_, v_a_2103_, v_e_2104_, v_xs_2105_, v_altBody_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v_xs_2105_);
lean_dec(v___x_2102_);
lean_dec(v_b_2098_);
lean_dec_ref(v___x_2097_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2118_, lean_object* v_fixedPrefixSize_2119_, lean_object* v_e_2120_, lean_object* v_as_2121_, lean_object* v_bs_2122_, lean_object* v_i_2123_, lean_object* v_cs_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_array_get_size(v_as_2121_);
v___x_2135_ = lean_nat_dec_lt(v_i_2123_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_i_2123_);
lean_dec_ref(v_e_2120_);
lean_dec(v_fixedPrefixSize_2119_);
lean_dec(v_recFnName_2118_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_cs_2124_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_array_get_size(v_bs_2122_);
v___x_2138_ = lean_nat_dec_lt(v_i_2123_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_dec(v_i_2123_);
lean_dec_ref(v_e_2120_);
lean_dec(v_fixedPrefixSize_2119_);
lean_dec(v_recFnName_2118_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_cs_2124_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v_a_2141_; lean_object* v_b_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2140_ = l_Lean_instInhabitedExpr;
v_a_2141_ = lean_array_fget_borrowed(v_as_2121_, v_i_2123_);
v_b_2142_ = lean_array_fget_borrowed(v_bs_2122_, v_i_2123_);
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_b_2142_, v___x_2143_);
v___x_2145_ = lean_box(v___x_2138_);
lean_inc_ref(v_e_2120_);
lean_inc_n(v_a_2141_, 2);
lean_inc(v___x_2144_);
lean_inc(v_fixedPrefixSize_2119_);
lean_inc(v_recFnName_2118_);
lean_inc(v_b_2142_);
v___f_2146_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2146_, 0, v___x_2140_);
lean_closure_set(v___f_2146_, 1, v_b_2142_);
lean_closure_set(v___f_2146_, 2, v_recFnName_2118_);
lean_closure_set(v___f_2146_, 3, v_fixedPrefixSize_2119_);
lean_closure_set(v___f_2146_, 4, v___x_2145_);
lean_closure_set(v___f_2146_, 5, v___x_2144_);
lean_closure_set(v___f_2146_, 6, v_a_2141_);
lean_closure_set(v___f_2146_, 7, v_e_2120_);
v___x_2147_ = 0;
v___x_2148_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2141_, v___x_2144_, v___f_2146_, v___x_2147_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = lean_nat_add(v_i_2123_, v___x_2143_);
lean_dec(v_i_2123_);
v___x_2151_ = lean_array_push(v_cs_2124_, v_a_2149_);
v_i_2123_ = v___x_2150_;
v_cs_2124_ = v___x_2151_;
goto _start;
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_cs_2124_);
lean_dec(v_i_2123_);
lean_dec_ref(v_e_2120_);
lean_dec(v_fixedPrefixSize_2119_);
lean_dec(v_recFnName_2118_);
v_a_2153_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2148_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2148_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2161_, lean_object* v_fixedPrefixSize_2162_, lean_object* v_F_2163_, lean_object* v_e_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
switch(lean_obj_tag(v_e_2164_))
{
case 6:
{
lean_object* v_binderName_2174_; lean_object* v_binderType_2175_; lean_object* v_body_2176_; uint8_t v_binderInfo_2177_; lean_object* v___x_2178_; 
v_binderName_2174_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_binderName_2174_);
v_binderType_2175_ = lean_ctor_get(v_e_2164_, 1);
lean_inc_ref(v_binderType_2175_);
v_body_2176_ = lean_ctor_get(v_e_2164_, 2);
lean_inc_ref(v_body_2176_);
v_binderInfo_2177_ = lean_ctor_get_uint8(v_e_2164_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2164_);
lean_inc_ref(v_F_2163_);
lean_inc(v_fixedPrefixSize_2162_);
lean_inc(v_recFnName_2161_);
v___x_2178_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_binderType_2175_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___f_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
v___f_2180_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2180_, 0, v_body_2176_);
lean_closure_set(v___f_2180_, 1, v_recFnName_2161_);
lean_closure_set(v___f_2180_, 2, v_fixedPrefixSize_2162_);
lean_closure_set(v___f_2180_, 3, v_F_2163_);
v___x_2181_ = 0;
v___x_2182_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2174_, v_binderInfo_2177_, v_a_2179_, v___f_2180_, v___x_2181_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2182_;
}
else
{
lean_dec_ref(v_body_2176_);
lean_dec(v_binderName_2174_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
return v___x_2178_;
}
}
case 7:
{
lean_object* v_binderName_2183_; lean_object* v_binderType_2184_; lean_object* v_body_2185_; uint8_t v_binderInfo_2186_; lean_object* v___x_2187_; 
v_binderName_2183_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_binderName_2183_);
v_binderType_2184_ = lean_ctor_get(v_e_2164_, 1);
lean_inc_ref(v_binderType_2184_);
v_body_2185_ = lean_ctor_get(v_e_2164_, 2);
lean_inc_ref(v_body_2185_);
v_binderInfo_2186_ = lean_ctor_get_uint8(v_e_2164_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2164_);
lean_inc_ref(v_F_2163_);
lean_inc(v_fixedPrefixSize_2162_);
lean_inc(v_recFnName_2161_);
v___x_2187_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_binderType_2184_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___f_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2189_, 0, v_body_2185_);
lean_closure_set(v___f_2189_, 1, v_recFnName_2161_);
lean_closure_set(v___f_2189_, 2, v_fixedPrefixSize_2162_);
lean_closure_set(v___f_2189_, 3, v_F_2163_);
v___x_2190_ = 0;
v___x_2191_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2183_, v_binderInfo_2186_, v_a_2188_, v___f_2189_, v___x_2190_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2191_;
}
else
{
lean_dec_ref(v_body_2185_);
lean_dec(v_binderName_2183_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
return v___x_2187_;
}
}
case 8:
{
lean_object* v_declName_2192_; lean_object* v_type_2193_; lean_object* v_value_2194_; lean_object* v_body_2195_; uint8_t v_nondep_2196_; lean_object* v___x_2197_; 
v_declName_2192_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_declName_2192_);
v_type_2193_ = lean_ctor_get(v_e_2164_, 1);
lean_inc_ref(v_type_2193_);
v_value_2194_ = lean_ctor_get(v_e_2164_, 2);
lean_inc_ref(v_value_2194_);
v_body_2195_ = lean_ctor_get(v_e_2164_, 3);
lean_inc_ref(v_body_2195_);
v_nondep_2196_ = lean_ctor_get_uint8(v_e_2164_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2164_);
lean_inc_ref(v_F_2163_);
lean_inc(v_fixedPrefixSize_2162_);
lean_inc(v_recFnName_2161_);
v___x_2197_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_type_2193_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
lean_inc_ref(v_F_2163_);
lean_inc(v_fixedPrefixSize_2162_);
lean_inc(v_recFnName_2161_);
v___x_2199_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_value_2194_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___f_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2201_, 0, v_body_2195_);
lean_closure_set(v___f_2201_, 1, v_recFnName_2161_);
lean_closure_set(v___f_2201_, 2, v_fixedPrefixSize_2162_);
lean_closure_set(v___f_2201_, 3, v_F_2163_);
v___x_2202_ = 0;
v___x_2203_ = 0;
v___x_2204_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2192_, v_a_2198_, v_a_2200_, v___f_2201_, v_nondep_2196_, v___x_2202_, v___x_2203_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2204_;
}
else
{
lean_dec(v_a_2198_);
lean_dec_ref(v_body_2195_);
lean_dec(v_declName_2192_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
return v___x_2199_;
}
}
else
{
lean_dec_ref(v_body_2195_);
lean_dec_ref(v_value_2194_);
lean_dec(v_declName_2192_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
return v___x_2197_;
}
}
case 10:
{
lean_object* v_data_2205_; lean_object* v_expr_2206_; lean_object* v___x_2207_; 
v_data_2205_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_data_2205_);
v_expr_2206_ = lean_ctor_get(v_e_2164_, 1);
lean_inc_ref(v_expr_2206_);
v___x_2207_ = l_Lean_getRecAppSyntax_x3f(v_e_2164_);
lean_dec_ref(v_e_2164_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v_val_2208_; lean_object* v_fileName_2209_; lean_object* v_fileMap_2210_; lean_object* v_options_2211_; lean_object* v_currRecDepth_2212_; lean_object* v_maxRecDepth_2213_; lean_object* v_ref_2214_; lean_object* v_currNamespace_2215_; lean_object* v_openDecls_2216_; lean_object* v_initHeartbeats_2217_; lean_object* v_maxHeartbeats_2218_; lean_object* v_quotContext_2219_; lean_object* v_currMacroScope_2220_; uint8_t v_diag_2221_; lean_object* v_cancelTk_x3f_2222_; uint8_t v_suppressElabErrors_2223_; lean_object* v_inheritedTraceOptions_2224_; lean_object* v_ref_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v_data_2205_);
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref(v___x_2207_);
v_fileName_2209_ = lean_ctor_get(v_a_2171_, 0);
v_fileMap_2210_ = lean_ctor_get(v_a_2171_, 1);
v_options_2211_ = lean_ctor_get(v_a_2171_, 2);
v_currRecDepth_2212_ = lean_ctor_get(v_a_2171_, 3);
v_maxRecDepth_2213_ = lean_ctor_get(v_a_2171_, 4);
v_ref_2214_ = lean_ctor_get(v_a_2171_, 5);
v_currNamespace_2215_ = lean_ctor_get(v_a_2171_, 6);
v_openDecls_2216_ = lean_ctor_get(v_a_2171_, 7);
v_initHeartbeats_2217_ = lean_ctor_get(v_a_2171_, 8);
v_maxHeartbeats_2218_ = lean_ctor_get(v_a_2171_, 9);
v_quotContext_2219_ = lean_ctor_get(v_a_2171_, 10);
v_currMacroScope_2220_ = lean_ctor_get(v_a_2171_, 11);
v_diag_2221_ = lean_ctor_get_uint8(v_a_2171_, sizeof(void*)*14);
v_cancelTk_x3f_2222_ = lean_ctor_get(v_a_2171_, 12);
v_suppressElabErrors_2223_ = lean_ctor_get_uint8(v_a_2171_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2224_ = lean_ctor_get(v_a_2171_, 13);
v_ref_2225_ = l_Lean_replaceRef(v_val_2208_, v_ref_2214_);
lean_dec(v_val_2208_);
lean_inc_ref(v_inheritedTraceOptions_2224_);
lean_inc(v_cancelTk_x3f_2222_);
lean_inc(v_currMacroScope_2220_);
lean_inc(v_quotContext_2219_);
lean_inc(v_maxHeartbeats_2218_);
lean_inc(v_initHeartbeats_2217_);
lean_inc(v_openDecls_2216_);
lean_inc(v_currNamespace_2215_);
lean_inc(v_maxRecDepth_2213_);
lean_inc(v_currRecDepth_2212_);
lean_inc_ref(v_options_2211_);
lean_inc_ref(v_fileMap_2210_);
lean_inc_ref(v_fileName_2209_);
v___x_2226_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2226_, 0, v_fileName_2209_);
lean_ctor_set(v___x_2226_, 1, v_fileMap_2210_);
lean_ctor_set(v___x_2226_, 2, v_options_2211_);
lean_ctor_set(v___x_2226_, 3, v_currRecDepth_2212_);
lean_ctor_set(v___x_2226_, 4, v_maxRecDepth_2213_);
lean_ctor_set(v___x_2226_, 5, v_ref_2225_);
lean_ctor_set(v___x_2226_, 6, v_currNamespace_2215_);
lean_ctor_set(v___x_2226_, 7, v_openDecls_2216_);
lean_ctor_set(v___x_2226_, 8, v_initHeartbeats_2217_);
lean_ctor_set(v___x_2226_, 9, v_maxHeartbeats_2218_);
lean_ctor_set(v___x_2226_, 10, v_quotContext_2219_);
lean_ctor_set(v___x_2226_, 11, v_currMacroScope_2220_);
lean_ctor_set(v___x_2226_, 12, v_cancelTk_x3f_2222_);
lean_ctor_set(v___x_2226_, 13, v_inheritedTraceOptions_2224_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*14, v_diag_2221_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*14 + 1, v_suppressElabErrors_2223_);
v___x_2227_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_expr_2206_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v___x_2226_, v_a_2172_);
lean_dec_ref(v___x_2226_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; 
lean_dec(v___x_2207_);
v___x_2228_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_expr_2206_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = l_Lean_mkMData(v_data_2205_, v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_dec(v_data_2205_);
return v___x_2228_;
}
}
}
case 11:
{
lean_object* v_typeName_2238_; lean_object* v_idx_2239_; lean_object* v_struct_2240_; lean_object* v___x_2241_; 
v_typeName_2238_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_typeName_2238_);
v_idx_2239_ = lean_ctor_get(v_e_2164_, 1);
lean_inc(v_idx_2239_);
v_struct_2240_ = lean_ctor_get(v_e_2164_, 2);
lean_inc_ref(v_struct_2240_);
lean_dec_ref(v_e_2164_);
v___x_2241_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_struct_2240_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = l_Lean_mkProj(v_typeName_2238_, v_idx_2239_, v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_dec(v_idx_2239_);
lean_dec(v_typeName_2238_);
return v___x_2241_;
}
}
case 4:
{
uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_Expr_isConstOf(v_e_2164_, v_recFnName_2161_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_e_2164_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_e_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2253_;
}
}
case 5:
{
uint8_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = 1;
lean_inc_ref(v_e_2164_);
v___x_2255_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2164_, v___x_2254_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
if (lean_obj_tag(v_a_2256_) == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_e_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2257_;
}
else
{
lean_object* v_val_2258_; lean_object* v___x_2259_; 
v_val_2258_ = lean_ctor_get(v_a_2256_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v_a_2256_);
lean_inc_ref(v_F_2163_);
v___x_2259_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2258_, v_F_2163_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
if (lean_obj_tag(v_a_2260_) == 1)
{
lean_object* v_val_2261_; lean_object* v_toMatcherInfo_2262_; lean_object* v_matcherName_2263_; lean_object* v_matcherLevels_2264_; lean_object* v_params_2265_; lean_object* v_motive_2266_; lean_object* v_discrs_2267_; lean_object* v_alts_2268_; lean_object* v_remaining_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_val_2261_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref(v_a_2260_);
v_toMatcherInfo_2262_ = lean_ctor_get(v_val_2261_, 0);
lean_inc_ref(v_toMatcherInfo_2262_);
v_matcherName_2263_ = lean_ctor_get(v_val_2261_, 1);
lean_inc(v_matcherName_2263_);
v_matcherLevels_2264_ = lean_ctor_get(v_val_2261_, 2);
lean_inc_ref(v_matcherLevels_2264_);
v_params_2265_ = lean_ctor_get(v_val_2261_, 3);
lean_inc_ref(v_params_2265_);
v_motive_2266_ = lean_ctor_get(v_val_2261_, 4);
lean_inc_ref(v_motive_2266_);
v_discrs_2267_ = lean_ctor_get(v_val_2261_, 5);
lean_inc_ref(v_discrs_2267_);
v_alts_2268_ = lean_ctor_get(v_val_2261_, 6);
lean_inc_ref(v_alts_2268_);
v_remaining_2269_ = lean_ctor_get(v_val_2261_, 7);
lean_inc_ref(v_remaining_2269_);
v___x_2270_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2261_);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2162_);
lean_inc(v_recFnName_2161_);
v___x_2273_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_e_2164_, v_alts_2268_, v___x_2270_, v___x_2271_, v___x_2272_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec_ref(v___x_2270_);
lean_dec_ref(v_alts_2268_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; size_t v_sz_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v_sz_2275_ = lean_array_size(v_discrs_2267_);
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_sz_2275_, v___x_2276_, v_discrs_2267_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2287_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2287_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2287_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2282_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2282_, 0, v_toMatcherInfo_2262_);
lean_ctor_set(v___x_2282_, 1, v_matcherName_2263_);
lean_ctor_set(v___x_2282_, 2, v_matcherLevels_2264_);
lean_ctor_set(v___x_2282_, 3, v_params_2265_);
lean_ctor_set(v___x_2282_, 4, v_motive_2266_);
lean_ctor_set(v___x_2282_, 5, v_a_2278_);
lean_ctor_set(v___x_2282_, 6, v_a_2274_);
lean_ctor_set(v___x_2282_, 7, v_remaining_2269_);
v___x_2283_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2282_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2283_);
v___x_2285_ = v___x_2280_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2274_);
lean_dec_ref(v_remaining_2269_);
lean_dec_ref(v_motive_2266_);
lean_dec_ref(v_params_2265_);
lean_dec_ref(v_matcherLevels_2264_);
lean_dec(v_matcherName_2263_);
lean_dec_ref(v_toMatcherInfo_2262_);
v_a_2288_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2277_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2277_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_remaining_2269_);
lean_dec_ref(v_discrs_2267_);
lean_dec_ref(v_motive_2266_);
lean_dec_ref(v_params_2265_);
lean_dec_ref(v_matcherLevels_2264_);
lean_dec(v_matcherName_2263_);
lean_dec_ref(v_toMatcherInfo_2262_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
v_a_2296_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2273_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2273_);
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
else
{
lean_object* v___x_2304_; 
lean_dec(v_a_2260_);
v___x_2304_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2161_, v_fixedPrefixSize_2162_, v_F_2163_, v_e_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2304_;
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_e_2164_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
v_a_2305_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2259_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2259_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_e_2164_);
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
lean_dec(v_recFnName_2161_);
v_a_2313_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2255_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2255_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
default: 
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v_F_2163_);
lean_dec(v_fixedPrefixSize_2162_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
v___x_2323_ = lean_array_push(v___x_2322_, v_recFnName_2161_);
lean_inc_ref(v_e_2164_);
v___x_2324_ = l_Lean_Elab_ensureNoRecFn(v___x_2323_, v_e_2164_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2324_, 0);
lean_dec(v_unused_2332_);
v___x_2326_ = v___x_2324_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v_e_2164_);
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_e_2164_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_e_2164_);
v_a_2333_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2324_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2324_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
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
uint8_t v___x_2341_; uint64_t v___x_2342_; 
v___x_2341_ = 0;
v___x_2342_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2343_, lean_object* v_fixedPrefixSize_2344_, lean_object* v_F_2345_, lean_object* v_e_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
lean_inc_ref(v_e_2346_);
lean_inc(v_recFnName_2343_);
v___x_2356_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2343_, v_e_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2495_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2495_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2495_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2363_; 
lean_dec_ref(v_F_2345_);
lean_dec(v_fixedPrefixSize_2344_);
lean_dec(v_recFnName_2343_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v_e_2346_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_e_2346_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___x_2473_; 
lean_del_object(v___x_2359_);
v___x_2365_ = lean_st_ref_get(v_a_2348_);
v___x_2366_ = 0;
v___x_2473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2365_, v_e_2346_);
lean_dec(v___x_2365_);
if (lean_obj_tag(v___x_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v___x_2477_; 
v_val_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_val_2474_);
lean_dec_ref(v___x_2473_);
v_fst_2475_ = lean_ctor_get(v_val_2474_, 0);
lean_inc(v_fst_2475_);
v_snd_2476_ = lean_ctor_get(v_val_2474_, 1);
lean_inc(v_snd_2476_);
lean_dec(v_val_2474_);
v___x_2477_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2476_, v_a_2351_);
lean_dec(v_snd_2476_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2486_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_unbox(v_a_2478_);
lean_dec(v_a_2478_);
if (v___x_2482_ == 0)
{
lean_del_object(v___x_2480_);
lean_dec(v_fst_2475_);
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
v___y_2375_ = v_a_2354_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2484_; 
lean_dec_ref(v_e_2346_);
lean_dec_ref(v_F_2345_);
lean_dec(v_fixedPrefixSize_2344_);
lean_dec(v_recFnName_2343_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_fst_2475_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_fst_2475_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_fst_2475_);
lean_dec_ref(v_e_2346_);
lean_dec_ref(v_F_2345_);
lean_dec(v_fixedPrefixSize_2344_);
lean_dec(v_recFnName_2343_);
v_a_2487_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2477_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2477_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_dec(v___x_2473_);
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
v___y_2375_ = v_a_2354_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2376_; 
lean_inc_ref(v_e_2346_);
v___x_2376_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2343_, v_fixedPrefixSize_2344_, v_F_2345_, v_e_2346_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2464_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2464_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2464_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_options_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2383_ = lean_st_ref_take(v___y_2369_);
lean_inc(v_a_2377_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_a_2377_);
lean_ctor_set(v___x_2384_, 1, v_a_2379_);
lean_inc_ref(v_e_2346_);
v___x_2385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2383_, v_e_2346_, v___x_2384_);
v___x_2386_ = lean_st_ref_set(v___y_2369_, v___x_2385_);
v_options_2387_ = lean_ctor_get(v___y_2374_, 2);
v___x_2388_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2389_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref(v_e_2346_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_a_2377_);
v___x_2391_ = v___x_2381_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2377_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
else
{
lean_object* v___x_2393_; uint8_t v_foApprox_2394_; uint8_t v_ctxApprox_2395_; uint8_t v_quasiPatternApprox_2396_; uint8_t v_constApprox_2397_; uint8_t v_isDefEqStuckEx_2398_; uint8_t v_unificationHints_2399_; uint8_t v_proofIrrelevance_2400_; uint8_t v_assignSyntheticOpaque_2401_; uint8_t v_offsetCnstrs_2402_; uint8_t v_etaStruct_2403_; uint8_t v_univApprox_2404_; uint8_t v_iota_2405_; uint8_t v_beta_2406_; uint8_t v_proj_2407_; uint8_t v_zeta_2408_; uint8_t v_zetaDelta_2409_; uint8_t v_zetaUnused_2410_; uint8_t v_zetaHave_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2463_; 
lean_del_object(v___x_2381_);
v___x_2393_ = l_Lean_Meta_Context_config(v___y_2372_);
v_foApprox_2394_ = lean_ctor_get_uint8(v___x_2393_, 0);
v_ctxApprox_2395_ = lean_ctor_get_uint8(v___x_2393_, 1);
v_quasiPatternApprox_2396_ = lean_ctor_get_uint8(v___x_2393_, 2);
v_constApprox_2397_ = lean_ctor_get_uint8(v___x_2393_, 3);
v_isDefEqStuckEx_2398_ = lean_ctor_get_uint8(v___x_2393_, 4);
v_unificationHints_2399_ = lean_ctor_get_uint8(v___x_2393_, 5);
v_proofIrrelevance_2400_ = lean_ctor_get_uint8(v___x_2393_, 6);
v_assignSyntheticOpaque_2401_ = lean_ctor_get_uint8(v___x_2393_, 7);
v_offsetCnstrs_2402_ = lean_ctor_get_uint8(v___x_2393_, 8);
v_etaStruct_2403_ = lean_ctor_get_uint8(v___x_2393_, 10);
v_univApprox_2404_ = lean_ctor_get_uint8(v___x_2393_, 11);
v_iota_2405_ = lean_ctor_get_uint8(v___x_2393_, 12);
v_beta_2406_ = lean_ctor_get_uint8(v___x_2393_, 13);
v_proj_2407_ = lean_ctor_get_uint8(v___x_2393_, 14);
v_zeta_2408_ = lean_ctor_get_uint8(v___x_2393_, 15);
v_zetaDelta_2409_ = lean_ctor_get_uint8(v___x_2393_, 16);
v_zetaUnused_2410_ = lean_ctor_get_uint8(v___x_2393_, 17);
v_zetaHave_2411_ = lean_ctor_get_uint8(v___x_2393_, 18);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2413_ = v___x_2393_;
v_isShared_2414_ = v_isSharedCheck_2463_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v___x_2393_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2463_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
uint8_t v_trackZetaDelta_2415_; lean_object* v_zetaDeltaSet_2416_; lean_object* v_lctx_2417_; lean_object* v_localInstances_2418_; lean_object* v_defEqCtx_x3f_2419_; lean_object* v_synthPendingDepth_2420_; lean_object* v_canUnfold_x3f_2421_; uint8_t v_univApprox_2422_; uint8_t v_inTypeClassResolution_2423_; uint8_t v_cacheInferType_2424_; uint8_t v___x_2425_; lean_object* v_config_2427_; 
v_trackZetaDelta_2415_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*7);
v_zetaDeltaSet_2416_ = lean_ctor_get(v___y_2372_, 1);
v_lctx_2417_ = lean_ctor_get(v___y_2372_, 2);
v_localInstances_2418_ = lean_ctor_get(v___y_2372_, 3);
v_defEqCtx_x3f_2419_ = lean_ctor_get(v___y_2372_, 4);
v_synthPendingDepth_2420_ = lean_ctor_get(v___y_2372_, 5);
v_canUnfold_x3f_2421_ = lean_ctor_get(v___y_2372_, 6);
v_univApprox_2422_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2423_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*7 + 2);
v_cacheInferType_2424_ = lean_ctor_get_uint8(v___y_2372_, sizeof(void*)*7 + 3);
v___x_2425_ = 0;
if (v_isShared_2414_ == 0)
{
v_config_2427_ = v___x_2413_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 0, v_foApprox_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 1, v_ctxApprox_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 2, v_quasiPatternApprox_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 3, v_constApprox_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 4, v_isDefEqStuckEx_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 5, v_unificationHints_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 6, v_proofIrrelevance_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 7, v_assignSyntheticOpaque_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 8, v_offsetCnstrs_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 10, v_etaStruct_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 11, v_univApprox_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 12, v_iota_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 13, v_beta_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 14, v_proj_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 15, v_zeta_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 16, v_zetaDelta_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 17, v_zetaUnused_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2462_, 18, v_zetaHave_2411_);
v_config_2427_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
uint64_t v___x_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; lean_object* v___f_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; uint64_t v_key_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_ctor_set_uint8(v_config_2427_, 9, v___x_2425_);
v___x_2428_ = l_Lean_Meta_Context_configKey(v___y_2372_);
v___x_2429_ = 2ULL;
v___x_2430_ = lean_uint64_shift_right(v___x_2428_, v___x_2429_);
lean_inc(v_a_2377_);
v___f_2431_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2431_, 0, v_a_2377_);
lean_closure_set(v___f_2431_, 1, v_e_2346_);
v___x_2432_ = lean_uint64_shift_left(v___x_2430_, v___x_2429_);
v___x_2433_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2434_ = lean_uint64_lor(v___x_2432_, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2435_, 0, v_config_2427_);
lean_ctor_set_uint64(v___x_2435_, sizeof(void*)*1, v_key_2434_);
lean_inc(v_canUnfold_x3f_2421_);
lean_inc(v_synthPendingDepth_2420_);
lean_inc(v_defEqCtx_x3f_2419_);
lean_inc_ref(v_localInstances_2418_);
lean_inc_ref(v_lctx_2417_);
lean_inc(v_zetaDeltaSet_2416_);
v___x_2436_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_zetaDeltaSet_2416_);
lean_ctor_set(v___x_2436_, 2, v_lctx_2417_);
lean_ctor_set(v___x_2436_, 3, v_localInstances_2418_);
lean_ctor_set(v___x_2436_, 4, v_defEqCtx_x3f_2419_);
lean_ctor_set(v___x_2436_, 5, v_synthPendingDepth_2420_);
lean_ctor_set(v___x_2436_, 6, v_canUnfold_x3f_2421_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*7, v_trackZetaDelta_2415_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*7 + 1, v_univApprox_2422_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2423_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*7 + 3, v_cacheInferType_2424_);
v___x_2437_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2431_, v___x_2366_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___x_2436_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec_ref(v___x_2436_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2445_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2377_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2377_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2453_);
v___x_2447_ = v___x_2437_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_dec(v___x_2437_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
lean_ctor_set_tag(v___x_2447_, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2377_);
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2377_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2377_);
v_a_2454_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2437_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2437_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
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
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2377_);
lean_dec_ref(v_e_2346_);
v_a_2465_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2378_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2378_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_dec_ref(v_e_2346_);
return v___x_2376_;
}
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_e_2346_);
lean_dec_ref(v_F_2345_);
lean_dec(v_fixedPrefixSize_2344_);
lean_dec(v_recFnName_2343_);
v_a_2496_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2356_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2356_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2504_, lean_object* v_recFnName_2505_, lean_object* v_fixedPrefixSize_2506_, lean_object* v_F_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_expr_instantiate1(v_body_2504_, v_x_2508_);
v___x_2519_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2505_, v_fixedPrefixSize_2506_, v_F_2507_, v___x_2518_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2520_, lean_object* v_fixedPrefixSize_2521_, lean_object* v_F_2522_, lean_object* v_e_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2520_, v_fixedPrefixSize_2521_, v_F_2522_, v_e_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec(v_a_2524_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2534_, lean_object* v_fixedPrefixSize_2535_, lean_object* v_F_2536_, lean_object* v_sz_2537_, lean_object* v_i_2538_, lean_object* v_bs_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_sz_boxed_2549_; size_t v_i_boxed_2550_; lean_object* v_res_2551_; 
v_sz_boxed_2549_ = lean_unbox_usize(v_sz_2537_);
lean_dec(v_sz_2537_);
v_i_boxed_2550_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2534_, v_fixedPrefixSize_2535_, v_F_2536_, v_sz_boxed_2549_, v_i_boxed_2550_, v_bs_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec(v___y_2540_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2552_, lean_object* v_fixedPrefixSize_2553_, lean_object* v_F_2554_, lean_object* v_x_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2552_, v_fixedPrefixSize_2553_, v_F_2554_, v_x_2555_, v_x_2556_, v_x_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec(v___y_2558_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2568_, lean_object* v_fixedPrefixSize_2569_, lean_object* v_e_2570_, lean_object* v_as_2571_, lean_object* v_bs_2572_, lean_object* v_i_2573_, lean_object* v_cs_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2568_, v_fixedPrefixSize_2569_, v_e_2570_, v_as_2571_, v_bs_2572_, v_i_2573_, v_cs_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v_bs_2572_);
lean_dec_ref(v_as_2571_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2585_, lean_object* v_fixedPrefixSize_2586_, lean_object* v_F_2587_, lean_object* v_e_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2585_, v_fixedPrefixSize_2586_, v_F_2587_, v_e_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec(v_a_2589_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2599_, lean_object* v_fixedPrefixSize_2600_, lean_object* v_F_2601_, lean_object* v_e_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2599_, v_fixedPrefixSize_2600_, v_F_2601_, v_e_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec(v_a_2603_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2613_, lean_object* v_fixedPrefixSize_2614_, lean_object* v_F_2615_, lean_object* v_e_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2613_, v_fixedPrefixSize_2614_, v_F_2615_, v_e_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec(v_a_2617_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2627_, lean_object* v_k_2628_, uint8_t v_allowLevelAssignments_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2628_, v_allowLevelAssignments_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_k_2641_, lean_object* v_allowLevelAssignments_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2652_; lean_object* v_res_2653_; 
v_allowLevelAssignments_boxed_2652_ = lean_unbox(v_allowLevelAssignments_2642_);
v_res_2653_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2640_, v_k_2641_, v_allowLevelAssignments_boxed_2652_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec(v___y_2643_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2654_, lean_object* v_name_2655_, uint8_t v_bi_2656_, lean_object* v_type_2657_, lean_object* v_k_2658_, uint8_t v_kind_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2655_, v_bi_2656_, v_type_2657_, v_k_2658_, v_kind_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2670_, lean_object* v_name_2671_, lean_object* v_bi_2672_, lean_object* v_type_2673_, lean_object* v_k_2674_, lean_object* v_kind_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_bi_boxed_2685_; uint8_t v_kind_boxed_2686_; lean_object* v_res_2687_; 
v_bi_boxed_2685_ = lean_unbox(v_bi_2672_);
v_kind_boxed_2686_ = lean_unbox(v_kind_2675_);
v_res_2687_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2670_, v_name_2671_, v_bi_boxed_2685_, v_type_2673_, v_k_2674_, v_kind_boxed_2686_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2676_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2688_, lean_object* v_e_2689_, lean_object* v_maxFVars_2690_, lean_object* v_k_2691_, uint8_t v_cleanupAnnotations_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2689_, v_maxFVars_2690_, v_k_2691_, v_cleanupAnnotations_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_e_2704_, lean_object* v_maxFVars_2705_, lean_object* v_k_2706_, lean_object* v_cleanupAnnotations_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2717_; lean_object* v_res_2718_; 
v_cleanupAnnotations_boxed_2717_ = lean_unbox(v_cleanupAnnotations_2707_);
v_res_2718_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2703_, v_e_2704_, v_maxFVars_2705_, v_k_2706_, v_cleanupAnnotations_boxed_2717_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2719_, lean_object* v_R_2720_, lean_object* v_a_2721_, lean_object* v_b_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2721_, v_b_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2724_, lean_object* v_msg_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2724_, v_msg_2725_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2736_, lean_object* v_msg_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2736_, v_msg_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2748_, lean_object* v_m_2749_, lean_object* v_a_2750_, lean_object* v_b_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2749_, v_a_2750_, v_b_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2754_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_msg_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2765_, v_msg_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec(v___y_2767_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2777_, lean_object* v_m_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2778_, v_a_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2781_, lean_object* v_m_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2781_, v_m_2782_, v_a_2783_);
lean_dec_ref(v_a_2783_);
lean_dec_ref(v_m_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2785_, lean_object* v_name_2786_, lean_object* v_type_2787_, lean_object* v_val_2788_, lean_object* v_k_2789_, uint8_t v_nondep_2790_, uint8_t v_kind_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2786_, v_type_2787_, v_val_2788_, v_k_2789_, v_nondep_2790_, v_kind_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2802_, lean_object* v_name_2803_, lean_object* v_type_2804_, lean_object* v_val_2805_, lean_object* v_k_2806_, lean_object* v_nondep_2807_, lean_object* v_kind_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
uint8_t v_nondep_boxed_2818_; uint8_t v_kind_boxed_2819_; lean_object* v_res_2820_; 
v_nondep_boxed_2818_ = lean_unbox(v_nondep_2807_);
v_kind_boxed_2819_ = lean_unbox(v_kind_2808_);
v_res_2820_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2802_, v_name_2803_, v_type_2804_, v_val_2805_, v_k_2806_, v_nondep_boxed_2818_, v_kind_boxed_2819_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2821_, v___y_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2843_, lean_object* v_a_2844_, lean_object* v_x_2845_){
_start:
{
uint8_t v___x_2846_; 
v___x_2846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2844_, v_x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2847_, lean_object* v_a_2848_, lean_object* v_x_2849_){
_start:
{
uint8_t v_res_2850_; lean_object* v_r_2851_; 
v_res_2850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2847_, v_a_2848_, v_x_2849_);
lean_dec(v_x_2849_);
lean_dec_ref(v_a_2848_);
v_r_2851_ = lean_box(v_res_2850_);
return v_r_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2852_, lean_object* v_data_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2855_, lean_object* v_a_2856_, lean_object* v_b_2857_, lean_object* v_x_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2856_, v_b_2857_, v_x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2860_, lean_object* v_a_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2861_, v_x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2864_, lean_object* v_a_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2864_, v_a_2865_, v_x_2866_);
lean_dec(v_x_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2868_, lean_object* v_i_2869_, lean_object* v_source_2870_, lean_object* v_target_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2869_, v_source_2870_, v_target_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2873_, lean_object* v_constName_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2885_, lean_object* v_constName_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2885_, v_constName_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2898_, v_x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2901_, lean_object* v_ref_2902_, lean_object* v_constName_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2902_, v_constName_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_ref_2915_, lean_object* v_constName_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2914_, v_ref_2915_, v_constName_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec(v_ref_2915_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2927_, lean_object* v_ref_2928_, lean_object* v_msg_2929_, lean_object* v_declHint_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2928_, v_msg_2929_, v_declHint_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2941_, lean_object* v_ref_2942_, lean_object* v_msg_2943_, lean_object* v_declHint_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2941_, v_ref_2942_, v_msg_2943_, v_declHint_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v_ref_2942_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2955_, lean_object* v_declHint_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2955_, v_declHint_2956_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2967_, lean_object* v_declHint_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2967_, v_declHint_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec(v___y_2969_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2979_, lean_object* v_ref_2980_, lean_object* v_msg_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2980_, v_msg_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_ref_2993_, lean_object* v_msg_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2992_, v_ref_2993_, v_msg_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec(v_ref_2993_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_ref_3012_; lean_object* v___x_3013_; lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3059_; 
v_ref_3012_ = lean_ctor_get(v___y_3009_, 5);
v___x_3013_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3059_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3059_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v_traceState_3019_; lean_object* v_env_3020_; lean_object* v_nextMacroScope_3021_; lean_object* v_ngen_3022_; lean_object* v_auxDeclNGen_3023_; lean_object* v_cache_3024_; lean_object* v_messages_3025_; lean_object* v_infoState_3026_; lean_object* v_snapshotTasks_3027_; lean_object* v_newDecls_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3058_; 
v___x_3018_ = lean_st_ref_take(v___y_3010_);
v_traceState_3019_ = lean_ctor_get(v___x_3018_, 4);
v_env_3020_ = lean_ctor_get(v___x_3018_, 0);
v_nextMacroScope_3021_ = lean_ctor_get(v___x_3018_, 1);
v_ngen_3022_ = lean_ctor_get(v___x_3018_, 2);
v_auxDeclNGen_3023_ = lean_ctor_get(v___x_3018_, 3);
v_cache_3024_ = lean_ctor_get(v___x_3018_, 5);
v_messages_3025_ = lean_ctor_get(v___x_3018_, 6);
v_infoState_3026_ = lean_ctor_get(v___x_3018_, 7);
v_snapshotTasks_3027_ = lean_ctor_get(v___x_3018_, 8);
v_newDecls_3028_ = lean_ctor_get(v___x_3018_, 9);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3030_ = v___x_3018_;
v_isShared_3031_ = v_isSharedCheck_3058_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_newDecls_3028_);
lean_inc(v_snapshotTasks_3027_);
lean_inc(v_infoState_3026_);
lean_inc(v_messages_3025_);
lean_inc(v_cache_3024_);
lean_inc(v_traceState_3019_);
lean_inc(v_auxDeclNGen_3023_);
lean_inc(v_ngen_3022_);
lean_inc(v_nextMacroScope_3021_);
lean_inc(v_env_3020_);
lean_dec(v___x_3018_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3058_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
uint64_t v_tid_3032_; lean_object* v_traces_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3057_; 
v_tid_3032_ = lean_ctor_get_uint64(v_traceState_3019_, sizeof(void*)*1);
v_traces_3033_ = lean_ctor_get(v_traceState_3019_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_traceState_3019_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3035_ = v_traceState_3019_;
v_isShared_3036_ = v_isSharedCheck_3057_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_traces_3033_);
lean_dec(v_traceState_3019_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3057_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; double v___x_3038_; uint8_t v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3039_ = 0;
v___x_3040_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3041_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3041_, 0, v_cls_3005_);
lean_ctor_set(v___x_3041_, 1, v___x_3037_);
lean_ctor_set(v___x_3041_, 2, v___x_3040_);
lean_ctor_set_float(v___x_3041_, sizeof(void*)*3, v___x_3038_);
lean_ctor_set_float(v___x_3041_, sizeof(void*)*3 + 8, v___x_3038_);
lean_ctor_set_uint8(v___x_3041_, sizeof(void*)*3 + 16, v___x_3039_);
v___x_3042_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3043_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v_a_3014_);
lean_ctor_set(v___x_3043_, 2, v___x_3042_);
lean_inc(v_ref_3012_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v_ref_3012_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_PersistentArray_push___redArg(v_traces_3033_, v___x_3044_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3045_);
v___x_3047_ = v___x_3035_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3045_);
lean_ctor_set_uint64(v_reuseFailAlloc_3056_, sizeof(void*)*1, v_tid_3032_);
v___x_3047_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3049_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 4, v___x_3047_);
v___x_3049_ = v___x_3030_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_env_3020_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_nextMacroScope_3021_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_ngen_3022_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_auxDeclNGen_3023_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3055_, 5, v_cache_3024_);
lean_ctor_set(v_reuseFailAlloc_3055_, 6, v_messages_3025_);
lean_ctor_set(v_reuseFailAlloc_3055_, 7, v_infoState_3026_);
lean_ctor_set(v_reuseFailAlloc_3055_, 8, v_snapshotTasks_3027_);
lean_ctor_set(v_reuseFailAlloc_3055_, 9, v_newDecls_3028_);
v___x_3049_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3050_ = lean_st_ref_set(v___y_3010_, v___x_3049_);
v___x_3051_ = lean_box(0);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3051_);
v___x_3053_ = v___x_3016_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3060_, lean_object* v_msg_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3060_, v_msg_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
return v_res_3067_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_unsigned_to_nat(16u);
v___x_3070_ = lean_mk_array(v___x_3069_, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3083_, lean_object* v_fixedPrefixSize_3084_, lean_object* v_F_3085_, lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v_options_3115_; uint8_t v_hasTrace_3116_; 
v_options_3115_ = lean_ctor_get(v_a_3091_, 2);
v_hasTrace_3116_ = lean_ctor_get_uint8(v_options_3115_, sizeof(void*)*1);
if (v_hasTrace_3116_ == 0)
{
v___y_3095_ = v_a_3087_;
v___y_3096_ = v_a_3088_;
v___y_3097_ = v_a_3089_;
v___y_3098_ = v_a_3090_;
v___y_3099_ = v_a_3091_;
v___y_3100_ = v_a_3092_;
goto v___jp_3094_;
}
else
{
lean_object* v_inheritedTraceOptions_3117_; lean_object* v_cls_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v_options_3125_; lean_object* v_inheritedTraceOptions_3126_; lean_object* v___y_3127_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_inheritedTraceOptions_3117_ = lean_ctor_get(v_a_3091_, 13);
v_cls_3118_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3148_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3117_, v_options_3115_, v___x_3148_);
if (v___x_3149_ == 0)
{
v___y_3120_ = v_a_3087_;
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v_options_3125_ = v_options_3115_;
v_inheritedTraceOptions_3126_ = v_inheritedTraceOptions_3117_;
v___y_3127_ = v_a_3092_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3150_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3086_);
v___x_3151_ = l_Lean_indentExpr(v_e_3086_);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3118_, v___x_3152_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_dec_ref(v___x_3153_);
v___y_3120_ = v_a_3087_;
v___y_3121_ = v_a_3088_;
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v_options_3125_ = v_options_3115_;
v_inheritedTraceOptions_3126_ = v_inheritedTraceOptions_3117_;
v___y_3127_ = v_a_3092_;
goto v___jp_3119_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v_e_3086_);
lean_dec_ref(v_F_3085_);
lean_dec(v_fixedPrefixSize_3084_);
lean_dec(v_recFnName_3083_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
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
v___jp_3119_:
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3126_, v_options_3125_, v___x_3128_);
if (v___x_3129_ == 0)
{
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3127_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3130_; 
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc_ref(v_F_3085_);
v___x_3130_ = lean_infer_type(v_F_3085_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3127_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
v___x_3132_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3085_);
v___x_3133_ = l_Lean_MessageData_ofExpr(v_F_3085_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_indentExpr(v_a_3131_);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3118_, v___x_3138_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3127_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_dec_ref(v___x_3139_);
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___y_3121_;
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3127_;
goto v___jp_3094_;
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_e_3086_);
lean_dec_ref(v_F_3085_);
lean_dec(v_fixedPrefixSize_3084_);
lean_dec(v_recFnName_3083_);
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_dec_ref(v_e_3086_);
lean_dec_ref(v_F_3085_);
lean_dec(v_fixedPrefixSize_3084_);
lean_dec(v_recFnName_3083_);
return v___x_3130_;
}
}
}
}
v___jp_3094_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3102_ = lean_st_mk_ref(v___x_3101_);
v___x_3103_ = lean_st_mk_ref(v___x_3101_);
v___x_3104_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3083_, v_fixedPrefixSize_3084_, v_F_3085_, v_e_3086_, v___x_3103_, v___x_3102_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3114_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3109_ = lean_st_ref_get(v___x_3103_);
lean_dec(v___x_3103_);
lean_dec(v___x_3109_);
v___x_3110_ = lean_st_ref_get(v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v___x_3110_);
if (v_isShared_3108_ == 0)
{
v___x_3112_ = v___x_3107_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3105_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_dec(v___x_3103_);
lean_dec(v___x_3102_);
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3162_, lean_object* v_fixedPrefixSize_3163_, lean_object* v_F_3164_, lean_object* v_e_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3162_, v_fixedPrefixSize_3163_, v_F_3164_, v_e_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3174_, lean_object* v_msg_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3174_, v_msg_3175_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3184_, lean_object* v_msg_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3184_, v_msg_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v_b_3197_, lean_object* v_c_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
v___x_3204_ = lean_apply_9(v_k_3194_, v_b_3197_, v_c_3198_, v___y_3195_, v___y_3196_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, lean_box(0));
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v_b_3208_, lean_object* v_c_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3205_, v___y_3206_, v___y_3207_, v_b_3208_, v_c_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3216_, lean_object* v_k_3217_, uint8_t v_cleanupAnnotations_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___f_3226_; uint8_t v___x_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3226_, 0, v_k_3217_);
lean_closure_set(v___f_3226_, 1, v___y_3219_);
lean_closure_set(v___f_3226_, 2, v___y_3220_);
v___x_3227_ = 1;
v___x_3228_ = 0;
v___x_3229_ = lean_box(0);
v___x_3230_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3216_, v___x_3227_, v___x_3228_, v___x_3227_, v___x_3228_, v___x_3229_, v___f_3226_, v_cleanupAnnotations_3218_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3230_) == 0)
{
return v___x_3230_;
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3239_, lean_object* v_k_3240_, lean_object* v_cleanupAnnotations_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3249_; lean_object* v_res_3250_; 
v_cleanupAnnotations_boxed_3249_ = lean_unbox(v_cleanupAnnotations_3241_);
v_res_3250_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3239_, v_k_3240_, v_cleanupAnnotations_boxed_3249_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3251_, lean_object* v_e_3252_, lean_object* v_k_3253_, uint8_t v_cleanupAnnotations_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3252_, v_k_3253_, v_cleanupAnnotations_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3263_, lean_object* v_e_3264_, lean_object* v_k_3265_, lean_object* v_cleanupAnnotations_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3274_; lean_object* v_res_3275_; 
v_cleanupAnnotations_boxed_3274_ = lean_unbox(v_cleanupAnnotations_3266_);
v_res_3275_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3263_, v_e_3264_, v_k_3265_, v_cleanupAnnotations_boxed_3274_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3276_, lean_object* v_maxFVars_3277_, lean_object* v_k_3278_, uint8_t v_cleanupAnnotations_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___f_3287_; uint8_t v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3287_, 0, v_k_3278_);
lean_closure_set(v___f_3287_, 1, v___y_3280_);
lean_closure_set(v___f_3287_, 2, v___y_3281_);
v___x_3288_ = 1;
v___x_3289_ = 0;
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_maxFVars_3277_);
v___x_3291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3276_, v___x_3288_, v___x_3289_, v___x_3288_, v___x_3289_, v___x_3290_, v___f_3287_, v_cleanupAnnotations_3279_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec_ref(v___x_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3300_, lean_object* v_maxFVars_3301_, lean_object* v_k_3302_, lean_object* v_cleanupAnnotations_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3311_; lean_object* v_res_3312_; 
v_cleanupAnnotations_boxed_3311_ = lean_unbox(v_cleanupAnnotations_3303_);
v_res_3312_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3300_, v_maxFVars_3301_, v_k_3302_, v_cleanupAnnotations_boxed_3311_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3313_, lean_object* v_e_3314_, lean_object* v_maxFVars_3315_, lean_object* v_k_3316_, uint8_t v_cleanupAnnotations_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3314_, v_maxFVars_3315_, v_k_3316_, v_cleanupAnnotations_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3326_, lean_object* v_e_3327_, lean_object* v_maxFVars_3328_, lean_object* v_k_3329_, lean_object* v_cleanupAnnotations_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3338_; lean_object* v_res_3339_; 
v_cleanupAnnotations_boxed_3338_ = lean_unbox(v_cleanupAnnotations_3330_);
v_res_3339_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3326_, v_e_3327_, v_maxFVars_3328_, v_k_3329_, v_cleanupAnnotations_boxed_3338_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3340_, lean_object* v___x_3341_, lean_object* v___x_3342_, lean_object* v_x_3343_, uint8_t v___x_3344_, lean_object* v_xs_3345_, lean_object* v_type_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3354_ = l_Lean_LocalDecl_type(v_a_3340_);
v___x_3355_ = lean_array_get_borrowed(v___x_3341_, v_xs_3345_, v___x_3342_);
v___x_3356_ = l_Lean_Expr_replaceFVar(v___x_3354_, v_x_3343_, v___x_3355_);
lean_dec_ref(v___x_3354_);
v___x_3357_ = l_Lean_mkArrow(v___x_3356_, v_type_3346_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; uint8_t v___x_3359_; uint8_t v___x_3360_; lean_object* v___x_3361_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_n(v_a_3358_, 2);
lean_dec_ref(v___x_3357_);
v___x_3359_ = 0;
v___x_3360_ = 1;
v___x_3361_ = l_Lean_Meta_mkLambdaFVars(v_xs_3345_, v_a_3358_, v___x_3359_, v___x_3344_, v___x_3359_, v___x_3344_, v___x_3360_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_Meta_getLevel(v_a_3358_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_a_3362_);
lean_ctor_set(v___x_3368_, 1, v_a_3364_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_a_3362_);
v_a_3373_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3363_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3363_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_a_3358_);
v_a_3381_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3361_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3361_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v_a_3389_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3357_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3357_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3397_, lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v_x_3400_, lean_object* v___x_3401_, lean_object* v_xs_3402_, lean_object* v_type_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v___x_6703__boxed_3411_; lean_object* v_res_3412_; 
v___x_6703__boxed_3411_ = lean_unbox(v___x_3401_);
v_res_3412_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3397_, v___x_3398_, v___x_3399_, v_x_3400_, v___x_6703__boxed_3411_, v_xs_3402_, v_type_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v_xs_3402_);
lean_dec(v___x_3399_);
lean_dec_ref(v___x_3398_);
lean_dec_ref(v_a_3397_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v_b_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3419_);
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3417_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3414_);
v___x_3422_ = lean_apply_8(v_k_3413_, v_b_3416_, v___y_3414_, v___y_3415_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, lean_box(0));
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v_b_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3423_, v___y_3424_, v___y_3425_, v_b_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3433_, uint8_t v_bi_3434_, lean_object* v_type_3435_, lean_object* v_k_3436_, uint8_t v_kind_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___f_3445_; lean_object* v___x_3446_; 
lean_inc(v___y_3439_);
lean_inc_ref(v___y_3438_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3445_, 0, v_k_3436_);
lean_closure_set(v___f_3445_, 1, v___y_3438_);
lean_closure_set(v___f_3445_, 2, v___y_3439_);
v___x_3446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3433_, v_bi_3434_, v_type_3435_, v___f_3445_, v_kind_3437_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3446_) == 0)
{
return v___x_3446_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3455_, lean_object* v_bi_3456_, lean_object* v_type_3457_, lean_object* v_k_3458_, lean_object* v_kind_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
uint8_t v_bi_boxed_3467_; uint8_t v_kind_boxed_3468_; lean_object* v_res_3469_; 
v_bi_boxed_3467_ = lean_unbox(v_bi_3456_);
v_kind_boxed_3468_ = lean_unbox(v_kind_3459_);
v_res_3469_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3455_, v_bi_boxed_3467_, v_type_3457_, v_k_3458_, v_kind_boxed_3468_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3470_, lean_object* v_type_3471_, lean_object* v_k_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
uint8_t v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = 0;
v___x_3481_ = 0;
v___x_3482_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3470_, v___x_3480_, v_type_3471_, v_k_3472_, v___x_3481_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3483_, lean_object* v_type_3484_, lean_object* v_k_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3483_, v_type_3484_, v_k_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3507_, lean_object* v_F_3508_, lean_object* v_val_3509_, lean_object* v_k_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
uint8_t v___y_3519_; uint8_t v___x_3634_; 
v___x_3634_ = l_Lean_Expr_isFVar(v_x_3507_);
if (v___x_3634_ == 0)
{
v___y_3519_ = v___x_3634_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3636_ = lean_unsigned_to_nat(6u);
v___x_3637_ = l_Lean_Expr_isAppOfArity(v_val_3509_, v___x_3635_, v___x_3636_);
v___y_3519_ = v___x_3637_;
goto v___jp_3518_;
}
v___jp_3518_:
{
if (v___y_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
v___x_3520_ = lean_apply_10(v_k_3510_, v_x_3507_, v_F_3508_, v_val_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, lean_box(0));
return v___x_3520_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3521_ = lean_unsigned_to_nat(3u);
v___x_3522_ = l_Lean_Expr_getAppNumArgs(v_val_3509_);
v___x_3523_ = lean_nat_sub(v___x_3522_, v___x_3521_);
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_sub(v___x_3523_, v___x_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = l_Lean_Expr_getRevArg_x21(v_val_3509_, v___x_3525_);
v___x_3527_ = lean_expr_eqv(v___x_3526_, v_x_3507_);
lean_dec_ref(v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec(v___x_3522_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
v___x_3528_ = lean_apply_10(v_k_3510_, v_x_3507_, v_F_3508_, v_val_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, lean_box(0));
return v___x_3528_;
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3529_ = lean_unsigned_to_nat(4u);
v___x_3530_ = lean_nat_sub(v___x_3522_, v___x_3529_);
v___x_3531_ = lean_nat_sub(v___x_3530_, v___x_3524_);
lean_dec(v___x_3530_);
v___x_3532_ = l_Lean_Expr_getRevArg_x21(v_val_3509_, v___x_3531_);
v___x_3533_ = l_Lean_Expr_isLambda(v___x_3532_);
lean_dec_ref(v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_dec(v___x_3522_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
v___x_3534_ = lean_apply_10(v_k_3510_, v_x_3507_, v_F_3508_, v_val_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, lean_box(0));
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3535_ = lean_unsigned_to_nat(5u);
v___x_3536_ = lean_nat_sub(v___x_3522_, v___x_3535_);
v___x_3537_ = lean_nat_sub(v___x_3536_, v___x_3524_);
lean_dec(v___x_3536_);
v___x_3538_ = l_Lean_Expr_getRevArg_x21(v_val_3509_, v___x_3537_);
v___x_3539_ = l_Lean_Expr_isLambda(v___x_3538_);
lean_dec_ref(v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec(v___x_3522_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
v___x_3540_ = lean_apply_10(v_k_3510_, v_x_3507_, v_F_3508_, v_val_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, lean_box(0));
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = l_Lean_Expr_fvarId_x21(v_F_3508_);
v___x_3542_ = l_Lean_FVarId_getDecl___redArg(v___x_3541_, v_a_3513_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; lean_object* v_dummy_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v_args_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc_n(v_a_3543_, 2);
lean_dec_ref(v___x_3542_);
v___x_3544_ = l_Lean_instInhabitedExpr;
v_dummy_3545_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3522_);
v___x_3546_ = lean_mk_array(v___x_3522_, v_dummy_3545_);
v___x_3547_ = lean_nat_sub(v___x_3522_, v___x_3524_);
lean_dec(v___x_3522_);
v_args_3548_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3509_, v___x_3546_, v___x_3547_);
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_box(v___x_3533_);
lean_inc_ref(v_x_3507_);
v___f_3551_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3551_, 0, v_a_3543_);
lean_closure_set(v___f_3551_, 1, v___x_3544_);
lean_closure_set(v___f_3551_, 2, v___x_3549_);
lean_closure_set(v___f_3551_, 3, v_x_3507_);
lean_closure_set(v___f_3551_, 4, v___x_3550_);
v___x_3552_ = lean_unsigned_to_nat(2u);
v___x_3553_ = lean_array_get(v___x_3544_, v_args_3548_, v___x_3552_);
v___x_3554_ = 0;
v___x_3555_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3553_, v___f_3551_, v___x_3554_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3617_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v_fst_3557_ = lean_ctor_get(v_a_3556_, 0);
v_snd_3558_ = lean_ctor_get(v_a_3556_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3560_ = v_a_3556_;
v_isShared_3561_ = v_isSharedCheck_3617_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_inc(v_fst_3557_);
lean_dec(v_a_3556_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3617_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_00_u03b1_3562_; lean_object* v_00_u03b2_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v_00_u03b1_3562_ = lean_array_get(v___x_3544_, v_args_3548_, v___x_3549_);
v_00_u03b2_3563_ = lean_array_get(v___x_3544_, v_args_3548_, v___x_3524_);
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3565_ = lean_array_get(v___x_3544_, v_args_3548_, v___x_3529_);
lean_inc_ref(v_x_3507_);
lean_inc(v_a_3543_);
lean_inc_ref(v_k_3510_);
lean_inc(v_00_u03b2_3563_);
lean_inc(v_00_u03b1_3562_);
v___x_3566_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3544_, v___x_3549_, v_00_u03b1_3562_, v_00_u03b2_3563_, v___x_3521_, v_k_3510_, v___x_3552_, v___x_3554_, v___x_3533_, v_a_3543_, v_x_3507_, v___x_3524_, v___x_3564_, v___x_3565_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3569_ = lean_array_get(v___x_3544_, v_args_3548_, v___x_3535_);
lean_dec_ref(v_args_3548_);
lean_inc_ref(v_x_3507_);
lean_inc(v_00_u03b2_3563_);
lean_inc(v_00_u03b1_3562_);
v___x_3570_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3544_, v___x_3549_, v_00_u03b1_3562_, v_00_u03b2_3563_, v___x_3521_, v_k_3510_, v___x_3552_, v___x_3554_, v___x_3533_, v_a_3543_, v_x_3507_, v___x_3524_, v___x_3568_, v___x_3569_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
lean_inc(v_00_u03b1_3562_);
v___x_3572_ = l_Lean_Meta_getLevel(v_00_u03b1_3562_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
lean_inc(v_00_u03b2_3563_);
v___x_3574_ = l_Lean_Meta_getLevel(v_00_u03b2_3563_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3600_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3600_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3600_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3579_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3580_ = lean_box(0);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 1);
lean_ctor_set(v___x_3560_, 1, v___x_3580_);
lean_ctor_set(v___x_3560_, 0, v_a_3575_);
v___x_3582_ = v___x_3560_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3575_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3583_, 0, v_a_3573_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_snd_3558_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_mkConst(v___x_3579_, v___x_3584_);
v___x_3586_ = lean_unsigned_to_nat(7u);
v___x_3587_ = lean_mk_empty_array_with_capacity(v___x_3586_);
v___x_3588_ = lean_array_push(v___x_3587_, v_00_u03b1_3562_);
v___x_3589_ = lean_array_push(v___x_3588_, v_00_u03b2_3563_);
v___x_3590_ = lean_array_push(v___x_3589_, v_fst_3557_);
v___x_3591_ = lean_array_push(v___x_3590_, v_x_3507_);
v___x_3592_ = lean_array_push(v___x_3591_, v_a_3567_);
v___x_3593_ = lean_array_push(v___x_3592_, v_a_3571_);
v___x_3594_ = lean_array_push(v___x_3593_, v_F_3508_);
v___x_3595_ = l_Lean_mkAppN(v___x_3585_, v___x_3594_);
lean_dec_ref(v___x_3594_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3595_);
v___x_3597_ = v___x_3577_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v_a_3573_);
lean_dec(v_a_3571_);
lean_dec(v_a_3567_);
lean_dec(v_00_u03b2_3563_);
lean_dec(v_00_u03b1_3562_);
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
v_a_3601_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3574_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3574_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3571_);
lean_dec(v_a_3567_);
lean_dec(v_00_u03b2_3563_);
lean_dec(v_00_u03b1_3562_);
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
v_a_3609_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3572_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3572_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_dec(v_a_3567_);
lean_dec(v_00_u03b2_3563_);
lean_dec(v_00_u03b1_3562_);
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
return v___x_3570_;
}
}
else
{
lean_dec(v_00_u03b2_3563_);
lean_dec(v_00_u03b1_3562_);
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec_ref(v_args_3548_);
lean_dec(v_a_3543_);
lean_dec_ref(v_k_3510_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
return v___x_3566_;
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_args_3548_);
lean_dec(v_a_3543_);
lean_dec_ref(v_k_3510_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
v_a_3618_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3555_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3555_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v___x_3522_);
lean_dec_ref(v_k_3510_);
lean_dec_ref(v_val_3509_);
lean_dec_ref(v_F_3508_);
lean_dec_ref(v_x_3507_);
v_a_3626_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3542_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3542_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3638_, lean_object* v_body_3639_, lean_object* v_k_3640_, lean_object* v___x_3641_, uint8_t v___x_3642_, uint8_t v___x_3643_, lean_object* v_FNew_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
lean_inc_ref(v_FNew_3644_);
lean_inc_ref(v___x_3638_);
v___x_3652_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3638_, v_FNew_3644_, v_body_3639_, v_k_3640_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3641_);
v___x_3655_ = lean_array_push(v___x_3654_, v___x_3638_);
v___x_3656_ = lean_array_push(v___x_3655_, v_FNew_3644_);
v___x_3657_ = 1;
v___x_3658_ = l_Lean_Meta_mkLambdaFVars(v___x_3656_, v_a_3653_, v___x_3642_, v___x_3643_, v___x_3642_, v___x_3643_, v___x_3657_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec_ref(v___x_3656_);
return v___x_3658_;
}
else
{
lean_dec_ref(v_FNew_3644_);
lean_dec_ref(v___x_3638_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3659_, lean_object* v_body_3660_, lean_object* v_k_3661_, lean_object* v___x_3662_, lean_object* v___x_3663_, lean_object* v___x_3664_, lean_object* v_FNew_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v___x_6949__boxed_3673_; uint8_t v___x_6950__boxed_3674_; lean_object* v_res_3675_; 
v___x_6949__boxed_3673_ = lean_unbox(v___x_3663_);
v___x_6950__boxed_3674_ = lean_unbox(v___x_3664_);
v_res_3675_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3659_, v_body_3660_, v_k_3661_, v___x_3662_, v___x_6949__boxed_3673_, v___x_6950__boxed_3674_, v_FNew_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___x_3662_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3676_, lean_object* v___x_3677_, lean_object* v_00_u03b1_3678_, lean_object* v_00_u03b2_3679_, lean_object* v___x_3680_, lean_object* v_ctorName_3681_, lean_object* v_k_3682_, lean_object* v___x_3683_, uint8_t v___x_3684_, uint8_t v___x_3685_, lean_object* v_a_3686_, lean_object* v_x_3687_, lean_object* v_xs_3688_, lean_object* v_body_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3697_ = lean_array_get_borrowed(v___x_3676_, v_xs_3688_, v___x_3677_);
v___x_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3698_, 0, v_00_u03b1_3678_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v_00_u03b2_3679_);
lean_inc(v___x_3697_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3697_);
v___x_3701_ = lean_mk_empty_array_with_capacity(v___x_3680_);
v___x_3702_ = lean_array_push(v___x_3701_, v___x_3698_);
v___x_3703_ = lean_array_push(v___x_3702_, v___x_3699_);
v___x_3704_ = lean_array_push(v___x_3703_, v___x_3700_);
v___x_3705_ = l_Lean_Meta_mkAppOptM(v_ctorName_3681_, v___x_3704_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___f_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = lean_box(v___x_3684_);
v___x_3708_ = lean_box(v___x_3685_);
lean_inc(v___x_3697_);
v___f_3709_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3709_, 0, v___x_3697_);
lean_closure_set(v___f_3709_, 1, v_body_3689_);
lean_closure_set(v___f_3709_, 2, v_k_3682_);
lean_closure_set(v___f_3709_, 3, v___x_3683_);
lean_closure_set(v___f_3709_, 4, v___x_3707_);
lean_closure_set(v___f_3709_, 5, v___x_3708_);
v___x_3710_ = l_Lean_LocalDecl_type(v_a_3686_);
v___x_3711_ = l_Lean_Expr_replaceFVar(v___x_3710_, v_x_3687_, v_a_3706_);
lean_dec(v_a_3706_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = l_Lean_LocalDecl_userName(v_a_3686_);
v___x_3713_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3712_, v___x_3711_, v___f_3709_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3713_;
}
else
{
lean_dec_ref(v_body_3689_);
lean_dec_ref(v_x_3687_);
lean_dec(v___x_3683_);
lean_dec_ref(v_k_3682_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3714_ = _args[0];
lean_object* v___x_3715_ = _args[1];
lean_object* v_00_u03b1_3716_ = _args[2];
lean_object* v_00_u03b2_3717_ = _args[3];
lean_object* v___x_3718_ = _args[4];
lean_object* v_ctorName_3719_ = _args[5];
lean_object* v_k_3720_ = _args[6];
lean_object* v___x_3721_ = _args[7];
lean_object* v___x_3722_ = _args[8];
lean_object* v___x_3723_ = _args[9];
lean_object* v_a_3724_ = _args[10];
lean_object* v_x_3725_ = _args[11];
lean_object* v_xs_3726_ = _args[12];
lean_object* v_body_3727_ = _args[13];
lean_object* v___y_3728_ = _args[14];
lean_object* v___y_3729_ = _args[15];
lean_object* v___y_3730_ = _args[16];
lean_object* v___y_3731_ = _args[17];
lean_object* v___y_3732_ = _args[18];
lean_object* v___y_3733_ = _args[19];
lean_object* v___y_3734_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3735_; uint8_t v___x_6971__boxed_3736_; lean_object* v_res_3737_; 
v___x_6970__boxed_3735_ = lean_unbox(v___x_3722_);
v___x_6971__boxed_3736_ = lean_unbox(v___x_3723_);
v_res_3737_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3714_, v___x_3715_, v_00_u03b1_3716_, v_00_u03b2_3717_, v___x_3718_, v_ctorName_3719_, v_k_3720_, v___x_3721_, v___x_6970__boxed_3735_, v___x_6971__boxed_3736_, v_a_3724_, v_x_3725_, v_xs_3726_, v_body_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec_ref(v_xs_3726_);
lean_dec_ref(v_a_3724_);
lean_dec(v___x_3718_);
lean_dec(v___x_3715_);
lean_dec_ref(v___x_3714_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3738_, lean_object* v___x_3739_, lean_object* v_00_u03b1_3740_, lean_object* v_00_u03b2_3741_, lean_object* v___x_3742_, lean_object* v_k_3743_, lean_object* v___x_3744_, uint8_t v___x_3745_, uint8_t v___x_3746_, lean_object* v_a_3747_, lean_object* v_x_3748_, lean_object* v___x_3749_, lean_object* v_ctorName_3750_, lean_object* v_minor_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___f_3761_; lean_object* v___x_3762_; 
v___x_3759_ = lean_box(v___x_3745_);
v___x_3760_ = lean_box(v___x_3746_);
v___f_3761_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3761_, 0, v___x_3738_);
lean_closure_set(v___f_3761_, 1, v___x_3739_);
lean_closure_set(v___f_3761_, 2, v_00_u03b1_3740_);
lean_closure_set(v___f_3761_, 3, v_00_u03b2_3741_);
lean_closure_set(v___f_3761_, 4, v___x_3742_);
lean_closure_set(v___f_3761_, 5, v_ctorName_3750_);
lean_closure_set(v___f_3761_, 6, v_k_3743_);
lean_closure_set(v___f_3761_, 7, v___x_3744_);
lean_closure_set(v___f_3761_, 8, v___x_3759_);
lean_closure_set(v___f_3761_, 9, v___x_3760_);
lean_closure_set(v___f_3761_, 10, v_a_3747_);
lean_closure_set(v___f_3761_, 11, v_x_3748_);
v___x_3762_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3751_, v___x_3749_, v___f_3761_, v___x_3745_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3763_ = _args[0];
lean_object* v___x_3764_ = _args[1];
lean_object* v_00_u03b1_3765_ = _args[2];
lean_object* v_00_u03b2_3766_ = _args[3];
lean_object* v___x_3767_ = _args[4];
lean_object* v_k_3768_ = _args[5];
lean_object* v___x_3769_ = _args[6];
lean_object* v___x_3770_ = _args[7];
lean_object* v___x_3771_ = _args[8];
lean_object* v_a_3772_ = _args[9];
lean_object* v_x_3773_ = _args[10];
lean_object* v___x_3774_ = _args[11];
lean_object* v_ctorName_3775_ = _args[12];
lean_object* v_minor_3776_ = _args[13];
lean_object* v___y_3777_ = _args[14];
lean_object* v___y_3778_ = _args[15];
lean_object* v___y_3779_ = _args[16];
lean_object* v___y_3780_ = _args[17];
lean_object* v___y_3781_ = _args[18];
lean_object* v___y_3782_ = _args[19];
lean_object* v___y_3783_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3784_; uint8_t v___x_6935__boxed_3785_; lean_object* v_res_3786_; 
v___x_6934__boxed_3784_ = lean_unbox(v___x_3770_);
v___x_6935__boxed_3785_ = lean_unbox(v___x_3771_);
v_res_3786_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3763_, v___x_3764_, v_00_u03b1_3765_, v_00_u03b2_3766_, v___x_3767_, v_k_3768_, v___x_3769_, v___x_6934__boxed_3784_, v___x_6935__boxed_3785_, v_a_3772_, v_x_3773_, v___x_3774_, v_ctorName_3775_, v_minor_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3787_, lean_object* v_F_3788_, lean_object* v_val_3789_, lean_object* v_k_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3787_, v_F_3788_, v_val_3789_, v_k_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3799_, lean_object* v_name_3800_, uint8_t v_bi_3801_, lean_object* v_type_3802_, lean_object* v_k_3803_, uint8_t v_kind_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3800_, v_bi_3801_, v_type_3802_, v_k_3803_, v_kind_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_name_3814_, lean_object* v_bi_3815_, lean_object* v_type_3816_, lean_object* v_k_3817_, lean_object* v_kind_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
uint8_t v_bi_boxed_3826_; uint8_t v_kind_boxed_3827_; lean_object* v_res_3828_; 
v_bi_boxed_3826_ = lean_unbox(v_bi_3815_);
v_kind_boxed_3827_ = lean_unbox(v_kind_3818_);
v_res_3828_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3813_, v_name_3814_, v_bi_boxed_3826_, v_type_3816_, v_k_3817_, v_kind_boxed_3827_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3829_, lean_object* v_name_3830_, lean_object* v_type_3831_, lean_object* v_k_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3830_, v_type_3831_, v_k_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_name_3842_, lean_object* v_type_3843_, lean_object* v_k_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3841_, v_name_3842_, v_type_3843_, v_k_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3852_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3874__overap_3863_; lean_object* v___x_3864_; 
v___x_3862_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3863_ = lean_panic_fn_borrowed(v___x_3862_, v_msg_3854_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc_ref(v___y_3855_);
v___x_3864_ = lean_apply_7(v___x_3874__overap_3863_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, lean_box(0));
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3873_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3878_ = lean_unsigned_to_nat(49u);
v___x_3879_ = lean_unsigned_to_nat(186u);
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3882_ = l_mkPanicMessageWithDecl(v___x_3881_, v___x_3880_, v___x_3879_, v___x_3878_, v___x_3877_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3888_, lean_object* v_a_3889_, lean_object* v_k_3890_, lean_object* v___x_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v_FNew_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
uint8_t v___x_4042__boxed_3904_; uint8_t v___x_4043__boxed_3905_; uint8_t v___x_4044__boxed_3906_; lean_object* v_res_3907_; 
v___x_4042__boxed_3904_ = lean_unbox(v___x_3893_);
v___x_4043__boxed_3905_ = lean_unbox(v___x_3894_);
v___x_4044__boxed_3906_ = lean_unbox(v___x_3895_);
v_res_3907_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3888_, v_a_3889_, v_k_3890_, v___x_3891_, v___x_3892_, v___x_4042__boxed_3904_, v___x_4043__boxed_3905_, v___x_4044__boxed_3906_, v_FNew_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___x_3891_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3908_, lean_object* v___x_3909_, lean_object* v___x_3910_, lean_object* v___x_3911_, uint8_t v___x_3912_, uint8_t v___x_3913_, lean_object* v_00_u03b1_3914_, lean_object* v_00_u03b2_3915_, lean_object* v___x_3916_, lean_object* v_k_3917_, lean_object* v___x_3918_, lean_object* v_a_3919_, lean_object* v_x_3920_, lean_object* v_xs_3921_, lean_object* v_body_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; 
v___x_3930_ = lean_array_get(v___x_3908_, v_xs_3921_, v___x_3909_);
v___x_3931_ = lean_array_get(v___x_3908_, v_xs_3921_, v___x_3910_);
v___x_3932_ = lean_array_get_size(v_xs_3921_);
v___x_3933_ = l_Array_toSubarray___redArg(v_xs_3921_, v___x_3911_, v___x_3932_);
v___x_3934_ = l_Subarray_copy___redArg(v___x_3933_);
v___x_3935_ = 1;
v___x_3936_ = l_Lean_Meta_mkLambdaFVars(v___x_3934_, v_body_3922_, v___x_3912_, v___x_3913_, v___x_3912_, v___x_3913_, v___x_3935_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec_ref(v___x_3934_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3963_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3939_ = v___x_3936_;
v_isShared_3940_ = v_isSharedCheck_3963_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3936_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3963_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3940_ == 0)
{
lean_ctor_set_tag(v___x_3939_, 1);
lean_ctor_set(v___x_3939_, 0, v_00_u03b1_3914_);
v___x_3943_ = v___x_3939_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_00_u03b1_3914_);
v___x_3943_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v_00_u03b2_3915_);
lean_inc(v___x_3930_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3930_);
lean_inc(v___x_3931_);
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3931_);
v___x_3947_ = lean_mk_empty_array_with_capacity(v___x_3916_);
v___x_3948_ = lean_array_push(v___x_3947_, v___x_3943_);
v___x_3949_ = lean_array_push(v___x_3948_, v___x_3944_);
v___x_3950_ = lean_array_push(v___x_3949_, v___x_3945_);
v___x_3951_ = lean_array_push(v___x_3950_, v___x_3946_);
v___x_3952_ = l_Lean_Meta_mkAppOptM(v___x_3941_, v___x_3951_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref(v___x_3952_);
v___x_3954_ = lean_box(v___x_3912_);
v___x_3955_ = lean_box(v___x_3913_);
v___x_3956_ = lean_box(v___x_3935_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3957_, 0, v___x_3931_);
lean_closure_set(v___f_3957_, 1, v_a_3937_);
lean_closure_set(v___f_3957_, 2, v_k_3917_);
lean_closure_set(v___f_3957_, 3, v___x_3918_);
lean_closure_set(v___f_3957_, 4, v___x_3930_);
lean_closure_set(v___f_3957_, 5, v___x_3954_);
lean_closure_set(v___f_3957_, 6, v___x_3955_);
lean_closure_set(v___f_3957_, 7, v___x_3956_);
v___x_3958_ = l_Lean_LocalDecl_type(v_a_3919_);
v___x_3959_ = l_Lean_Expr_replaceFVar(v___x_3958_, v_x_3920_, v_a_3953_);
lean_dec(v_a_3953_);
lean_dec_ref(v___x_3958_);
v___x_3960_ = l_Lean_LocalDecl_userName(v_a_3919_);
v___x_3961_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3960_, v___x_3959_, v___f_3957_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
return v___x_3961_;
}
else
{
lean_dec(v_a_3937_);
lean_dec(v___x_3931_);
lean_dec(v___x_3930_);
lean_dec_ref(v_x_3920_);
lean_dec(v___x_3918_);
lean_dec_ref(v_k_3917_);
return v___x_3952_;
}
}
}
}
else
{
lean_dec(v___x_3931_);
lean_dec(v___x_3930_);
lean_dec_ref(v_x_3920_);
lean_dec(v___x_3918_);
lean_dec_ref(v_k_3917_);
lean_dec_ref(v_00_u03b2_3915_);
lean_dec_ref(v_00_u03b1_3914_);
return v___x_3936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3964_ = _args[0];
lean_object* v___x_3965_ = _args[1];
lean_object* v___x_3966_ = _args[2];
lean_object* v___x_3967_ = _args[3];
lean_object* v___x_3968_ = _args[4];
lean_object* v___x_3969_ = _args[5];
lean_object* v_00_u03b1_3970_ = _args[6];
lean_object* v_00_u03b2_3971_ = _args[7];
lean_object* v___x_3972_ = _args[8];
lean_object* v_k_3973_ = _args[9];
lean_object* v___x_3974_ = _args[10];
lean_object* v_a_3975_ = _args[11];
lean_object* v_x_3976_ = _args[12];
lean_object* v_xs_3977_ = _args[13];
lean_object* v_body_3978_ = _args[14];
lean_object* v___y_3979_ = _args[15];
lean_object* v___y_3980_ = _args[16];
lean_object* v___y_3981_ = _args[17];
lean_object* v___y_3982_ = _args[18];
lean_object* v___y_3983_ = _args[19];
lean_object* v___y_3984_ = _args[20];
lean_object* v___y_3985_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_3986_; uint8_t v___x_4070__boxed_3987_; lean_object* v_res_3988_; 
v___x_4069__boxed_3986_ = lean_unbox(v___x_3968_);
v___x_4070__boxed_3987_ = lean_unbox(v___x_3969_);
v_res_3988_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3964_, v___x_3965_, v___x_3966_, v___x_3967_, v___x_4069__boxed_3986_, v___x_4070__boxed_3987_, v_00_u03b1_3970_, v_00_u03b2_3971_, v___x_3972_, v_k_3973_, v___x_3974_, v_a_3975_, v_x_3976_, v_xs_3977_, v_body_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v_a_3975_);
lean_dec(v___x_3972_);
lean_dec(v___x_3966_);
lean_dec(v___x_3965_);
lean_dec_ref(v___x_3964_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3992_, lean_object* v_F_3993_, lean_object* v_val_3994_, lean_object* v_k_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; uint8_t v___y_4013_; uint8_t v___x_4105_; 
v___x_4105_ = l_Lean_Expr_isFVar(v_x_3992_);
if (v___x_4105_ == 0)
{
v___y_4013_ = v___x_4105_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_4106_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4107_ = lean_unsigned_to_nat(5u);
v___x_4108_ = l_Lean_Expr_isAppOfArity(v_val_3994_, v___x_4106_, v___x_4107_);
v___y_4013_ = v___x_4108_;
goto v___jp_4012_;
}
v___jp_4003_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4011_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4010_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4011_;
}
v___jp_4012_:
{
if (v___y_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_dec_ref(v_x_3992_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
v___x_4014_ = lean_apply_9(v_k_3995_, v_F_3993_, v_val_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, lean_box(0));
return v___x_4014_;
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4015_ = lean_unsigned_to_nat(3u);
v___x_4016_ = l_Lean_Expr_getAppNumArgs(v_val_3994_);
v___x_4017_ = lean_nat_sub(v___x_4016_, v___x_4015_);
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = lean_nat_sub(v___x_4017_, v___x_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = l_Lean_Expr_getRevArg_x21(v_val_3994_, v___x_4019_);
v___x_4021_ = lean_expr_eqv(v___x_4020_, v_x_3992_);
lean_dec_ref(v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_dec(v___x_4016_);
lean_dec_ref(v_x_3992_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
v___x_4022_ = lean_apply_9(v_k_3995_, v_F_3993_, v_val_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, lean_box(0));
return v___x_4022_;
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4023_ = lean_unsigned_to_nat(4u);
v___x_4024_ = lean_nat_sub(v___x_4016_, v___x_4023_);
v___x_4025_ = lean_nat_sub(v___x_4024_, v___x_4018_);
lean_dec(v___x_4024_);
v___x_4026_ = l_Lean_Expr_getRevArg_x21(v_val_3994_, v___x_4025_);
v___x_4027_ = l_Lean_Expr_isLambda(v___x_4026_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref(v___x_4026_);
lean_dec(v___x_4016_);
lean_dec_ref(v_x_3992_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
v___x_4028_ = lean_apply_9(v_k_3995_, v_F_3993_, v_val_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, lean_box(0));
return v___x_4028_;
}
else
{
lean_object* v___x_4029_; uint8_t v___x_4030_; 
v___x_4029_ = l_Lean_Expr_bindingBody_x21(v___x_4026_);
lean_dec_ref(v___x_4026_);
v___x_4030_ = l_Lean_Expr_isLambda(v___x_4029_);
lean_dec_ref(v___x_4029_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; 
lean_dec(v___x_4016_);
lean_dec_ref(v_x_3992_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
lean_inc(v_a_3997_);
lean_inc_ref(v_a_3996_);
v___x_4031_ = lean_apply_9(v_k_3995_, v_F_3993_, v_val_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, lean_box(0));
return v___x_4031_;
}
else
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = l_Lean_Expr_getAppFn(v_val_3994_);
v___x_4033_ = l_Lean_Expr_constLevels_x21(v___x_4032_);
lean_dec_ref(v___x_4032_);
if (lean_obj_tag(v___x_4033_) == 1)
{
lean_object* v_tail_4034_; 
v_tail_4034_ = lean_ctor_get(v___x_4033_, 1);
lean_inc(v_tail_4034_);
lean_dec_ref(v___x_4033_);
if (lean_obj_tag(v_tail_4034_) == 1)
{
lean_object* v_tail_4035_; 
v_tail_4035_ = lean_ctor_get(v_tail_4034_, 1);
lean_inc(v_tail_4035_);
if (lean_obj_tag(v_tail_4035_) == 1)
{
lean_object* v_tail_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4103_; 
v_tail_4036_ = lean_ctor_get(v_tail_4035_, 1);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_tail_4035_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; 
v_unused_4104_ = lean_ctor_get(v_tail_4035_, 0);
lean_dec(v_unused_4104_);
v___x_4038_ = v_tail_4035_;
v_isShared_4039_ = v_isSharedCheck_4103_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_tail_4036_);
lean_dec(v_tail_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4103_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
if (lean_obj_tag(v_tail_4036_) == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = l_Lean_Expr_fvarId_x21(v_F_3993_);
v___x_4041_ = l_Lean_FVarId_getDecl___redArg(v___x_4040_, v_a_3998_, v_a_4000_, v_a_4001_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4043_; lean_object* v_dummy_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_args_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_n(v_a_4042_, 2);
lean_dec_ref(v___x_4041_);
v___x_4043_ = l_Lean_instInhabitedExpr;
v_dummy_4044_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_4016_);
v___x_4045_ = lean_mk_array(v___x_4016_, v_dummy_4044_);
v___x_4046_ = lean_nat_sub(v___x_4016_, v___x_4018_);
lean_dec(v___x_4016_);
v_args_4047_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3994_, v___x_4045_, v___x_4046_);
v___x_4048_ = lean_unsigned_to_nat(0u);
v___x_4049_ = lean_box(v___x_4027_);
lean_inc_ref(v_x_3992_);
v___f_4050_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4050_, 0, v_a_4042_);
lean_closure_set(v___f_4050_, 1, v___x_4043_);
lean_closure_set(v___f_4050_, 2, v___x_4048_);
lean_closure_set(v___f_4050_, 3, v_x_3992_);
lean_closure_set(v___f_4050_, 4, v___x_4049_);
v___x_4051_ = lean_unsigned_to_nat(2u);
v___x_4052_ = lean_array_get(v___x_4043_, v_args_4047_, v___x_4051_);
v___x_4053_ = 0;
v___x_4054_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4052_, v___f_4050_, v___x_4053_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v_fst_4056_; lean_object* v_snd_4057_; lean_object* v_00_u03b1_4058_; lean_object* v_00_u03b2_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___f_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref(v___x_4054_);
v_fst_4056_ = lean_ctor_get(v_a_4055_, 0);
lean_inc(v_fst_4056_);
v_snd_4057_ = lean_ctor_get(v_a_4055_, 1);
lean_inc(v_snd_4057_);
lean_dec(v_a_4055_);
v_00_u03b1_4058_ = lean_array_get(v___x_4043_, v_args_4047_, v___x_4048_);
v_00_u03b2_4059_ = lean_array_get(v___x_4043_, v_args_4047_, v___x_4018_);
v___x_4060_ = lean_box(v___x_4053_);
v___x_4061_ = lean_box(v___x_4027_);
lean_inc_ref(v_x_3992_);
lean_inc(v_00_u03b2_4059_);
lean_inc(v_00_u03b1_4058_);
v___f_4062_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4062_, 0, v___x_4043_);
lean_closure_set(v___f_4062_, 1, v___x_4048_);
lean_closure_set(v___f_4062_, 2, v___x_4018_);
lean_closure_set(v___f_4062_, 3, v___x_4051_);
lean_closure_set(v___f_4062_, 4, v___x_4060_);
lean_closure_set(v___f_4062_, 5, v___x_4061_);
lean_closure_set(v___f_4062_, 6, v_00_u03b1_4058_);
lean_closure_set(v___f_4062_, 7, v_00_u03b2_4059_);
lean_closure_set(v___f_4062_, 8, v___x_4023_);
lean_closure_set(v___f_4062_, 9, v_k_3995_);
lean_closure_set(v___f_4062_, 10, v___x_4015_);
lean_closure_set(v___f_4062_, 11, v_a_4042_);
lean_closure_set(v___f_4062_, 12, v_x_3992_);
v___x_4063_ = lean_array_get(v___x_4043_, v_args_4047_, v___x_4023_);
lean_dec_ref(v_args_4047_);
v___x_4064_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4063_, v___f_4062_, v___x_4053_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4086_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4086_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4086_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4069_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 1, v_tail_4034_);
lean_ctor_set(v___x_4038_, 0, v_snd_4057_);
v___x_4071_ = v___x_4038_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_snd_4057_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_tail_4034_);
v___x_4071_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4072_ = l_Lean_mkConst(v___x_4069_, v___x_4071_);
v___x_4073_ = lean_unsigned_to_nat(6u);
v___x_4074_ = lean_mk_empty_array_with_capacity(v___x_4073_);
v___x_4075_ = lean_array_push(v___x_4074_, v_00_u03b1_4058_);
v___x_4076_ = lean_array_push(v___x_4075_, v_00_u03b2_4059_);
v___x_4077_ = lean_array_push(v___x_4076_, v_fst_4056_);
v___x_4078_ = lean_array_push(v___x_4077_, v_x_3992_);
v___x_4079_ = lean_array_push(v___x_4078_, v_a_4065_);
v___x_4080_ = lean_array_push(v___x_4079_, v_F_3993_);
v___x_4081_ = l_Lean_mkAppN(v___x_4072_, v___x_4080_);
lean_dec_ref(v___x_4080_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4081_);
v___x_4083_ = v___x_4067_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4059_);
lean_dec(v_00_u03b1_4058_);
lean_dec(v_snd_4057_);
lean_dec(v_fst_4056_);
lean_del_object(v___x_4038_);
lean_dec_ref(v_tail_4034_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
return v___x_4064_;
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v_args_4047_);
lean_dec(v_a_4042_);
lean_del_object(v___x_4038_);
lean_dec_ref(v_tail_4034_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v_a_4087_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4054_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4054_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_del_object(v___x_4038_);
lean_dec_ref(v_tail_4034_);
lean_dec(v___x_4016_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_val_3994_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v_a_4095_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4041_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4041_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
else
{
lean_del_object(v___x_4038_);
lean_dec(v_tail_4036_);
lean_dec_ref(v_tail_4034_);
lean_dec(v___x_4016_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_val_3994_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
goto v___jp_4003_;
}
}
}
else
{
lean_dec_ref(v_tail_4034_);
lean_dec(v_tail_4035_);
lean_dec(v___x_4016_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_val_3994_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
goto v___jp_4003_;
}
}
else
{
lean_dec(v_tail_4034_);
lean_dec(v___x_4016_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_val_3994_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
goto v___jp_4003_;
}
}
else
{
lean_dec(v___x_4033_);
lean_dec(v___x_4016_);
lean_dec_ref(v_k_3995_);
lean_dec_ref(v_val_3994_);
lean_dec_ref(v_F_3993_);
lean_dec_ref(v_x_3992_);
v___y_4004_ = v_a_3996_;
v___y_4005_ = v_a_3997_;
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
goto v___jp_4003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4109_, lean_object* v_a_4110_, lean_object* v_k_4111_, lean_object* v___x_4112_, lean_object* v___x_4113_, uint8_t v___x_4114_, uint8_t v___x_4115_, uint8_t v___x_4116_, lean_object* v_FNew_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
lean_inc_ref(v_FNew_4117_);
lean_inc_ref(v___x_4109_);
v___x_4125_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4109_, v_FNew_4117_, v_a_4110_, v_k_4111_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref(v___x_4125_);
v___x_4127_ = lean_mk_empty_array_with_capacity(v___x_4112_);
v___x_4128_ = lean_array_push(v___x_4127_, v___x_4113_);
v___x_4129_ = lean_array_push(v___x_4128_, v___x_4109_);
v___x_4130_ = lean_array_push(v___x_4129_, v_FNew_4117_);
v___x_4131_ = l_Lean_Meta_mkLambdaFVars(v___x_4130_, v_a_4126_, v___x_4114_, v___x_4115_, v___x_4114_, v___x_4115_, v___x_4116_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec_ref(v___x_4130_);
return v___x_4131_;
}
else
{
lean_dec_ref(v_FNew_4117_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4109_);
return v___x_4125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4132_, lean_object* v_F_4133_, lean_object* v_val_4134_, lean_object* v_k_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4132_, v_F_4133_, v_val_4134_, v_k_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_ref_4158_; uint8_t v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v___x_4157_);
v_ref_4158_ = lean_ctor_get(v___y_4154_, 5);
v___x_4159_ = 0;
v___x_4160_ = l_Lean_SourceInfo_fromRef(v_ref_4158_, v___x_4159_);
v___x_4161_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4160_);
v___x_4163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4160_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = l_Lean_Syntax_node1(v___x_4160_, v___x_4161_, v___x_4163_);
v___x_4165_ = l_Lean_Elab_Tactic_evalTactic(v___x_4164_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
return v___x_4165_;
}
else
{
return v___x_4157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v___f_4185_; lean_object* v___x_4186_; 
v___f_4185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4186_ = l_Lean_Elab_Tactic_run(v_mvarId_4177_, v___f_4185_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4197_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4197_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4197_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
uint8_t v___x_4191_; 
v___x_4191_ = l_List_isEmpty___redArg(v_a_4187_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
lean_del_object(v___x_4189_);
v___x_4192_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4187_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
return v___x_4192_;
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
lean_dec(v_a_4187_);
v___x_4193_ = lean_box(0);
if (v_isShared_4190_ == 0)
{
lean_ctor_set(v___x_4189_, 0, v___x_4193_);
v___x_4195_ = v___x_4189_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4186_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4186_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4215_, lean_object* v_x_4216_, lean_object* v_x_4217_, lean_object* v_x_4218_){
_start:
{
lean_object* v_ks_4219_; lean_object* v_vs_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4244_; 
v_ks_4219_ = lean_ctor_get(v_x_4215_, 0);
v_vs_4220_ = lean_ctor_get(v_x_4215_, 1);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_x_4215_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4222_ = v_x_4215_;
v_isShared_4223_ = v_isSharedCheck_4244_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_vs_4220_);
lean_inc(v_ks_4219_);
lean_dec(v_x_4215_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4244_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = lean_array_get_size(v_ks_4219_);
v___x_4225_ = lean_nat_dec_lt(v_x_4216_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
lean_dec(v_x_4216_);
v___x_4226_ = lean_array_push(v_ks_4219_, v_x_4217_);
v___x_4227_ = lean_array_push(v_vs_4220_, v_x_4218_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v___x_4227_);
lean_ctor_set(v___x_4222_, 0, v___x_4226_);
v___x_4229_ = v___x_4222_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4226_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
else
{
lean_object* v_k_x27_4231_; uint8_t v___x_4232_; 
v_k_x27_4231_ = lean_array_fget_borrowed(v_ks_4219_, v_x_4216_);
v___x_4232_ = l_Lean_instBEqMVarId_beq(v_x_4217_, v_k_x27_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4234_; 
if (v_isShared_4223_ == 0)
{
v___x_4234_ = v___x_4222_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_ks_4219_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_vs_4220_);
v___x_4234_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_unsigned_to_nat(1u);
v___x_4236_ = lean_nat_add(v_x_4216_, v___x_4235_);
lean_dec(v_x_4216_);
v_x_4215_ = v___x_4234_;
v_x_4216_ = v___x_4236_;
goto _start;
}
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4239_ = lean_array_fset(v_ks_4219_, v_x_4216_, v_x_4217_);
v___x_4240_ = lean_array_fset(v_vs_4220_, v_x_4216_, v_x_4218_);
lean_dec(v_x_4216_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v___x_4240_);
lean_ctor_set(v___x_4222_, 0, v___x_4239_);
v___x_4242_ = v___x_4222_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4245_, lean_object* v_k_4246_, lean_object* v_v_4247_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4245_, v___x_4248_, v_k_4246_, v_v_4247_);
return v___x_4249_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4250_; size_t v___x_4251_; size_t v___x_4252_; 
v___x_4250_ = ((size_t)5ULL);
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_shift_left(v___x_4251_, v___x_4250_);
return v___x_4252_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4253_; size_t v___x_4254_; size_t v___x_4255_; 
v___x_4253_ = ((size_t)1ULL);
v___x_4254_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4255_ = lean_usize_sub(v___x_4254_, v___x_4253_);
return v___x_4255_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4257_, size_t v_x_4258_, size_t v_x_4259_, lean_object* v_x_4260_, lean_object* v_x_4261_){
_start:
{
if (lean_obj_tag(v_x_4257_) == 0)
{
lean_object* v_es_4262_; size_t v___x_4263_; size_t v___x_4264_; size_t v___x_4265_; size_t v___x_4266_; lean_object* v_j_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_es_4262_ = lean_ctor_get(v_x_4257_, 0);
v___x_4263_ = ((size_t)5ULL);
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4266_ = lean_usize_land(v_x_4258_, v___x_4265_);
v_j_4267_ = lean_usize_to_nat(v___x_4266_);
v___x_4268_ = lean_array_get_size(v_es_4262_);
v___x_4269_ = lean_nat_dec_lt(v_j_4267_, v___x_4268_);
if (v___x_4269_ == 0)
{
lean_dec(v_j_4267_);
lean_dec(v_x_4261_);
lean_dec(v_x_4260_);
return v_x_4257_;
}
else
{
lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4306_; 
lean_inc_ref(v_es_4262_);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_x_4257_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v_x_4257_, 0);
lean_dec(v_unused_4307_);
v___x_4271_ = v_x_4257_;
v_isShared_4272_ = v_isSharedCheck_4306_;
goto v_resetjp_4270_;
}
else
{
lean_dec(v_x_4257_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4306_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v_v_4273_; lean_object* v___x_4274_; lean_object* v_xs_x27_4275_; lean_object* v___y_4277_; 
v_v_4273_ = lean_array_fget(v_es_4262_, v_j_4267_);
v___x_4274_ = lean_box(0);
v_xs_x27_4275_ = lean_array_fset(v_es_4262_, v_j_4267_, v___x_4274_);
switch(lean_obj_tag(v_v_4273_))
{
case 0:
{
lean_object* v_key_4282_; lean_object* v_val_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4293_; 
v_key_4282_ = lean_ctor_get(v_v_4273_, 0);
v_val_4283_ = lean_ctor_get(v_v_4273_, 1);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_v_4273_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4285_ = v_v_4273_;
v_isShared_4286_ = v_isSharedCheck_4293_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_val_4283_);
lean_inc(v_key_4282_);
lean_dec(v_v_4273_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4293_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
uint8_t v___x_4287_; 
v___x_4287_ = l_Lean_instBEqMVarId_beq(v_x_4260_, v_key_4282_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_del_object(v___x_4285_);
v___x_4288_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4282_, v_val_4283_, v_x_4260_, v_x_4261_);
v___x_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
v___y_4277_ = v___x_4289_;
goto v___jp_4276_;
}
else
{
lean_object* v___x_4291_; 
lean_dec(v_val_4283_);
lean_dec(v_key_4282_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 1, v_x_4261_);
lean_ctor_set(v___x_4285_, 0, v_x_4260_);
v___x_4291_ = v___x_4285_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_x_4260_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_x_4261_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
v___y_4277_ = v___x_4291_;
goto v___jp_4276_;
}
}
}
}
case 1:
{
lean_object* v_node_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4304_; 
v_node_4294_ = lean_ctor_get(v_v_4273_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_v_4273_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4296_ = v_v_4273_;
v_isShared_4297_ = v_isSharedCheck_4304_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_node_4294_);
lean_dec(v_v_4273_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4304_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
size_t v___x_4298_; size_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4302_; 
v___x_4298_ = lean_usize_shift_right(v_x_4258_, v___x_4263_);
v___x_4299_ = lean_usize_add(v_x_4259_, v___x_4264_);
v___x_4300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4294_, v___x_4298_, v___x_4299_, v_x_4260_, v_x_4261_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4300_);
v___x_4302_ = v___x_4296_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4300_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
v___y_4277_ = v___x_4302_;
goto v___jp_4276_;
}
}
}
default: 
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_x_4260_);
lean_ctor_set(v___x_4305_, 1, v_x_4261_);
v___y_4277_ = v___x_4305_;
goto v___jp_4276_;
}
}
v___jp_4276_:
{
lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4278_ = lean_array_fset(v_xs_x27_4275_, v_j_4267_, v___y_4277_);
lean_dec(v_j_4267_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4278_);
v___x_4280_ = v___x_4271_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
else
{
lean_object* v_ks_4308_; lean_object* v_vs_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4329_; 
v_ks_4308_ = lean_ctor_get(v_x_4257_, 0);
v_vs_4309_ = lean_ctor_get(v_x_4257_, 1);
v_isSharedCheck_4329_ = !lean_is_exclusive(v_x_4257_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4311_ = v_x_4257_;
v_isShared_4312_ = v_isSharedCheck_4329_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_vs_4309_);
lean_inc(v_ks_4308_);
lean_dec(v_x_4257_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4329_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_ks_4308_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_vs_4309_);
v___x_4314_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v_newNode_4315_; uint8_t v___y_4317_; size_t v___x_4323_; uint8_t v___x_4324_; 
v_newNode_4315_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4314_, v_x_4260_, v_x_4261_);
v___x_4323_ = ((size_t)7ULL);
v___x_4324_ = lean_usize_dec_le(v___x_4323_, v_x_4259_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4325_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4315_);
v___x_4326_ = lean_unsigned_to_nat(4u);
v___x_4327_ = lean_nat_dec_lt(v___x_4325_, v___x_4326_);
lean_dec(v___x_4325_);
v___y_4317_ = v___x_4327_;
goto v___jp_4316_;
}
else
{
v___y_4317_ = v___x_4324_;
goto v___jp_4316_;
}
v___jp_4316_:
{
if (v___y_4317_ == 0)
{
lean_object* v_ks_4318_; lean_object* v_vs_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_ks_4318_ = lean_ctor_get(v_newNode_4315_, 0);
lean_inc_ref(v_ks_4318_);
v_vs_4319_ = lean_ctor_get(v_newNode_4315_, 1);
lean_inc_ref(v_vs_4319_);
lean_dec_ref(v_newNode_4315_);
v___x_4320_ = lean_unsigned_to_nat(0u);
v___x_4321_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_4322_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4259_, v_ks_4318_, v_vs_4319_, v___x_4320_, v___x_4321_);
lean_dec_ref(v_vs_4319_);
lean_dec_ref(v_ks_4318_);
return v___x_4322_;
}
else
{
return v_newNode_4315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4330_, lean_object* v_keys_4331_, lean_object* v_vals_4332_, lean_object* v_i_4333_, lean_object* v_entries_4334_){
_start:
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = lean_array_get_size(v_keys_4331_);
v___x_4336_ = lean_nat_dec_lt(v_i_4333_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_dec(v_i_4333_);
return v_entries_4334_;
}
else
{
lean_object* v_k_4337_; lean_object* v_v_4338_; uint64_t v___x_4339_; size_t v_h_4340_; size_t v___x_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; size_t v___x_4345_; size_t v_h_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v_k_4337_ = lean_array_fget_borrowed(v_keys_4331_, v_i_4333_);
v_v_4338_ = lean_array_fget_borrowed(v_vals_4332_, v_i_4333_);
v___x_4339_ = l_Lean_instHashableMVarId_hash(v_k_4337_);
v_h_4340_ = lean_uint64_to_usize(v___x_4339_);
v___x_4341_ = ((size_t)5ULL);
v___x_4342_ = lean_unsigned_to_nat(1u);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_sub(v_depth_4330_, v___x_4343_);
v___x_4345_ = lean_usize_mul(v___x_4341_, v___x_4344_);
v_h_4346_ = lean_usize_shift_right(v_h_4340_, v___x_4345_);
v___x_4347_ = lean_nat_add(v_i_4333_, v___x_4342_);
lean_dec(v_i_4333_);
lean_inc(v_v_4338_);
lean_inc(v_k_4337_);
v___x_4348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4334_, v_h_4346_, v_depth_4330_, v_k_4337_, v_v_4338_);
v_i_4333_ = v___x_4347_;
v_entries_4334_ = v___x_4348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4350_, lean_object* v_keys_4351_, lean_object* v_vals_4352_, lean_object* v_i_4353_, lean_object* v_entries_4354_){
_start:
{
size_t v_depth_boxed_4355_; lean_object* v_res_4356_; 
v_depth_boxed_4355_ = lean_unbox_usize(v_depth_4350_);
lean_dec(v_depth_4350_);
v_res_4356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4355_, v_keys_4351_, v_vals_4352_, v_i_4353_, v_entries_4354_);
lean_dec_ref(v_vals_4352_);
lean_dec_ref(v_keys_4351_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4357_, lean_object* v_x_4358_, lean_object* v_x_4359_, lean_object* v_x_4360_, lean_object* v_x_4361_){
_start:
{
size_t v_x_4263__boxed_4362_; size_t v_x_4264__boxed_4363_; lean_object* v_res_4364_; 
v_x_4263__boxed_4362_ = lean_unbox_usize(v_x_4358_);
lean_dec(v_x_4358_);
v_x_4264__boxed_4363_ = lean_unbox_usize(v_x_4359_);
lean_dec(v_x_4359_);
v_res_4364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4357_, v_x_4263__boxed_4362_, v_x_4264__boxed_4363_, v_x_4360_, v_x_4361_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4365_, lean_object* v_x_4366_, lean_object* v_x_4367_){
_start:
{
uint64_t v___x_4368_; size_t v___x_4369_; size_t v___x_4370_; lean_object* v___x_4371_; 
v___x_4368_ = l_Lean_instHashableMVarId_hash(v_x_4366_);
v___x_4369_ = lean_uint64_to_usize(v___x_4368_);
v___x_4370_ = ((size_t)1ULL);
v___x_4371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4365_, v___x_4369_, v___x_4370_, v_x_4366_, v_x_4367_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4372_, lean_object* v_val_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; lean_object* v_mctx_4377_; lean_object* v_cache_4378_; lean_object* v_zetaDeltaFVarIds_4379_; lean_object* v_postponed_4380_; lean_object* v_diag_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4409_; 
v___x_4376_ = lean_st_ref_take(v___y_4374_);
v_mctx_4377_ = lean_ctor_get(v___x_4376_, 0);
v_cache_4378_ = lean_ctor_get(v___x_4376_, 1);
v_zetaDeltaFVarIds_4379_ = lean_ctor_get(v___x_4376_, 2);
v_postponed_4380_ = lean_ctor_get(v___x_4376_, 3);
v_diag_4381_ = lean_ctor_get(v___x_4376_, 4);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4383_ = v___x_4376_;
v_isShared_4384_ = v_isSharedCheck_4409_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_diag_4381_);
lean_inc(v_postponed_4380_);
lean_inc(v_zetaDeltaFVarIds_4379_);
lean_inc(v_cache_4378_);
lean_inc(v_mctx_4377_);
lean_dec(v___x_4376_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4409_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v_depth_4385_; lean_object* v_levelAssignDepth_4386_; lean_object* v_lmvarCounter_4387_; lean_object* v_mvarCounter_4388_; lean_object* v_lDecls_4389_; lean_object* v_decls_4390_; lean_object* v_userNames_4391_; lean_object* v_lAssignment_4392_; lean_object* v_eAssignment_4393_; lean_object* v_dAssignment_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4408_; 
v_depth_4385_ = lean_ctor_get(v_mctx_4377_, 0);
v_levelAssignDepth_4386_ = lean_ctor_get(v_mctx_4377_, 1);
v_lmvarCounter_4387_ = lean_ctor_get(v_mctx_4377_, 2);
v_mvarCounter_4388_ = lean_ctor_get(v_mctx_4377_, 3);
v_lDecls_4389_ = lean_ctor_get(v_mctx_4377_, 4);
v_decls_4390_ = lean_ctor_get(v_mctx_4377_, 5);
v_userNames_4391_ = lean_ctor_get(v_mctx_4377_, 6);
v_lAssignment_4392_ = lean_ctor_get(v_mctx_4377_, 7);
v_eAssignment_4393_ = lean_ctor_get(v_mctx_4377_, 8);
v_dAssignment_4394_ = lean_ctor_get(v_mctx_4377_, 9);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_mctx_4377_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4396_ = v_mctx_4377_;
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_dAssignment_4394_);
lean_inc(v_eAssignment_4393_);
lean_inc(v_lAssignment_4392_);
lean_inc(v_userNames_4391_);
lean_inc(v_decls_4390_);
lean_inc(v_lDecls_4389_);
lean_inc(v_mvarCounter_4388_);
lean_inc(v_lmvarCounter_4387_);
lean_inc(v_levelAssignDepth_4386_);
lean_inc(v_depth_4385_);
lean_dec(v_mctx_4377_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4393_, v_mvarId_4372_, v_val_4373_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 8, v___x_4398_);
v___x_4400_ = v___x_4396_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_depth_4385_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_levelAssignDepth_4386_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_lmvarCounter_4387_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_mvarCounter_4388_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_lDecls_4389_);
lean_ctor_set(v_reuseFailAlloc_4407_, 5, v_decls_4390_);
lean_ctor_set(v_reuseFailAlloc_4407_, 6, v_userNames_4391_);
lean_ctor_set(v_reuseFailAlloc_4407_, 7, v_lAssignment_4392_);
lean_ctor_set(v_reuseFailAlloc_4407_, 8, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4407_, 9, v_dAssignment_4394_);
v___x_4400_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4402_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4400_);
v___x_4402_ = v___x_4383_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_cache_4378_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_zetaDeltaFVarIds_4379_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_postponed_4380_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v_diag_4381_);
v___x_4402_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4403_ = lean_st_ref_set(v___y_4374_, v___x_4402_);
v___x_4404_ = lean_box(0);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4410_, lean_object* v_val_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4410_, v_val_4411_, v___y_4412_);
lean_dec(v___y_4412_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4419_, lean_object* v_mv_u2082_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4429_; 
lean_inc(v_mv_u2081_4419_);
v___x_4429_ = l_Lean_MVarId_getDecl(v_mv_u2081_4419_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4431_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref(v___x_4429_);
lean_inc(v_mv_u2082_4420_);
v___x_4431_ = l_Lean_MVarId_getDecl(v_mv_u2082_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v_lctx_4433_; lean_object* v_type_4434_; lean_object* v_lctx_4435_; lean_object* v_type_4436_; uint8_t v___x_4437_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref(v___x_4431_);
v_lctx_4433_ = lean_ctor_get(v_a_4430_, 1);
lean_inc_ref(v_lctx_4433_);
v_type_4434_ = lean_ctor_get(v_a_4430_, 2);
lean_inc_ref(v_type_4434_);
lean_dec(v_a_4430_);
v_lctx_4435_ = lean_ctor_get(v_a_4432_, 1);
lean_inc_ref(v_lctx_4435_);
v_type_4436_ = lean_ctor_get(v_a_4432_, 2);
lean_inc_ref(v_type_4436_);
lean_dec(v_a_4432_);
v___x_4437_ = lean_expr_eqv(v_type_4434_, v_type_4436_);
lean_dec_ref(v_type_4436_);
lean_dec_ref(v_type_4434_);
if (v___x_4437_ == 0)
{
lean_dec_ref(v_lctx_4435_);
lean_dec_ref(v_lctx_4433_);
lean_dec(v_mv_u2082_4420_);
lean_dec(v_mv_u2081_4419_);
goto v___jp_4426_;
}
else
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4439_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4433_, v_lctx_4435_, v___x_4438_);
if (v___x_4439_ == 0)
{
uint8_t v___x_4440_; 
v___x_4440_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4435_, v_lctx_4433_, v___x_4438_);
lean_dec_ref(v_lctx_4433_);
lean_dec_ref(v_lctx_4435_);
if (v___x_4440_ == 0)
{
lean_dec(v_mv_u2082_4420_);
lean_dec(v_mv_u2081_4419_);
goto v___jp_4426_;
}
else
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4452_; 
v___x_4441_ = l_Lean_Expr_mvar___override(v_mv_u2082_4420_);
v___x_4442_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4419_, v___x_4441_, v___y_4422_);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4452_ == 0)
{
lean_object* v_unused_4453_; 
v_unused_4453_ = lean_ctor_get(v___x_4442_, 0);
lean_dec(v_unused_4453_);
v___x_4444_ = v___x_4442_;
v_isShared_4445_ = v_isSharedCheck_4452_;
goto v_resetjp_4443_;
}
else
{
lean_dec(v___x_4442_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4452_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
v___x_4446_ = lean_box(v___x_4439_);
v___x_4447_ = lean_box(v___x_4437_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4446_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4448_);
v___x_4450_ = v___x_4444_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref(v_lctx_4435_);
lean_dec_ref(v_lctx_4433_);
v___x_4454_ = l_Lean_Expr_mvar___override(v_mv_u2081_4419_);
v___x_4455_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4420_, v___x_4454_, v___y_4422_);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4466_ == 0)
{
lean_object* v_unused_4467_; 
v_unused_4467_ = lean_ctor_get(v___x_4455_, 0);
lean_dec(v_unused_4467_);
v___x_4457_ = v___x_4455_;
v_isShared_4458_ = v_isSharedCheck_4466_;
goto v_resetjp_4456_;
}
else
{
lean_dec(v___x_4455_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4466_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
uint8_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4459_ = 0;
v___x_4460_ = lean_box(v___x_4437_);
v___x_4461_ = lean_box(v___x_4459_);
v___x_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4460_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4462_);
v___x_4464_ = v___x_4457_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_a_4430_);
lean_dec(v_mv_u2082_4420_);
lean_dec(v_mv_u2081_4419_);
v_a_4468_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4431_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4431_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec(v_mv_u2082_4420_);
lean_dec(v_mv_u2081_4419_);
v_a_4476_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4429_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4429_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
v___jp_4426_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
return v___x_4428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4484_, lean_object* v_mv_u2082_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4484_, v_mv_u2082_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4492_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4506_, lean_object* v_removed_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_b_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___y_4517_; uint8_t v___x_4540_; 
v___x_4540_ = lean_nat_dec_lt(v_a_4509_, v_upperBound_4506_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_dec(v_a_4509_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v_b_4510_);
return v___x_4541_;
}
else
{
uint8_t v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4542_ = 0;
v___x_4543_ = lean_box(v___x_4542_);
v___x_4544_ = lean_array_get(v___x_4543_, v_removed_4507_, v_a_4509_);
lean_dec(v___x_4543_);
v___x_4545_ = lean_unbox(v___x_4544_);
lean_dec(v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___f_4549_; 
v___x_4546_ = lean_array_fget_borrowed(v_a_4508_, v_a_4509_);
lean_inc(v___x_4546_);
v___x_4547_ = lean_array_push(v_b_4510_, v___x_4546_);
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
v___f_4549_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4549_, 0, v___x_4548_);
v___y_4517_ = v___f_4549_;
goto v___jp_4516_;
}
else
{
lean_object* v___x_4550_; lean_object* v___f_4551_; 
v___x_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4550_, 0, v_b_4510_);
v___f_4551_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4551_, 0, v___x_4550_);
v___y_4517_ = v___f_4551_;
goto v___jp_4516_;
}
}
v___jp_4516_:
{
lean_object* v___x_4518_; 
lean_inc(v___y_4514_);
lean_inc_ref(v___y_4513_);
lean_inc(v___y_4512_);
lean_inc_ref(v___y_4511_);
v___x_4518_ = lean_apply_5(v___y_4517_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, lean_box(0));
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4531_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4521_ = v___x_4518_;
v_isShared_4522_ = v_isSharedCheck_4531_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4531_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
if (lean_obj_tag(v_a_4519_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4525_; 
lean_dec(v_a_4509_);
v_a_4523_ = lean_ctor_get(v_a_4519_, 0);
lean_inc(v_a_4523_);
lean_dec_ref(v_a_4519_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 0, v_a_4523_);
v___x_4525_ = v___x_4521_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_del_object(v___x_4521_);
v_a_4527_ = lean_ctor_get(v_a_4519_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v_a_4519_);
v___x_4528_ = lean_unsigned_to_nat(1u);
v___x_4529_ = lean_nat_add(v_a_4509_, v___x_4528_);
lean_dec(v_a_4509_);
v_a_4509_ = v___x_4529_;
v_b_4510_ = v_a_4527_;
goto _start;
}
}
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_dec(v_a_4509_);
v_a_4532_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4518_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4518_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4552_, lean_object* v_removed_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_b_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4552_, v_removed_4553_, v_a_4554_, v_a_4555_, v_b_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec_ref(v_a_4554_);
lean_dec_ref(v_removed_4553_);
lean_dec(v_upperBound_4552_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4563_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4577_, lean_object* v___x_4578_, lean_object* v___x_4579_, lean_object* v___x_4580_, lean_object* v_a_4581_, uint8_t v___x_4582_, lean_object* v_snd_4583_, lean_object* v_fst_4584_, lean_object* v_next_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_apply_7(v_f_4577_, v___x_4578_, v___x_4579_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, lean_box(0));
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4627_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4627_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4627_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v_fst_4596_; lean_object* v_snd_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4626_; 
v_fst_4596_ = lean_ctor_get(v_a_4592_, 0);
v_snd_4597_ = lean_ctor_get(v_a_4592_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_a_4592_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4599_ = v_a_4592_;
v_isShared_4600_ = v_isSharedCheck_4626_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_snd_4597_);
lean_inc(v_fst_4596_);
lean_dec(v_a_4592_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4626_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v_removed_4602_; lean_object* v_numRemoved_4603_; uint8_t v___x_4622_; 
v___x_4622_ = lean_unbox(v_fst_4596_);
lean_dec(v_fst_4596_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = lean_nat_add(v_snd_4583_, v___x_4580_);
lean_dec(v_snd_4583_);
v___x_4624_ = lean_box(v___x_4582_);
v___x_4625_ = lean_array_set(v_fst_4584_, v_next_4585_, v___x_4624_);
v_removed_4602_ = v___x_4625_;
v_numRemoved_4603_ = v___x_4623_;
goto v___jp_4601_;
}
else
{
v_removed_4602_ = v_fst_4584_;
v_numRemoved_4603_ = v_snd_4583_;
goto v___jp_4601_;
}
v___jp_4601_:
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_unbox(v_snd_4597_);
lean_dec(v_snd_4597_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4605_ = lean_nat_add(v_numRemoved_4603_, v___x_4580_);
lean_dec(v_numRemoved_4603_);
v___x_4606_ = lean_box(v___x_4582_);
v___x_4607_ = lean_array_set(v_removed_4602_, v_a_4581_, v___x_4606_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 1, v___x_4605_);
lean_ctor_set(v___x_4599_, 0, v___x_4607_);
v___x_4609_ = v___x_4599_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4614_, 1, v___x_4605_);
v___x_4609_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4610_);
v___x_4612_ = v___x_4594_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
else
{
lean_object* v___x_4616_; 
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 1, v_numRemoved_4603_);
lean_ctor_set(v___x_4599_, 0, v_removed_4602_);
v___x_4616_ = v___x_4599_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_removed_4602_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_numRemoved_4603_);
v___x_4616_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4617_);
v___x_4619_ = v___x_4594_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_fst_4584_);
lean_dec(v_snd_4583_);
v_a_4628_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4591_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4591_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4636_, lean_object* v___x_4637_, lean_object* v___x_4638_, lean_object* v___x_4639_, lean_object* v_a_4640_, lean_object* v___x_4641_, lean_object* v_snd_4642_, lean_object* v_fst_4643_, lean_object* v_next_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___x_4756__boxed_4650_; lean_object* v_res_4651_; 
v___x_4756__boxed_4650_ = lean_unbox(v___x_4641_);
v_res_4651_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4636_, v___x_4637_, v___x_4638_, v___x_4639_, v_a_4640_, v___x_4756__boxed_4650_, v_snd_4642_, v_fst_4643_, v_next_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v_next_4644_);
lean_dec(v_a_4640_);
lean_dec(v___x_4639_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4652_, lean_object* v_a_4653_, lean_object* v_next_4654_, lean_object* v_f_4655_, lean_object* v_a_4656_, lean_object* v_b_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
uint8_t v___x_4663_; 
v___x_4663_ = lean_nat_dec_lt(v_a_4656_, v_upperBound_4652_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; 
lean_dec(v_a_4656_);
lean_dec_ref(v_f_4655_);
lean_dec(v_next_4654_);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v_b_4657_);
return v___x_4664_;
}
else
{
lean_object* v_fst_4665_; lean_object* v_snd_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4713_; 
v_fst_4665_ = lean_ctor_get(v_b_4657_, 0);
v_snd_4666_ = lean_ctor_get(v_b_4657_, 1);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_b_4657_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4668_ = v_b_4657_;
v_isShared_4669_ = v_isSharedCheck_4713_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_snd_4666_);
lean_inc(v_fst_4665_);
lean_dec(v_b_4657_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4713_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___y_4672_; uint8_t v___y_4695_; uint8_t v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4670_ = lean_unsigned_to_nat(1u);
v___x_4705_ = 0;
v___x_4706_ = lean_box(v___x_4705_);
v___x_4707_ = lean_array_get(v___x_4706_, v_fst_4665_, v_next_4654_);
lean_dec(v___x_4706_);
v___x_4708_ = lean_unbox(v___x_4707_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; 
lean_dec(v___x_4707_);
v___x_4709_ = lean_box(v___x_4705_);
v___x_4710_ = lean_array_get(v___x_4709_, v_fst_4665_, v_a_4656_);
lean_dec(v___x_4709_);
v___x_4711_ = lean_unbox(v___x_4710_);
lean_dec(v___x_4710_);
v___y_4695_ = v___x_4711_;
goto v___jp_4694_;
}
else
{
uint8_t v___x_4712_; 
v___x_4712_ = lean_unbox(v___x_4707_);
lean_dec(v___x_4707_);
v___y_4695_ = v___x_4712_;
goto v___jp_4694_;
}
v___jp_4671_:
{
lean_object* v___x_4673_; 
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
lean_inc(v___y_4659_);
lean_inc_ref(v___y_4658_);
v___x_4673_ = lean_apply_5(v___y_4672_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, lean_box(0));
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4685_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4685_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4685_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
if (lean_obj_tag(v_a_4674_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; 
lean_dec(v_a_4656_);
lean_dec_ref(v_f_4655_);
lean_dec(v_next_4654_);
v_a_4678_ = lean_ctor_get(v_a_4674_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v_a_4674_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v_a_4678_);
v___x_4680_ = v___x_4676_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4683_; 
lean_del_object(v___x_4676_);
v_a_4682_ = lean_ctor_get(v_a_4674_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v_a_4674_);
v___x_4683_ = lean_nat_add(v_a_4656_, v___x_4670_);
lean_dec(v_a_4656_);
v_a_4656_ = v___x_4683_;
v_b_4657_ = v_a_4682_;
goto _start;
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_a_4656_);
lean_dec_ref(v_f_4655_);
lean_dec(v_next_4654_);
v_a_4686_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4673_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4673_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
v___jp_4694_:
{
if (v___y_4695_ == 0)
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___f_4699_; 
lean_del_object(v___x_4668_);
v___x_4696_ = lean_array_fget_borrowed(v_a_4653_, v_next_4654_);
v___x_4697_ = lean_array_fget_borrowed(v_a_4653_, v_a_4656_);
v___x_4698_ = lean_box(v___x_4663_);
lean_inc(v_next_4654_);
lean_inc(v_a_4656_);
lean_inc(v___x_4697_);
lean_inc(v___x_4696_);
lean_inc_ref(v_f_4655_);
v___f_4699_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4699_, 0, v_f_4655_);
lean_closure_set(v___f_4699_, 1, v___x_4696_);
lean_closure_set(v___f_4699_, 2, v___x_4697_);
lean_closure_set(v___f_4699_, 3, v___x_4670_);
lean_closure_set(v___f_4699_, 4, v_a_4656_);
lean_closure_set(v___f_4699_, 5, v___x_4698_);
lean_closure_set(v___f_4699_, 6, v_snd_4666_);
lean_closure_set(v___f_4699_, 7, v_fst_4665_);
lean_closure_set(v___f_4699_, 8, v_next_4654_);
v___y_4672_ = v___f_4699_;
goto v___jp_4671_;
}
else
{
lean_object* v___x_4701_; 
if (v_isShared_4669_ == 0)
{
v___x_4701_ = v___x_4668_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_fst_4665_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_snd_4666_);
v___x_4701_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___f_4703_; 
v___x_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
v___f_4703_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4703_, 0, v___x_4702_);
v___y_4672_ = v___f_4703_;
goto v___jp_4671_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4714_, lean_object* v_a_4715_, lean_object* v_next_4716_, lean_object* v_f_4717_, lean_object* v_a_4718_, lean_object* v_b_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4714_, v_a_4715_, v_next_4716_, v_f_4717_, v_a_4718_, v_b_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec_ref(v_a_4715_);
lean_dec(v_upperBound_4714_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4726_, lean_object* v___x_4727_, lean_object* v_a_4728_, lean_object* v_f_4729_, lean_object* v_a_4730_, lean_object* v_b_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_nat_dec_lt(v_a_4730_, v_upperBound_4726_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; 
lean_dec(v_a_4730_);
lean_dec_ref(v_f_4729_);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v_b_4731_);
return v___x_4738_;
}
else
{
lean_object* v_fst_4739_; lean_object* v_snd_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4761_; 
v_fst_4739_ = lean_ctor_get(v_b_4731_, 0);
v_snd_4740_ = lean_ctor_get(v_b_4731_, 1);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_b_4731_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4742_ = v_b_4731_;
v_isShared_4743_ = v_isSharedCheck_4761_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_snd_4740_);
lean_inc(v_fst_4739_);
lean_dec(v_b_4731_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4761_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4744_ = lean_unsigned_to_nat(1u);
v___x_4745_ = lean_nat_add(v_a_4730_, v___x_4744_);
if (v_isShared_4743_ == 0)
{
v___x_4747_ = v___x_4742_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_fst_4739_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_snd_4740_);
v___x_4747_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4748_; 
lean_inc(v___x_4745_);
lean_inc_ref(v_f_4729_);
v___x_4748_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4727_, v_a_4728_, v_a_4730_, v_f_4729_, v___x_4745_, v___x_4747_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v_fst_4750_; lean_object* v_snd_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4759_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref(v___x_4748_);
v_fst_4750_ = lean_ctor_get(v_a_4749_, 0);
v_snd_4751_ = lean_ctor_get(v_a_4749_, 1);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_a_4749_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4753_ = v_a_4749_;
v_isShared_4754_ = v_isSharedCheck_4759_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_snd_4751_);
lean_inc(v_fst_4750_);
lean_dec(v_a_4749_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4759_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_fst_4750_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_snd_4751_);
v___x_4756_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
v_a_4730_ = v___x_4745_;
v_b_4731_ = v___x_4756_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4745_);
lean_dec_ref(v_f_4729_);
return v___x_4748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4762_, lean_object* v___x_4763_, lean_object* v_a_4764_, lean_object* v_f_4765_, lean_object* v_a_4766_, lean_object* v_b_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4762_, v___x_4763_, v_a_4764_, v_f_4765_, v_a_4766_, v_b_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec_ref(v_a_4764_);
lean_dec(v___x_4763_);
lean_dec(v_upperBound_4762_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4774_, lean_object* v_f_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v_removed_4784_; lean_object* v_numRemoved_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4781_ = lean_array_get_size(v_a_4774_);
v___x_4782_ = 0;
v___x_4783_ = lean_box(v___x_4782_);
v_removed_4784_ = lean_mk_array(v___x_4781_, v___x_4783_);
v_numRemoved_4785_ = lean_unsigned_to_nat(0u);
v___x_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4786_, 0, v_removed_4784_);
lean_ctor_set(v___x_4786_, 1, v_numRemoved_4785_);
v___x_4787_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4781_, v___x_4781_, v_a_4774_, v_f_4775_, v_numRemoved_4785_, v___x_4786_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v_fst_4789_; lean_object* v_snd_4790_; lean_object* v_a_x27_4791_; lean_object* v___x_4792_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref(v___x_4787_);
v_fst_4789_ = lean_ctor_get(v_a_4788_, 0);
lean_inc(v_fst_4789_);
v_snd_4790_ = lean_ctor_get(v_a_4788_, 1);
lean_inc(v_snd_4790_);
lean_dec(v_a_4788_);
v_a_x27_4791_ = lean_mk_empty_array_with_capacity(v_snd_4790_);
lean_dec(v_snd_4790_);
v___x_4792_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4781_, v_fst_4789_, v_a_4774_, v_numRemoved_4785_, v_a_x27_4791_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v_fst_4789_);
return v___x_4792_;
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_a_4793_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4787_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4787_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4801_, lean_object* v_f_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4801_, v_f_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec_ref(v_a_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v___f_4816_; lean_object* v___x_4817_; 
v___f_4816_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4817_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4810_, v___f_4816_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
lean_dec(v_a_4822_);
lean_dec_ref(v_a_4821_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec_ref(v_mvars_4818_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4825_, lean_object* v_val_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4825_, v_val_4826_, v___y_4828_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4833_, lean_object* v_val_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4833_, v_val_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4841_, lean_object* v_a_4842_, lean_object* v_f_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4842_, v_f_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_a_4851_, lean_object* v_f_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4850_, v_a_4851_, v_f_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec_ref(v_a_4851_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4859_, lean_object* v_x_4860_, lean_object* v_x_4861_, lean_object* v_x_4862_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4860_, v_x_4861_, v_x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4864_, lean_object* v_00_u03b1_4865_, lean_object* v_a_4866_, lean_object* v_next_4867_, lean_object* v_f_4868_, lean_object* v_inst_4869_, lean_object* v_R_4870_, lean_object* v_a_4871_, lean_object* v_b_4872_, lean_object* v_c_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4864_, v_a_4866_, v_next_4867_, v_f_4868_, v_a_4871_, v_b_4872_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4880_, lean_object* v_00_u03b1_4881_, lean_object* v_a_4882_, lean_object* v_next_4883_, lean_object* v_f_4884_, lean_object* v_inst_4885_, lean_object* v_R_4886_, lean_object* v_a_4887_, lean_object* v_b_4888_, lean_object* v_c_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4880_, v_00_u03b1_4881_, v_a_4882_, v_next_4883_, v_f_4884_, v_inst_4885_, v_R_4886_, v_a_4887_, v_b_4888_, v_c_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v_a_4882_);
lean_dec(v_upperBound_4880_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4896_, lean_object* v_upperBound_4897_, lean_object* v_removed_4898_, lean_object* v_a_4899_, lean_object* v_inst_4900_, lean_object* v_R_4901_, lean_object* v_a_4902_, lean_object* v_b_4903_, lean_object* v_c_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4897_, v_removed_4898_, v_a_4899_, v_a_4902_, v_b_4903_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4911_, lean_object* v_upperBound_4912_, lean_object* v_removed_4913_, lean_object* v_a_4914_, lean_object* v_inst_4915_, lean_object* v_R_4916_, lean_object* v_a_4917_, lean_object* v_b_4918_, lean_object* v_c_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4911_, v_upperBound_4912_, v_removed_4913_, v_a_4914_, v_inst_4915_, v_R_4916_, v_a_4917_, v_b_4918_, v_c_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec_ref(v_a_4914_);
lean_dec_ref(v_removed_4913_);
lean_dec(v_upperBound_4912_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4926_, lean_object* v___x_4927_, lean_object* v_00_u03b1_4928_, lean_object* v_a_4929_, lean_object* v_f_4930_, lean_object* v_inst_4931_, lean_object* v_R_4932_, lean_object* v_a_4933_, lean_object* v_b_4934_, lean_object* v_c_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4926_, v___x_4927_, v_a_4929_, v_f_4930_, v_a_4933_, v_b_4934_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4942_, lean_object* v___x_4943_, lean_object* v_00_u03b1_4944_, lean_object* v_a_4945_, lean_object* v_f_4946_, lean_object* v_inst_4947_, lean_object* v_R_4948_, lean_object* v_a_4949_, lean_object* v_b_4950_, lean_object* v_c_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4942_, v___x_4943_, v_00_u03b1_4944_, v_a_4945_, v_f_4946_, v_inst_4947_, v_R_4948_, v_a_4949_, v_b_4950_, v_c_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec_ref(v_a_4945_);
lean_dec(v___x_4943_);
lean_dec(v_upperBound_4942_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4958_, lean_object* v_x_4959_, size_t v_x_4960_, size_t v_x_4961_, lean_object* v_x_4962_, lean_object* v_x_4963_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4959_, v_x_4960_, v_x_4961_, v_x_4962_, v_x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4965_, lean_object* v_x_4966_, lean_object* v_x_4967_, lean_object* v_x_4968_, lean_object* v_x_4969_, lean_object* v_x_4970_){
_start:
{
size_t v_x_5216__boxed_4971_; size_t v_x_5217__boxed_4972_; lean_object* v_res_4973_; 
v_x_5216__boxed_4971_ = lean_unbox_usize(v_x_4967_);
lean_dec(v_x_4967_);
v_x_5217__boxed_4972_ = lean_unbox_usize(v_x_4968_);
lean_dec(v_x_4968_);
v_res_4973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4965_, v_x_4966_, v_x_5216__boxed_4971_, v_x_5217__boxed_4972_, v_x_4969_, v_x_4970_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4974_, lean_object* v_n_4975_, lean_object* v_k_4976_, lean_object* v_v_4977_){
_start:
{
lean_object* v___x_4978_; 
v___x_4978_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4975_, v_k_4976_, v_v_4977_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4979_, size_t v_depth_4980_, lean_object* v_keys_4981_, lean_object* v_vals_4982_, lean_object* v_heq_4983_, lean_object* v_i_4984_, lean_object* v_entries_4985_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4980_, v_keys_4981_, v_vals_4982_, v_i_4984_, v_entries_4985_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4987_, lean_object* v_depth_4988_, lean_object* v_keys_4989_, lean_object* v_vals_4990_, lean_object* v_heq_4991_, lean_object* v_i_4992_, lean_object* v_entries_4993_){
_start:
{
size_t v_depth_boxed_4994_; lean_object* v_res_4995_; 
v_depth_boxed_4994_ = lean_unbox_usize(v_depth_4988_);
lean_dec(v_depth_4988_);
v_res_4995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4987_, v_depth_boxed_4994_, v_keys_4989_, v_vals_4990_, v_heq_4991_, v_i_4992_, v_entries_4993_);
lean_dec_ref(v_vals_4990_);
lean_dec_ref(v_keys_4989_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4996_, lean_object* v_x_4997_, lean_object* v_x_4998_, lean_object* v_x_4999_, lean_object* v_x_5000_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4997_, v_x_4998_, v_x_4999_, v_x_5000_);
return v___x_5001_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5004_ = l_Lean_stringToMessageData(v___x_5003_);
return v___x_5004_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5008_, lean_object* v_as_5009_, size_t v_sz_5010_, size_t v_i_5011_, lean_object* v_b_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v_a_5019_; uint8_t v___x_5023_; 
v___x_5023_ = lean_usize_dec_lt(v_i_5011_, v_sz_5010_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; 
v___x_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5024_, 0, v_b_5012_);
return v___x_5024_;
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5026_; 
v_a_5025_ = lean_array_uget_borrowed(v_as_5009_, v_i_5011_);
lean_inc(v_a_5025_);
v___x_5026_ = l_Lean_MVarId_getType(v_a_5025_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___y_5029_; lean_object* v___y_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref(v___x_5026_);
if (lean_obj_tag(v_a_5027_) == 10)
{
lean_object* v_expr_5045_; 
v_expr_5045_ = lean_ctor_get(v_a_5027_, 1);
if (lean_obj_tag(v_expr_5045_) == 5)
{
lean_object* v_arg_5046_; lean_object* v___x_5047_; 
lean_inc_ref(v_expr_5045_);
lean_dec_ref(v_a_5027_);
v_arg_5046_ = lean_ctor_get(v_expr_5045_, 1);
lean_inc_ref_n(v_arg_5046_, 2);
lean_dec_ref(v_expr_5045_);
v___x_5047_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5008_, v_arg_5046_);
if (lean_obj_tag(v___x_5047_) == 1)
{
lean_object* v_val_5048_; lean_object* v_fst_5049_; lean_object* v___x_5050_; uint8_t v___x_5051_; 
lean_dec_ref(v_arg_5046_);
v_val_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_val_5048_);
lean_dec_ref(v___x_5047_);
v_fst_5049_ = lean_ctor_get(v_val_5048_, 0);
lean_inc(v_fst_5049_);
lean_dec(v_val_5048_);
v___x_5050_ = lean_array_get_size(v_b_5012_);
v___x_5051_ = lean_nat_dec_lt(v_fst_5049_, v___x_5050_);
if (v___x_5051_ == 0)
{
lean_dec(v_fst_5049_);
v_a_5019_ = v_b_5012_;
goto v___jp_5018_;
}
else
{
lean_object* v_v_5052_; lean_object* v___x_5053_; lean_object* v_xs_x27_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_v_5052_ = lean_array_fget(v_b_5012_, v_fst_5049_);
v___x_5053_ = lean_box(0);
v_xs_x27_5054_ = lean_array_fset(v_b_5012_, v_fst_5049_, v___x_5053_);
lean_inc(v_a_5025_);
v___x_5055_ = lean_array_push(v_v_5052_, v_a_5025_);
v___x_5056_ = lean_array_fset(v_xs_x27_5054_, v_fst_5049_, v___x_5055_);
lean_dec(v_fst_5049_);
v_a_5019_ = v___x_5056_;
goto v___jp_5018_;
}
}
else
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_dec(v___x_5047_);
v___x_5057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5058_ = l_Lean_indentExpr(v_arg_5046_);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5057_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5059_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_dec_ref(v___x_5060_);
v_a_5019_ = v_b_5012_;
goto v___jp_5018_;
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_dec_ref(v_b_5012_);
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
else
{
v___y_5029_ = v___y_5013_;
v___y_5030_ = v___y_5014_;
v___y_5031_ = v___y_5015_;
v___y_5032_ = v___y_5016_;
goto v___jp_5028_;
}
}
else
{
v___y_5029_ = v___y_5013_;
v___y_5030_ = v___y_5014_;
v___y_5031_ = v___y_5015_;
v___y_5032_ = v___y_5016_;
goto v___jp_5028_;
}
v___jp_5028_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5034_ = l_Lean_indentExpr(v_a_5027_);
v___x_5035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5033_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
v___x_5036_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5035_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_dec_ref(v___x_5036_);
v_a_5019_ = v_b_5012_;
goto v___jp_5018_;
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
lean_dec_ref(v_b_5012_);
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref(v_b_5012_);
v_a_5069_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5026_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5026_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
v___jp_5018_:
{
size_t v___x_5020_; size_t v___x_5021_; 
v___x_5020_ = ((size_t)1ULL);
v___x_5021_ = lean_usize_add(v_i_5011_, v___x_5020_);
v_i_5011_ = v___x_5021_;
v_b_5012_ = v_a_5019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5077_, lean_object* v_as_5078_, lean_object* v_sz_5079_, lean_object* v_i_5080_, lean_object* v_b_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
size_t v_sz_boxed_5087_; size_t v_i_boxed_5088_; lean_object* v_res_5089_; 
v_sz_boxed_5087_ = lean_unbox_usize(v_sz_5079_);
lean_dec(v_sz_5079_);
v_i_boxed_5088_ = lean_unbox_usize(v_i_5080_);
lean_dec(v_i_5080_);
v_res_5089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5077_, v_as_5078_, v_sz_boxed_5087_, v_i_boxed_5088_, v_b_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec_ref(v_as_5078_);
lean_dec_ref(v_argsPacker_5077_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5090_, lean_object* v_numFuncs_5091_, lean_object* v_goals_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_){
_start:
{
lean_object* v___x_5098_; lean_object* v_r_5099_; size_t v_sz_5100_; size_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5098_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5099_ = lean_mk_array(v_numFuncs_5091_, v___x_5098_);
v_sz_5100_ = lean_array_size(v_goals_5092_);
v___x_5101_ = ((size_t)0ULL);
v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5090_, v_goals_5092_, v_sz_5100_, v___x_5101_, v_r_5099_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5103_, lean_object* v_numFuncs_5104_, lean_object* v_goals_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5103_, v_numFuncs_5104_, v_goals_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec_ref(v_goals_5105_);
lean_dec_ref(v_argsPacker_5103_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v___x_5115_; lean_object* v_infoState_5116_; uint8_t v_enabled_5117_; 
v___x_5115_ = lean_st_ref_get(v___y_5113_);
v_infoState_5116_ = lean_ctor_get(v___x_5115_, 7);
lean_inc_ref(v_infoState_5116_);
lean_dec(v___x_5115_);
v_enabled_5117_ = lean_ctor_get_uint8(v_infoState_5116_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5116_);
if (v_enabled_5117_ == 0)
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
lean_dec_ref(v_t_5112_);
v___x_5118_ = lean_box(0);
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5118_);
return v___x_5119_;
}
else
{
lean_object* v___x_5120_; lean_object* v_infoState_5121_; lean_object* v_env_5122_; lean_object* v_nextMacroScope_5123_; lean_object* v_ngen_5124_; lean_object* v_auxDeclNGen_5125_; lean_object* v_traceState_5126_; lean_object* v_cache_5127_; lean_object* v_messages_5128_; lean_object* v_snapshotTasks_5129_; lean_object* v_newDecls_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5152_; 
v___x_5120_ = lean_st_ref_take(v___y_5113_);
v_infoState_5121_ = lean_ctor_get(v___x_5120_, 7);
v_env_5122_ = lean_ctor_get(v___x_5120_, 0);
v_nextMacroScope_5123_ = lean_ctor_get(v___x_5120_, 1);
v_ngen_5124_ = lean_ctor_get(v___x_5120_, 2);
v_auxDeclNGen_5125_ = lean_ctor_get(v___x_5120_, 3);
v_traceState_5126_ = lean_ctor_get(v___x_5120_, 4);
v_cache_5127_ = lean_ctor_get(v___x_5120_, 5);
v_messages_5128_ = lean_ctor_get(v___x_5120_, 6);
v_snapshotTasks_5129_ = lean_ctor_get(v___x_5120_, 8);
v_newDecls_5130_ = lean_ctor_get(v___x_5120_, 9);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5132_ = v___x_5120_;
v_isShared_5133_ = v_isSharedCheck_5152_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_newDecls_5130_);
lean_inc(v_snapshotTasks_5129_);
lean_inc(v_infoState_5121_);
lean_inc(v_messages_5128_);
lean_inc(v_cache_5127_);
lean_inc(v_traceState_5126_);
lean_inc(v_auxDeclNGen_5125_);
lean_inc(v_ngen_5124_);
lean_inc(v_nextMacroScope_5123_);
lean_inc(v_env_5122_);
lean_dec(v___x_5120_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5152_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
uint8_t v_enabled_5134_; lean_object* v_assignment_5135_; lean_object* v_lazyAssignment_5136_; lean_object* v_trees_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5151_; 
v_enabled_5134_ = lean_ctor_get_uint8(v_infoState_5121_, sizeof(void*)*3);
v_assignment_5135_ = lean_ctor_get(v_infoState_5121_, 0);
v_lazyAssignment_5136_ = lean_ctor_get(v_infoState_5121_, 1);
v_trees_5137_ = lean_ctor_get(v_infoState_5121_, 2);
v_isSharedCheck_5151_ = !lean_is_exclusive(v_infoState_5121_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5139_ = v_infoState_5121_;
v_isShared_5140_ = v_isSharedCheck_5151_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_trees_5137_);
lean_inc(v_lazyAssignment_5136_);
lean_inc(v_assignment_5135_);
lean_dec(v_infoState_5121_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5151_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
v___x_5141_ = l_Lean_PersistentArray_push___redArg(v_trees_5137_, v_t_5112_);
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 2, v___x_5141_);
v___x_5143_ = v___x_5139_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_assignment_5135_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_lazyAssignment_5136_);
lean_ctor_set(v_reuseFailAlloc_5150_, 2, v___x_5141_);
lean_ctor_set_uint8(v_reuseFailAlloc_5150_, sizeof(void*)*3, v_enabled_5134_);
v___x_5143_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___x_5145_; 
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 7, v___x_5143_);
v___x_5145_ = v___x_5132_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_env_5122_);
lean_ctor_set(v_reuseFailAlloc_5149_, 1, v_nextMacroScope_5123_);
lean_ctor_set(v_reuseFailAlloc_5149_, 2, v_ngen_5124_);
lean_ctor_set(v_reuseFailAlloc_5149_, 3, v_auxDeclNGen_5125_);
lean_ctor_set(v_reuseFailAlloc_5149_, 4, v_traceState_5126_);
lean_ctor_set(v_reuseFailAlloc_5149_, 5, v_cache_5127_);
lean_ctor_set(v_reuseFailAlloc_5149_, 6, v_messages_5128_);
lean_ctor_set(v_reuseFailAlloc_5149_, 7, v___x_5143_);
lean_ctor_set(v_reuseFailAlloc_5149_, 8, v_snapshotTasks_5129_);
lean_ctor_set(v_reuseFailAlloc_5149_, 9, v_newDecls_5130_);
v___x_5145_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5146_ = lean_st_ref_set(v___y_5113_, v___x_5145_);
v___x_5147_ = lean_box(0);
v___x_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5148_, 0, v___x_5147_);
return v___x_5148_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5153_, v___y_5154_);
lean_dec(v___y_5154_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5157_, v___y_5163_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5175_, lean_object* v___y_5176_){
_start:
{
uint8_t v___x_5178_; 
v___x_5178_ = l_Lean_Expr_hasMVar(v_e_5175_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; 
v___x_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5179_, 0, v_e_5175_);
return v___x_5179_;
}
else
{
lean_object* v___x_5180_; lean_object* v_mctx_5181_; lean_object* v___x_5182_; lean_object* v_fst_5183_; lean_object* v_snd_5184_; lean_object* v___x_5185_; lean_object* v_cache_5186_; lean_object* v_zetaDeltaFVarIds_5187_; lean_object* v_postponed_5188_; lean_object* v_diag_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5198_; 
v___x_5180_ = lean_st_ref_get(v___y_5176_);
v_mctx_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc_ref(v_mctx_5181_);
lean_dec(v___x_5180_);
v___x_5182_ = l_Lean_instantiateMVarsCore(v_mctx_5181_, v_e_5175_);
v_fst_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_fst_5183_);
v_snd_5184_ = lean_ctor_get(v___x_5182_, 1);
lean_inc(v_snd_5184_);
lean_dec_ref(v___x_5182_);
v___x_5185_ = lean_st_ref_take(v___y_5176_);
v_cache_5186_ = lean_ctor_get(v___x_5185_, 1);
v_zetaDeltaFVarIds_5187_ = lean_ctor_get(v___x_5185_, 2);
v_postponed_5188_ = lean_ctor_get(v___x_5185_, 3);
v_diag_5189_ = lean_ctor_get(v___x_5185_, 4);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5198_ == 0)
{
lean_object* v_unused_5199_; 
v_unused_5199_ = lean_ctor_get(v___x_5185_, 0);
lean_dec(v_unused_5199_);
v___x_5191_ = v___x_5185_;
v_isShared_5192_ = v_isSharedCheck_5198_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_diag_5189_);
lean_inc(v_postponed_5188_);
lean_inc(v_zetaDeltaFVarIds_5187_);
lean_inc(v_cache_5186_);
lean_dec(v___x_5185_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5198_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 0, v_snd_5184_);
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_snd_5184_);
lean_ctor_set(v_reuseFailAlloc_5197_, 1, v_cache_5186_);
lean_ctor_set(v_reuseFailAlloc_5197_, 2, v_zetaDeltaFVarIds_5187_);
lean_ctor_set(v_reuseFailAlloc_5197_, 3, v_postponed_5188_);
lean_ctor_set(v_reuseFailAlloc_5197_, 4, v_diag_5189_);
v___x_5194_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5195_ = lean_st_ref_set(v___y_5176_, v___x_5194_);
v___x_5196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5196_, 0, v_fst_5183_);
return v___x_5196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5200_, v___y_5201_);
lean_dec(v___y_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5204_, v___y_5206_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5218_, size_t v_i_5219_, size_t v_stop_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
uint8_t v___x_5229_; 
v___x_5229_ = lean_usize_dec_eq(v_i_5219_, v_stop_5220_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
v___x_5230_ = lean_array_uget_borrowed(v_as_5218_, v_i_5219_);
lean_inc(v___x_5230_);
v___x_5231_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
v___x_5232_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5231_, v___y_5227_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; size_t v___x_5234_; size_t v___x_5235_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref(v___x_5232_);
v___x_5234_ = ((size_t)1ULL);
v___x_5235_ = lean_usize_add(v_i_5219_, v___x_5234_);
v_i_5219_ = v___x_5235_;
v_b_5221_ = v_a_5233_;
goto _start;
}
else
{
return v___x_5232_;
}
}
else
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5237_, 0, v_b_5221_);
return v___x_5237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5238_, lean_object* v_i_5239_, lean_object* v_stop_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
size_t v_i_boxed_5249_; size_t v_stop_boxed_5250_; lean_object* v_res_5251_; 
v_i_boxed_5249_ = lean_unbox_usize(v_i_5239_);
lean_dec(v_i_5239_);
v_stop_boxed_5250_ = lean_unbox_usize(v_stop_5240_);
lean_dec(v_stop_5240_);
v_res_5251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5238_, v_i_boxed_5249_, v_stop_boxed_5250_, v_b_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec_ref(v_as_5238_);
return v_res_5251_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5252_ = lean_unsigned_to_nat(32u);
v___x_5253_ = lean_mk_empty_array_with_capacity(v___x_5252_);
v___x_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5253_);
return v___x_5254_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5255_ = ((size_t)5ULL);
v___x_5256_ = lean_unsigned_to_nat(0u);
v___x_5257_ = lean_unsigned_to_nat(32u);
v___x_5258_ = lean_mk_empty_array_with_capacity(v___x_5257_);
v___x_5259_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5260_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
lean_ctor_set(v___x_5260_, 1, v___x_5258_);
lean_ctor_set(v___x_5260_, 2, v___x_5256_);
lean_ctor_set(v___x_5260_, 3, v___x_5256_);
lean_ctor_set_usize(v___x_5260_, 4, v___x_5255_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5261_){
_start:
{
lean_object* v___x_5263_; lean_object* v_infoState_5264_; lean_object* v_trees_5265_; lean_object* v___x_5266_; lean_object* v_infoState_5267_; lean_object* v_env_5268_; lean_object* v_nextMacroScope_5269_; lean_object* v_ngen_5270_; lean_object* v_auxDeclNGen_5271_; lean_object* v_traceState_5272_; lean_object* v_cache_5273_; lean_object* v_messages_5274_; lean_object* v_snapshotTasks_5275_; lean_object* v_newDecls_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5297_; 
v___x_5263_ = lean_st_ref_get(v___y_5261_);
v_infoState_5264_ = lean_ctor_get(v___x_5263_, 7);
lean_inc_ref(v_infoState_5264_);
lean_dec(v___x_5263_);
v_trees_5265_ = lean_ctor_get(v_infoState_5264_, 2);
lean_inc_ref(v_trees_5265_);
lean_dec_ref(v_infoState_5264_);
v___x_5266_ = lean_st_ref_take(v___y_5261_);
v_infoState_5267_ = lean_ctor_get(v___x_5266_, 7);
v_env_5268_ = lean_ctor_get(v___x_5266_, 0);
v_nextMacroScope_5269_ = lean_ctor_get(v___x_5266_, 1);
v_ngen_5270_ = lean_ctor_get(v___x_5266_, 2);
v_auxDeclNGen_5271_ = lean_ctor_get(v___x_5266_, 3);
v_traceState_5272_ = lean_ctor_get(v___x_5266_, 4);
v_cache_5273_ = lean_ctor_get(v___x_5266_, 5);
v_messages_5274_ = lean_ctor_get(v___x_5266_, 6);
v_snapshotTasks_5275_ = lean_ctor_get(v___x_5266_, 8);
v_newDecls_5276_ = lean_ctor_get(v___x_5266_, 9);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5278_ = v___x_5266_;
v_isShared_5279_ = v_isSharedCheck_5297_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_newDecls_5276_);
lean_inc(v_snapshotTasks_5275_);
lean_inc(v_infoState_5267_);
lean_inc(v_messages_5274_);
lean_inc(v_cache_5273_);
lean_inc(v_traceState_5272_);
lean_inc(v_auxDeclNGen_5271_);
lean_inc(v_ngen_5270_);
lean_inc(v_nextMacroScope_5269_);
lean_inc(v_env_5268_);
lean_dec(v___x_5266_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5297_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
uint8_t v_enabled_5280_; lean_object* v_assignment_5281_; lean_object* v_lazyAssignment_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5295_; 
v_enabled_5280_ = lean_ctor_get_uint8(v_infoState_5267_, sizeof(void*)*3);
v_assignment_5281_ = lean_ctor_get(v_infoState_5267_, 0);
v_lazyAssignment_5282_ = lean_ctor_get(v_infoState_5267_, 1);
v_isSharedCheck_5295_ = !lean_is_exclusive(v_infoState_5267_);
if (v_isSharedCheck_5295_ == 0)
{
lean_object* v_unused_5296_; 
v_unused_5296_ = lean_ctor_get(v_infoState_5267_, 2);
lean_dec(v_unused_5296_);
v___x_5284_ = v_infoState_5267_;
v_isShared_5285_ = v_isSharedCheck_5295_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_lazyAssignment_5282_);
lean_inc(v_assignment_5281_);
lean_dec(v_infoState_5267_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5295_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5286_; lean_object* v___x_5288_; 
v___x_5286_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5285_ == 0)
{
lean_ctor_set(v___x_5284_, 2, v___x_5286_);
v___x_5288_ = v___x_5284_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_assignment_5281_);
lean_ctor_set(v_reuseFailAlloc_5294_, 1, v_lazyAssignment_5282_);
lean_ctor_set(v_reuseFailAlloc_5294_, 2, v___x_5286_);
lean_ctor_set_uint8(v_reuseFailAlloc_5294_, sizeof(void*)*3, v_enabled_5280_);
v___x_5288_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
lean_object* v___x_5290_; 
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 7, v___x_5288_);
v___x_5290_ = v___x_5278_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_env_5268_);
lean_ctor_set(v_reuseFailAlloc_5293_, 1, v_nextMacroScope_5269_);
lean_ctor_set(v_reuseFailAlloc_5293_, 2, v_ngen_5270_);
lean_ctor_set(v_reuseFailAlloc_5293_, 3, v_auxDeclNGen_5271_);
lean_ctor_set(v_reuseFailAlloc_5293_, 4, v_traceState_5272_);
lean_ctor_set(v_reuseFailAlloc_5293_, 5, v_cache_5273_);
lean_ctor_set(v_reuseFailAlloc_5293_, 6, v_messages_5274_);
lean_ctor_set(v_reuseFailAlloc_5293_, 7, v___x_5288_);
lean_ctor_set(v_reuseFailAlloc_5293_, 8, v_snapshotTasks_5275_);
lean_ctor_set(v_reuseFailAlloc_5293_, 9, v_newDecls_5276_);
v___x_5290_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5291_ = lean_st_ref_set(v___y_5261_, v___x_5290_);
v___x_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5292_, 0, v_trees_5265_);
return v___x_5292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5298_);
lean_dec(v___y_5298_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5301_, lean_object* v_mkInfoTree_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v_a_5310_, lean_object* v_a_x3f_5311_){
_start:
{
lean_object* v___x_5313_; lean_object* v_infoState_5314_; lean_object* v_trees_5315_; lean_object* v___x_5316_; 
v___x_5313_ = lean_st_ref_get(v___y_5301_);
v_infoState_5314_ = lean_ctor_get(v___x_5313_, 7);
lean_inc_ref(v_infoState_5314_);
lean_dec(v___x_5313_);
v_trees_5315_ = lean_ctor_get(v_infoState_5314_, 2);
lean_inc_ref(v_trees_5315_);
lean_dec_ref(v_infoState_5314_);
lean_inc(v___y_5301_);
lean_inc_ref(v___y_5309_);
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
lean_inc(v___y_5306_);
lean_inc_ref(v___y_5305_);
lean_inc(v___y_5304_);
lean_inc_ref(v___y_5303_);
v___x_5316_ = lean_apply_10(v_mkInfoTree_5302_, v_trees_5315_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5301_, lean_box(0));
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5356_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5319_ = v___x_5316_;
v_isShared_5320_ = v_isSharedCheck_5356_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5356_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v_infoState_5322_; lean_object* v_env_5323_; lean_object* v_nextMacroScope_5324_; lean_object* v_ngen_5325_; lean_object* v_auxDeclNGen_5326_; lean_object* v_traceState_5327_; lean_object* v_cache_5328_; lean_object* v_messages_5329_; lean_object* v_snapshotTasks_5330_; lean_object* v_newDecls_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5355_; 
v___x_5321_ = lean_st_ref_take(v___y_5301_);
v_infoState_5322_ = lean_ctor_get(v___x_5321_, 7);
v_env_5323_ = lean_ctor_get(v___x_5321_, 0);
v_nextMacroScope_5324_ = lean_ctor_get(v___x_5321_, 1);
v_ngen_5325_ = lean_ctor_get(v___x_5321_, 2);
v_auxDeclNGen_5326_ = lean_ctor_get(v___x_5321_, 3);
v_traceState_5327_ = lean_ctor_get(v___x_5321_, 4);
v_cache_5328_ = lean_ctor_get(v___x_5321_, 5);
v_messages_5329_ = lean_ctor_get(v___x_5321_, 6);
v_snapshotTasks_5330_ = lean_ctor_get(v___x_5321_, 8);
v_newDecls_5331_ = lean_ctor_get(v___x_5321_, 9);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5333_ = v___x_5321_;
v_isShared_5334_ = v_isSharedCheck_5355_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_newDecls_5331_);
lean_inc(v_snapshotTasks_5330_);
lean_inc(v_infoState_5322_);
lean_inc(v_messages_5329_);
lean_inc(v_cache_5328_);
lean_inc(v_traceState_5327_);
lean_inc(v_auxDeclNGen_5326_);
lean_inc(v_ngen_5325_);
lean_inc(v_nextMacroScope_5324_);
lean_inc(v_env_5323_);
lean_dec(v___x_5321_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5355_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
uint8_t v_enabled_5335_; lean_object* v_assignment_5336_; lean_object* v_lazyAssignment_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5353_; 
v_enabled_5335_ = lean_ctor_get_uint8(v_infoState_5322_, sizeof(void*)*3);
v_assignment_5336_ = lean_ctor_get(v_infoState_5322_, 0);
v_lazyAssignment_5337_ = lean_ctor_get(v_infoState_5322_, 1);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_infoState_5322_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v_infoState_5322_, 2);
lean_dec(v_unused_5354_);
v___x_5339_ = v_infoState_5322_;
v_isShared_5340_ = v_isSharedCheck_5353_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_lazyAssignment_5337_);
lean_inc(v_assignment_5336_);
lean_dec(v_infoState_5322_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5353_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5341_; lean_object* v___x_5343_; 
v___x_5341_ = l_Lean_PersistentArray_push___redArg(v_a_5310_, v_a_5317_);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 2, v___x_5341_);
v___x_5343_ = v___x_5339_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_assignment_5336_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_lazyAssignment_5337_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v___x_5341_);
lean_ctor_set_uint8(v_reuseFailAlloc_5352_, sizeof(void*)*3, v_enabled_5335_);
v___x_5343_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
lean_object* v___x_5345_; 
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 7, v___x_5343_);
v___x_5345_ = v___x_5333_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_env_5323_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_nextMacroScope_5324_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_ngen_5325_);
lean_ctor_set(v_reuseFailAlloc_5351_, 3, v_auxDeclNGen_5326_);
lean_ctor_set(v_reuseFailAlloc_5351_, 4, v_traceState_5327_);
lean_ctor_set(v_reuseFailAlloc_5351_, 5, v_cache_5328_);
lean_ctor_set(v_reuseFailAlloc_5351_, 6, v_messages_5329_);
lean_ctor_set(v_reuseFailAlloc_5351_, 7, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5351_, 8, v_snapshotTasks_5330_);
lean_ctor_set(v_reuseFailAlloc_5351_, 9, v_newDecls_5331_);
v___x_5345_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5346_ = lean_st_ref_set(v___y_5301_, v___x_5345_);
v___x_5347_ = lean_box(0);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5347_);
v___x_5349_ = v___x_5319_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec_ref(v_a_5310_);
v_a_5357_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5316_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5316_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5365_, lean_object* v_mkInfoTree_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v_a_5374_, lean_object* v_a_x3f_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5365_, v_mkInfoTree_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v_a_5374_, v_a_x3f_5375_);
lean_dec(v_a_x3f_5375_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5365_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5378_, lean_object* v_mkInfoTree_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; lean_object* v_infoState_5390_; uint8_t v_enabled_5391_; 
v___x_5389_ = lean_st_ref_get(v___y_5387_);
v_infoState_5390_ = lean_ctor_get(v___x_5389_, 7);
lean_inc_ref(v_infoState_5390_);
lean_dec(v___x_5389_);
v_enabled_5391_ = lean_ctor_get_uint8(v_infoState_5390_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5390_);
if (v_enabled_5391_ == 0)
{
lean_object* v___x_5392_; 
lean_dec_ref(v_mkInfoTree_5379_);
lean_inc(v___y_5387_);
lean_inc_ref(v___y_5386_);
lean_inc(v___y_5385_);
lean_inc_ref(v___y_5384_);
lean_inc(v___y_5383_);
lean_inc_ref(v___y_5382_);
lean_inc(v___y_5381_);
lean_inc_ref(v___y_5380_);
v___x_5392_ = lean_apply_9(v_x_5378_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, lean_box(0));
return v___x_5392_;
}
else
{
lean_object* v___x_5393_; lean_object* v_a_5394_; lean_object* v_r_5395_; 
v___x_5393_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5387_);
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref(v___x_5393_);
lean_inc(v___y_5387_);
lean_inc_ref(v___y_5386_);
lean_inc(v___y_5385_);
lean_inc_ref(v___y_5384_);
lean_inc(v___y_5383_);
lean_inc_ref(v___y_5382_);
lean_inc(v___y_5381_);
lean_inc_ref(v___y_5380_);
v_r_5395_ = lean_apply_9(v_x_5378_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, lean_box(0));
if (lean_obj_tag(v_r_5395_) == 0)
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5420_; 
v_a_5396_ = lean_ctor_get(v_r_5395_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_r_5395_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5398_ = v_r_5395_;
v_isShared_5399_ = v_isSharedCheck_5420_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v_r_5395_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5420_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
lean_inc(v_a_5396_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set_tag(v___x_5398_, 1);
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; 
v___x_5402_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5387_, v_mkInfoTree_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v_a_5394_, v___x_5401_);
lean_dec_ref(v___x_5401_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5409_ == 0)
{
lean_object* v_unused_5410_; 
v_unused_5410_ = lean_ctor_get(v___x_5402_, 0);
lean_dec(v_unused_5410_);
v___x_5404_ = v___x_5402_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_dec(v___x_5402_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v_a_5396_);
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5396_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
lean_dec(v_a_5396_);
v_a_5411_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5402_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5402_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5414_ == 0)
{
v___x_5416_ = v___x_5413_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_a_5411_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
v_a_5421_ = lean_ctor_get(v_r_5395_, 0);
lean_inc(v_a_5421_);
lean_dec_ref(v_r_5395_);
v___x_5422_ = lean_box(0);
v___x_5423_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5387_, v_mkInfoTree_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v_a_5394_, v___x_5422_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5430_ == 0)
{
lean_object* v_unused_5431_; 
v_unused_5431_ = lean_ctor_get(v___x_5423_, 0);
lean_dec(v_unused_5431_);
v___x_5425_ = v___x_5423_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_dec(v___x_5423_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set_tag(v___x_5425_, 1);
lean_ctor_set(v___x_5425_, 0, v_a_5421_);
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5421_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_dec(v_a_5421_);
v_a_5432_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5423_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5423_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5440_, lean_object* v_mkInfoTree_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5440_, v_mkInfoTree_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec(v___y_5447_);
lean_dec_ref(v___y_5446_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5452_, lean_object* v_trees_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v___x_5463_; 
lean_inc(v___y_5461_);
lean_inc_ref(v___y_5460_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5454_);
v___x_5463_ = lean_apply_9(v_a_5452_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, lean_box(0));
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5472_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5466_ = v___x_5463_;
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5463_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5468_, 0, v_a_5464_);
lean_ctor_set(v___x_5468_, 1, v_trees_5453_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 0, v___x_5468_);
v___x_5470_ = v___x_5466_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_dec_ref(v_trees_5453_);
v_a_5473_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v___x_5463_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5463_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_a_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5481_, lean_object* v_trees_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5481_, v_trees_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5493_, lean_object* v_ref_5494_, lean_object* v_tactic_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_){
_start:
{
lean_object* v___x_5505_; 
v___x_5505_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5493_, v___y_5497_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v___x_5506_; 
lean_dec_ref(v___x_5505_);
v___x_5506_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v___x_5507_; 
lean_dec_ref(v___x_5506_);
v___x_5507_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5494_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v___f_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref(v___x_5507_);
v___f_5509_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5509_, 0, v_a_5508_);
v___x_5510_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5510_, 0, v_tactic_5495_);
v___x_5511_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5510_, v___f_5509_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
return v___x_5511_;
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec(v_tactic_5495_);
v_a_5512_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5507_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5507_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
else
{
lean_dec(v_tactic_5495_);
lean_dec(v_ref_5494_);
return v___x_5506_;
}
}
else
{
lean_dec(v_tactic_5495_);
lean_dec(v_ref_5494_);
return v___x_5505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5520_, lean_object* v_ref_5521_, lean_object* v_tactic_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5520_, v_ref_5521_, v_tactic_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5527_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec(v___y_5524_);
lean_dec_ref(v___y_5523_);
return v_res_5532_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = lean_box(1);
v___x_5534_ = l_Lean_MessageData_ofFormat(v___x_5533_);
return v___x_5534_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5538_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5539_ = l_Lean_MessageData_ofFormat(v___x_5538_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5540_, lean_object* v_x_5541_){
_start:
{
if (lean_obj_tag(v_x_5541_) == 0)
{
return v_x_5540_;
}
else
{
lean_object* v_head_5542_; lean_object* v_tail_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5565_; 
v_head_5542_ = lean_ctor_get(v_x_5541_, 0);
v_tail_5543_ = lean_ctor_get(v_x_5541_, 1);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_x_5541_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5545_ = v_x_5541_;
v_isShared_5546_ = v_isSharedCheck_5565_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_tail_5543_);
lean_inc(v_head_5542_);
lean_dec(v_x_5541_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5565_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v_before_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5563_; 
v_before_5547_ = lean_ctor_get(v_head_5542_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v_head_5542_);
if (v_isSharedCheck_5563_ == 0)
{
lean_object* v_unused_5564_; 
v_unused_5564_ = lean_ctor_get(v_head_5542_, 1);
lean_dec(v_unused_5564_);
v___x_5549_ = v_head_5542_;
v_isShared_5550_ = v_isSharedCheck_5563_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_before_5547_);
lean_dec(v_head_5542_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5563_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5551_; lean_object* v___x_5553_; 
v___x_5551_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5550_ == 0)
{
lean_ctor_set_tag(v___x_5549_, 7);
lean_ctor_set(v___x_5549_, 1, v___x_5551_);
lean_ctor_set(v___x_5549_, 0, v_x_5540_);
v___x_5553_ = v___x_5549_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_x_5540_);
lean_ctor_set(v_reuseFailAlloc_5562_, 1, v___x_5551_);
v___x_5553_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; lean_object* v___x_5556_; 
v___x_5554_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5546_ == 0)
{
lean_ctor_set_tag(v___x_5545_, 7);
lean_ctor_set(v___x_5545_, 1, v___x_5554_);
lean_ctor_set(v___x_5545_, 0, v___x_5553_);
v___x_5556_ = v___x_5545_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5553_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5557_ = l_Lean_MessageData_ofSyntax(v_before_5547_);
v___x_5558_ = l_Lean_indentD(v___x_5557_);
v___x_5559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5556_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
v_x_5540_ = v___x_5559_;
v_x_5541_ = v_tail_5543_;
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
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5570_ = l_Lean_MessageData_ofFormat(v___x_5569_);
return v___x_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5571_, lean_object* v_macroStack_5572_, lean_object* v___y_5573_){
_start:
{
lean_object* v_options_5575_; lean_object* v___x_5576_; uint8_t v___x_5577_; 
v_options_5575_ = lean_ctor_get(v___y_5573_, 2);
v___x_5576_ = l_Lean_Elab_pp_macroStack;
v___x_5577_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5575_, v___x_5576_);
if (v___x_5577_ == 0)
{
lean_object* v___x_5578_; 
lean_dec(v_macroStack_5572_);
v___x_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5578_, 0, v_msgData_5571_);
return v___x_5578_;
}
else
{
if (lean_obj_tag(v_macroStack_5572_) == 0)
{
lean_object* v___x_5579_; 
v___x_5579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5579_, 0, v_msgData_5571_);
return v___x_5579_;
}
else
{
lean_object* v_head_5580_; lean_object* v_after_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5596_; 
v_head_5580_ = lean_ctor_get(v_macroStack_5572_, 0);
lean_inc(v_head_5580_);
v_after_5581_ = lean_ctor_get(v_head_5580_, 1);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_head_5580_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_head_5580_, 0);
lean_dec(v_unused_5597_);
v___x_5583_ = v_head_5580_;
v_isShared_5584_ = v_isSharedCheck_5596_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_after_5581_);
lean_dec(v_head_5580_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5596_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5585_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5584_ == 0)
{
lean_ctor_set_tag(v___x_5583_, 7);
lean_ctor_set(v___x_5583_, 1, v___x_5585_);
lean_ctor_set(v___x_5583_, 0, v_msgData_5571_);
v___x_5587_ = v___x_5583_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_msgData_5571_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v_msgData_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v___x_5588_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5587_);
lean_ctor_set(v___x_5589_, 1, v___x_5588_);
v___x_5590_ = l_Lean_MessageData_ofSyntax(v_after_5581_);
v___x_5591_ = l_Lean_indentD(v___x_5590_);
v_msgData_5592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5592_, 0, v___x_5589_);
lean_ctor_set(v_msgData_5592_, 1, v___x_5591_);
v___x_5593_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5592_, v_macroStack_5572_);
v___x_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5593_);
return v___x_5594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5598_, lean_object* v_macroStack_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5598_, v_macroStack_5599_, v___y_5600_);
lean_dec_ref(v___y_5600_);
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_ref_5611_; lean_object* v___x_5612_; lean_object* v_a_5613_; lean_object* v_macroStack_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v_a_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5625_; 
v_ref_5611_ = lean_ctor_get(v___y_5608_, 5);
v___x_5612_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5603_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_a_5613_);
lean_dec_ref(v___x_5612_);
v_macroStack_5614_ = lean_ctor_get(v___y_5604_, 1);
v___x_5615_ = l_Lean_Elab_getBetterRef(v_ref_5611_, v_macroStack_5614_);
lean_inc(v_macroStack_5614_);
v___x_5616_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5613_, v_macroStack_5614_, v___y_5608_);
v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5616_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5619_ = v___x_5616_;
v_isShared_5620_ = v_isSharedCheck_5625_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_a_5617_);
lean_dec(v___x_5616_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5625_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5621_; lean_object* v___x_5623_; 
v___x_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5615_);
lean_ctor_set(v___x_5621_, 1, v_a_5617_);
if (v_isShared_5620_ == 0)
{
lean_ctor_set_tag(v___x_5619_, 1);
lean_ctor_set(v___x_5619_, 0, v___x_5621_);
v___x_5623_ = v___x_5619_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5621_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_){
_start:
{
lean_object* v_res_5634_; 
v_res_5634_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_);
lean_dec(v___y_5632_);
lean_dec_ref(v___y_5631_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
return v_res_5634_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; 
v___x_5636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5637_ = l_Lean_stringToMessageData(v___x_5636_);
return v___x_5637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5638_, size_t v_sz_5639_, size_t v_i_5640_, lean_object* v_b_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v_a_5650_; uint8_t v___x_5654_; 
v___x_5654_ = lean_usize_dec_lt(v_i_5640_, v_sz_5639_);
if (v___x_5654_ == 0)
{
lean_object* v___x_5655_; 
v___x_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5655_, 0, v_b_5641_);
return v___x_5655_;
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5657_; 
v_a_5656_ = lean_array_uget_borrowed(v_as_5638_, v_i_5640_);
lean_inc(v_a_5656_);
v___x_5657_ = l_Lean_MVarId_getType(v_a_5656_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v_a_5658_; lean_object* v___x_5659_; 
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_a_5658_);
lean_dec_ref(v___x_5657_);
lean_inc(v_a_5656_);
v___x_5659_ = l_Lean_MVarId_getType(v_a_5656_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref(v___x_5659_);
v___x_5661_ = lean_box(0);
v___x_5662_ = l_Lean_getRecAppSyntax_x3f(v_a_5660_);
lean_dec(v_a_5660_);
if (lean_obj_tag(v___x_5662_) == 1)
{
lean_object* v_val_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v_val_5663_ = lean_ctor_get(v___x_5662_, 0);
lean_inc(v_val_5663_);
lean_dec_ref(v___x_5662_);
v___x_5664_ = l_Lean_Expr_mdataExpr_x21(v_a_5658_);
lean_dec(v_a_5658_);
lean_inc(v_a_5656_);
v___x_5665_ = l_Lean_MVarId_setType___redArg(v_a_5656_, v___x_5664_, v___y_5645_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_object* v_fileName_5666_; lean_object* v_fileMap_5667_; lean_object* v_options_5668_; lean_object* v_currRecDepth_5669_; lean_object* v_maxRecDepth_5670_; lean_object* v_ref_5671_; lean_object* v_currNamespace_5672_; lean_object* v_openDecls_5673_; lean_object* v_initHeartbeats_5674_; lean_object* v_maxHeartbeats_5675_; lean_object* v_quotContext_5676_; lean_object* v_currMacroScope_5677_; uint8_t v_diag_5678_; lean_object* v_cancelTk_x3f_5679_; uint8_t v_suppressElabErrors_5680_; lean_object* v_inheritedTraceOptions_5681_; lean_object* v_ref_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
lean_dec_ref(v___x_5665_);
v_fileName_5666_ = lean_ctor_get(v___y_5646_, 0);
v_fileMap_5667_ = lean_ctor_get(v___y_5646_, 1);
v_options_5668_ = lean_ctor_get(v___y_5646_, 2);
v_currRecDepth_5669_ = lean_ctor_get(v___y_5646_, 3);
v_maxRecDepth_5670_ = lean_ctor_get(v___y_5646_, 4);
v_ref_5671_ = lean_ctor_get(v___y_5646_, 5);
v_currNamespace_5672_ = lean_ctor_get(v___y_5646_, 6);
v_openDecls_5673_ = lean_ctor_get(v___y_5646_, 7);
v_initHeartbeats_5674_ = lean_ctor_get(v___y_5646_, 8);
v_maxHeartbeats_5675_ = lean_ctor_get(v___y_5646_, 9);
v_quotContext_5676_ = lean_ctor_get(v___y_5646_, 10);
v_currMacroScope_5677_ = lean_ctor_get(v___y_5646_, 11);
v_diag_5678_ = lean_ctor_get_uint8(v___y_5646_, sizeof(void*)*14);
v_cancelTk_x3f_5679_ = lean_ctor_get(v___y_5646_, 12);
v_suppressElabErrors_5680_ = lean_ctor_get_uint8(v___y_5646_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5681_ = lean_ctor_get(v___y_5646_, 13);
v_ref_5682_ = l_Lean_replaceRef(v_val_5663_, v_ref_5671_);
lean_dec(v_val_5663_);
lean_inc_ref(v_inheritedTraceOptions_5681_);
lean_inc(v_cancelTk_x3f_5679_);
lean_inc(v_currMacroScope_5677_);
lean_inc(v_quotContext_5676_);
lean_inc(v_maxHeartbeats_5675_);
lean_inc(v_initHeartbeats_5674_);
lean_inc(v_openDecls_5673_);
lean_inc(v_currNamespace_5672_);
lean_inc(v_maxRecDepth_5670_);
lean_inc(v_currRecDepth_5669_);
lean_inc_ref(v_options_5668_);
lean_inc_ref(v_fileMap_5667_);
lean_inc_ref(v_fileName_5666_);
v___x_5683_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5683_, 0, v_fileName_5666_);
lean_ctor_set(v___x_5683_, 1, v_fileMap_5667_);
lean_ctor_set(v___x_5683_, 2, v_options_5668_);
lean_ctor_set(v___x_5683_, 3, v_currRecDepth_5669_);
lean_ctor_set(v___x_5683_, 4, v_maxRecDepth_5670_);
lean_ctor_set(v___x_5683_, 5, v_ref_5682_);
lean_ctor_set(v___x_5683_, 6, v_currNamespace_5672_);
lean_ctor_set(v___x_5683_, 7, v_openDecls_5673_);
lean_ctor_set(v___x_5683_, 8, v_initHeartbeats_5674_);
lean_ctor_set(v___x_5683_, 9, v_maxHeartbeats_5675_);
lean_ctor_set(v___x_5683_, 10, v_quotContext_5676_);
lean_ctor_set(v___x_5683_, 11, v_currMacroScope_5677_);
lean_ctor_set(v___x_5683_, 12, v_cancelTk_x3f_5679_);
lean_ctor_set(v___x_5683_, 13, v_inheritedTraceOptions_5681_);
lean_ctor_set_uint8(v___x_5683_, sizeof(void*)*14, v_diag_5678_);
lean_ctor_set_uint8(v___x_5683_, sizeof(void*)*14 + 1, v_suppressElabErrors_5680_);
lean_inc(v_a_5656_);
v___x_5684_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5656_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___x_5683_, v___y_5647_);
lean_dec_ref(v___x_5683_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_dec_ref(v___x_5684_);
v_a_5650_ = v___x_5661_;
goto v___jp_5649_;
}
else
{
return v___x_5684_;
}
}
else
{
lean_dec(v_val_5663_);
return v___x_5665_;
}
}
else
{
lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; 
lean_dec(v___x_5662_);
v___x_5685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5686_ = l_Lean_indentExpr(v_a_5658_);
v___x_5687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set(v___x_5687_, 1, v___x_5686_);
v___x_5688_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5687_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_dec_ref(v___x_5688_);
v_a_5650_ = v___x_5661_;
goto v___jp_5649_;
}
else
{
return v___x_5688_;
}
}
}
else
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5696_; 
lean_dec(v_a_5658_);
v_a_5689_ = lean_ctor_get(v___x_5659_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5659_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5691_ = v___x_5659_;
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5659_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
else
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5704_; 
v_a_5697_ = lean_ctor_get(v___x_5657_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5699_ = v___x_5657_;
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___x_5657_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
v___jp_5649_:
{
size_t v___x_5651_; size_t v___x_5652_; 
v___x_5651_ = ((size_t)1ULL);
v___x_5652_ = lean_usize_add(v_i_5640_, v___x_5651_);
v_i_5640_ = v___x_5652_;
v_b_5641_ = v_a_5650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5705_, lean_object* v_sz_5706_, lean_object* v_i_5707_, lean_object* v_b_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
size_t v_sz_boxed_5716_; size_t v_i_boxed_5717_; lean_object* v_res_5718_; 
v_sz_boxed_5716_ = lean_unbox_usize(v_sz_5706_);
lean_dec(v_sz_5706_);
v_i_boxed_5717_ = lean_unbox_usize(v_i_5707_);
lean_dec(v_i_5707_);
v_res_5718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5705_, v_sz_boxed_5716_, v_i_boxed_5717_, v_b_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec_ref(v_as_5705_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5719_, size_t v_i_5720_, size_t v_stop_5721_, lean_object* v_b_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
uint8_t v___x_5728_; 
v___x_5728_ = lean_usize_dec_eq(v_i_5720_, v_stop_5721_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; lean_object* v___x_5730_; 
v___x_5729_ = lean_array_uget_borrowed(v_as_5719_, v_i_5720_);
lean_inc(v___x_5729_);
v___x_5730_ = l_Lean_MVarId_getType(v___x_5729_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v_a_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref(v___x_5730_);
v___x_5732_ = l_Lean_Expr_mdataExpr_x21(v_a_5731_);
lean_dec(v_a_5731_);
lean_inc(v___x_5729_);
v___x_5733_ = l_Lean_MVarId_setType___redArg(v___x_5729_, v___x_5732_, v___y_5724_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v_a_5734_; size_t v___x_5735_; size_t v___x_5736_; 
v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
lean_inc(v_a_5734_);
lean_dec_ref(v___x_5733_);
v___x_5735_ = ((size_t)1ULL);
v___x_5736_ = lean_usize_add(v_i_5720_, v___x_5735_);
v_i_5720_ = v___x_5736_;
v_b_5722_ = v_a_5734_;
goto _start;
}
else
{
return v___x_5733_;
}
}
else
{
lean_object* v_a_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
v_a_5738_ = lean_ctor_get(v___x_5730_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5730_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_a_5738_);
lean_dec(v___x_5730_);
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
else
{
lean_object* v___x_5746_; 
v___x_5746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5746_, 0, v_b_5722_);
return v___x_5746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5747_, lean_object* v_i_5748_, lean_object* v_stop_5749_, lean_object* v_b_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
size_t v_i_boxed_5756_; size_t v_stop_boxed_5757_; lean_object* v_res_5758_; 
v_i_boxed_5756_ = lean_unbox_usize(v_i_5748_);
lean_dec(v_i_5748_);
v_stop_boxed_5757_ = lean_unbox_usize(v_stop_5749_);
lean_dec(v_stop_5749_);
v_res_5758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5747_, v_i_boxed_5756_, v_stop_boxed_5757_, v_b_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_);
lean_dec(v___y_5754_);
lean_dec_ref(v___y_5753_);
lean_dec(v___y_5752_);
lean_dec_ref(v___y_5751_);
lean_dec_ref(v_as_5747_);
return v_res_5758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5759_, lean_object* v___x_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v___x_5768_; size_t v_sz_5769_; size_t v___x_5770_; lean_object* v___x_5771_; 
v___x_5768_ = lean_box(0);
v_sz_5769_ = lean_array_size(v___x_5760_);
v___x_5770_ = ((size_t)0ULL);
v___x_5771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5760_, v_sz_5769_, v___x_5770_, v___x_5768_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
lean_dec_ref(v___x_5760_);
if (lean_obj_tag(v___x_5771_) == 0)
{
lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5778_; 
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5771_);
if (v_isSharedCheck_5778_ == 0)
{
lean_object* v_unused_5779_; 
v_unused_5779_ = lean_ctor_get(v___x_5771_, 0);
lean_dec(v_unused_5779_);
v___x_5773_ = v___x_5771_;
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
else
{
lean_dec(v___x_5771_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 0, v___x_5768_);
v___x_5776_ = v___x_5773_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5768_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
else
{
return v___x_5771_;
}
}
else
{
lean_object* v_val_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5859_; 
v_val_5780_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5782_ = v___x_5759_;
v_isShared_5783_ = v_isSharedCheck_5859_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_val_5780_);
lean_dec(v___x_5759_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5859_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v_ref_5784_; lean_object* v_tactic_5785_; lean_object* v_fileName_5786_; lean_object* v_fileMap_5787_; lean_object* v_options_5788_; lean_object* v_currRecDepth_5789_; lean_object* v_maxRecDepth_5790_; lean_object* v_ref_5791_; lean_object* v_currNamespace_5792_; lean_object* v_openDecls_5793_; lean_object* v_initHeartbeats_5794_; lean_object* v_maxHeartbeats_5795_; lean_object* v_quotContext_5796_; lean_object* v_currMacroScope_5797_; uint8_t v_diag_5798_; lean_object* v_cancelTk_x3f_5799_; uint8_t v_suppressElabErrors_5800_; lean_object* v_inheritedTraceOptions_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v_ref_5804_; lean_object* v___x_5805_; lean_object* v___y_5832_; lean_object* v___y_5849_; uint8_t v___x_5850_; 
v_ref_5784_ = lean_ctor_get(v_val_5780_, 0);
lean_inc(v_ref_5784_);
v_tactic_5785_ = lean_ctor_get(v_val_5780_, 1);
lean_inc(v_tactic_5785_);
lean_dec(v_val_5780_);
v_fileName_5786_ = lean_ctor_get(v___y_5765_, 0);
v_fileMap_5787_ = lean_ctor_get(v___y_5765_, 1);
v_options_5788_ = lean_ctor_get(v___y_5765_, 2);
v_currRecDepth_5789_ = lean_ctor_get(v___y_5765_, 3);
v_maxRecDepth_5790_ = lean_ctor_get(v___y_5765_, 4);
v_ref_5791_ = lean_ctor_get(v___y_5765_, 5);
v_currNamespace_5792_ = lean_ctor_get(v___y_5765_, 6);
v_openDecls_5793_ = lean_ctor_get(v___y_5765_, 7);
v_initHeartbeats_5794_ = lean_ctor_get(v___y_5765_, 8);
v_maxHeartbeats_5795_ = lean_ctor_get(v___y_5765_, 9);
v_quotContext_5796_ = lean_ctor_get(v___y_5765_, 10);
v_currMacroScope_5797_ = lean_ctor_get(v___y_5765_, 11);
v_diag_5798_ = lean_ctor_get_uint8(v___y_5765_, sizeof(void*)*14);
v_cancelTk_x3f_5799_ = lean_ctor_get(v___y_5765_, 12);
v_suppressElabErrors_5800_ = lean_ctor_get_uint8(v___y_5765_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5801_ = lean_ctor_get(v___y_5765_, 13);
v___x_5802_ = lean_unsigned_to_nat(0u);
v___x_5803_ = lean_array_get_size(v___x_5760_);
v_ref_5804_ = l_Lean_replaceRef(v_ref_5784_, v_ref_5791_);
lean_inc_ref(v_inheritedTraceOptions_5801_);
lean_inc(v_cancelTk_x3f_5799_);
lean_inc(v_currMacroScope_5797_);
lean_inc(v_quotContext_5796_);
lean_inc(v_maxHeartbeats_5795_);
lean_inc(v_initHeartbeats_5794_);
lean_inc(v_openDecls_5793_);
lean_inc(v_currNamespace_5792_);
lean_inc(v_maxRecDepth_5790_);
lean_inc(v_currRecDepth_5789_);
lean_inc_ref(v_options_5788_);
lean_inc_ref(v_fileMap_5787_);
lean_inc_ref(v_fileName_5786_);
v___x_5805_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5805_, 0, v_fileName_5786_);
lean_ctor_set(v___x_5805_, 1, v_fileMap_5787_);
lean_ctor_set(v___x_5805_, 2, v_options_5788_);
lean_ctor_set(v___x_5805_, 3, v_currRecDepth_5789_);
lean_ctor_set(v___x_5805_, 4, v_maxRecDepth_5790_);
lean_ctor_set(v___x_5805_, 5, v_ref_5804_);
lean_ctor_set(v___x_5805_, 6, v_currNamespace_5792_);
lean_ctor_set(v___x_5805_, 7, v_openDecls_5793_);
lean_ctor_set(v___x_5805_, 8, v_initHeartbeats_5794_);
lean_ctor_set(v___x_5805_, 9, v_maxHeartbeats_5795_);
lean_ctor_set(v___x_5805_, 10, v_quotContext_5796_);
lean_ctor_set(v___x_5805_, 11, v_currMacroScope_5797_);
lean_ctor_set(v___x_5805_, 12, v_cancelTk_x3f_5799_);
lean_ctor_set(v___x_5805_, 13, v_inheritedTraceOptions_5801_);
lean_ctor_set_uint8(v___x_5805_, sizeof(void*)*14, v_diag_5798_);
lean_ctor_set_uint8(v___x_5805_, sizeof(void*)*14 + 1, v_suppressElabErrors_5800_);
v___x_5850_ = lean_nat_dec_lt(v___x_5802_, v___x_5803_);
if (v___x_5850_ == 0)
{
goto v___jp_5833_;
}
else
{
lean_object* v___x_5851_; uint8_t v___x_5852_; 
v___x_5851_ = lean_box(0);
v___x_5852_ = lean_nat_dec_le(v___x_5803_, v___x_5803_);
if (v___x_5852_ == 0)
{
if (v___x_5850_ == 0)
{
goto v___jp_5833_;
}
else
{
size_t v___x_5853_; size_t v___x_5854_; lean_object* v___x_5855_; 
v___x_5853_ = ((size_t)0ULL);
v___x_5854_ = lean_usize_of_nat(v___x_5803_);
v___x_5855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5760_, v___x_5853_, v___x_5854_, v___x_5851_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
v___y_5849_ = v___x_5855_;
goto v___jp_5848_;
}
}
else
{
size_t v___x_5856_; size_t v___x_5857_; lean_object* v___x_5858_; 
v___x_5856_ = ((size_t)0ULL);
v___x_5857_ = lean_usize_of_nat(v___x_5803_);
v___x_5858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5760_, v___x_5856_, v___x_5857_, v___x_5851_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
v___y_5849_ = v___x_5858_;
goto v___jp_5848_;
}
}
v___jp_5806_:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___f_5810_; lean_object* v___x_5811_; 
v___x_5807_ = lean_box(0);
v___x_5808_ = lean_array_get(v___x_5807_, v___x_5760_, v___x_5802_);
v___x_5809_ = lean_array_to_list(v___x_5760_);
v___f_5810_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5810_, 0, v___x_5809_);
lean_closure_set(v___f_5810_, 1, v_ref_5784_);
lean_closure_set(v___f_5810_, 2, v_tactic_5785_);
v___x_5811_ = l_Lean_Elab_Tactic_run(v___x_5808_, v___f_5810_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5822_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5814_ = v___x_5811_;
v_isShared_5815_ = v_isSharedCheck_5822_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5811_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5822_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
uint8_t v___x_5816_; 
v___x_5816_ = l_List_isEmpty___redArg(v_a_5812_);
if (v___x_5816_ == 0)
{
lean_object* v___x_5817_; 
lean_del_object(v___x_5814_);
v___x_5817_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5812_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
lean_dec_ref(v___x_5805_);
return v___x_5817_;
}
else
{
lean_object* v___x_5818_; lean_object* v___x_5820_; 
lean_dec(v_a_5812_);
lean_dec_ref(v___x_5805_);
v___x_5818_ = lean_box(0);
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 0, v___x_5818_);
v___x_5820_ = v___x_5814_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v___x_5818_);
v___x_5820_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
return v___x_5820_;
}
}
}
}
else
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5830_; 
lean_dec_ref(v___x_5805_);
v_a_5823_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5811_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5811_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5826_ == 0)
{
v___x_5828_ = v___x_5825_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
v___jp_5831_:
{
if (lean_obj_tag(v___y_5832_) == 0)
{
lean_dec_ref(v___y_5832_);
goto v___jp_5806_;
}
else
{
lean_dec_ref(v___x_5805_);
lean_dec(v_tactic_5785_);
lean_dec(v_ref_5784_);
lean_dec_ref(v___x_5760_);
return v___y_5832_;
}
}
v___jp_5833_:
{
uint8_t v___x_5834_; 
v___x_5834_ = lean_nat_dec_eq(v___x_5803_, v___x_5802_);
if (v___x_5834_ == 0)
{
uint8_t v___x_5835_; 
lean_del_object(v___x_5782_);
v___x_5835_ = lean_nat_dec_lt(v___x_5802_, v___x_5803_);
if (v___x_5835_ == 0)
{
goto v___jp_5806_;
}
else
{
lean_object* v___x_5836_; uint8_t v___x_5837_; 
v___x_5836_ = lean_box(0);
v___x_5837_ = lean_nat_dec_le(v___x_5803_, v___x_5803_);
if (v___x_5837_ == 0)
{
if (v___x_5835_ == 0)
{
goto v___jp_5806_;
}
else
{
size_t v___x_5838_; size_t v___x_5839_; lean_object* v___x_5840_; 
v___x_5838_ = ((size_t)0ULL);
v___x_5839_ = lean_usize_of_nat(v___x_5803_);
v___x_5840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5760_, v___x_5838_, v___x_5839_, v___x_5836_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
v___y_5832_ = v___x_5840_;
goto v___jp_5831_;
}
}
else
{
size_t v___x_5841_; size_t v___x_5842_; lean_object* v___x_5843_; 
v___x_5841_ = ((size_t)0ULL);
v___x_5842_ = lean_usize_of_nat(v___x_5803_);
v___x_5843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5760_, v___x_5841_, v___x_5842_, v___x_5836_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___x_5805_, v___y_5766_);
v___y_5832_ = v___x_5843_;
goto v___jp_5831_;
}
}
}
else
{
lean_object* v___x_5844_; lean_object* v___x_5846_; 
lean_dec_ref(v___x_5805_);
lean_dec(v_tactic_5785_);
lean_dec(v_ref_5784_);
lean_dec_ref(v___x_5760_);
v___x_5844_ = lean_box(0);
if (v_isShared_5783_ == 0)
{
lean_ctor_set_tag(v___x_5782_, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5844_);
v___x_5846_ = v___x_5782_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5844_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
}
}
}
v___jp_5848_:
{
if (lean_obj_tag(v___y_5849_) == 0)
{
lean_dec_ref(v___y_5849_);
goto v___jp_5833_;
}
else
{
lean_dec_ref(v___x_5805_);
lean_dec(v_tactic_5785_);
lean_dec(v_ref_5784_);
lean_del_object(v___x_5782_);
lean_dec_ref(v___x_5760_);
return v___y_5849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5860_, lean_object* v___x_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5860_, v___x_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
return v_res_5869_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5870_){
_start:
{
uint8_t v___x_5871_; 
v___x_5871_ = 0;
return v___x_5871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5872_){
_start:
{
uint8_t v_res_5873_; lean_object* v_r_5874_; 
v_res_5873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5872_);
lean_dec(v_x_5872_);
v_r_5874_ = lean_box(v_res_5873_);
return v_r_5874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5881_, size_t v_sz_5882_, size_t v_i_5883_, lean_object* v_b_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_){
_start:
{
uint8_t v___x_5890_; 
v___x_5890_ = lean_usize_dec_lt(v_i_5883_, v_sz_5882_);
if (v___x_5890_ == 0)
{
lean_object* v___x_5891_; 
v___x_5891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5891_, 0, v_b_5884_);
return v___x_5891_;
}
else
{
lean_object* v_snd_5892_; lean_object* v_fst_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5964_; 
v_snd_5892_ = lean_ctor_get(v_b_5884_, 1);
v_fst_5893_ = lean_ctor_get(v_b_5884_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_b_5884_);
if (v_isSharedCheck_5964_ == 0)
{
v___x_5895_ = v_b_5884_;
v_isShared_5896_ = v_isSharedCheck_5964_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_snd_5892_);
lean_inc(v_fst_5893_);
lean_dec(v_b_5884_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5964_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v_array_5897_; lean_object* v_start_5898_; lean_object* v_stop_5899_; uint8_t v___x_5900_; 
v_array_5897_ = lean_ctor_get(v_snd_5892_, 0);
v_start_5898_ = lean_ctor_get(v_snd_5892_, 1);
v_stop_5899_ = lean_ctor_get(v_snd_5892_, 2);
v___x_5900_ = lean_nat_dec_lt(v_start_5898_, v_stop_5899_);
if (v___x_5900_ == 0)
{
lean_object* v___x_5902_; 
if (v_isShared_5896_ == 0)
{
v___x_5902_ = v___x_5895_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_fst_5893_);
lean_ctor_set(v_reuseFailAlloc_5904_, 1, v_snd_5892_);
v___x_5902_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5903_; 
v___x_5903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5902_);
return v___x_5903_;
}
}
else
{
lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5960_; 
lean_inc(v_stop_5899_);
lean_inc(v_start_5898_);
lean_inc_ref(v_array_5897_);
v_isSharedCheck_5960_ = !lean_is_exclusive(v_snd_5892_);
if (v_isSharedCheck_5960_ == 0)
{
lean_object* v_unused_5961_; lean_object* v_unused_5962_; lean_object* v_unused_5963_; 
v_unused_5961_ = lean_ctor_get(v_snd_5892_, 2);
lean_dec(v_unused_5961_);
v_unused_5962_ = lean_ctor_get(v_snd_5892_, 1);
lean_dec(v_unused_5962_);
v_unused_5963_ = lean_ctor_get(v_snd_5892_, 0);
lean_dec(v_unused_5963_);
v___x_5906_ = v_snd_5892_;
v_isShared_5907_ = v_isSharedCheck_5960_;
goto v_resetjp_5905_;
}
else
{
lean_dec(v_snd_5892_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5960_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v_array_5908_; lean_object* v_start_5909_; lean_object* v_stop_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5915_; 
v_array_5908_ = lean_ctor_get(v_fst_5893_, 0);
v_start_5909_ = lean_ctor_get(v_fst_5893_, 1);
v_stop_5910_ = lean_ctor_get(v_fst_5893_, 2);
v___x_5911_ = lean_array_fget(v_array_5897_, v_start_5898_);
v___x_5912_ = lean_unsigned_to_nat(1u);
v___x_5913_ = lean_nat_add(v_start_5898_, v___x_5912_);
lean_dec(v_start_5898_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 1, v___x_5913_);
v___x_5915_ = v___x_5906_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_array_5897_);
lean_ctor_set(v_reuseFailAlloc_5959_, 1, v___x_5913_);
lean_ctor_set(v_reuseFailAlloc_5959_, 2, v_stop_5899_);
v___x_5915_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
uint8_t v___x_5916_; 
v___x_5916_ = lean_nat_dec_lt(v_start_5909_, v_stop_5910_);
if (v___x_5916_ == 0)
{
lean_object* v___x_5918_; 
lean_dec(v___x_5911_);
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 1, v___x_5915_);
v___x_5918_ = v___x_5895_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_fst_5893_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v___x_5915_);
v___x_5918_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
lean_object* v___x_5919_; 
v___x_5919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
return v___x_5919_;
}
}
else
{
lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5955_; 
lean_inc(v_stop_5910_);
lean_inc(v_start_5909_);
lean_inc_ref(v_array_5908_);
v_isSharedCheck_5955_ = !lean_is_exclusive(v_fst_5893_);
if (v_isSharedCheck_5955_ == 0)
{
lean_object* v_unused_5956_; lean_object* v_unused_5957_; lean_object* v_unused_5958_; 
v_unused_5956_ = lean_ctor_get(v_fst_5893_, 2);
lean_dec(v_unused_5956_);
v_unused_5957_ = lean_ctor_get(v_fst_5893_, 1);
lean_dec(v_unused_5957_);
v_unused_5958_ = lean_ctor_get(v_fst_5893_, 0);
lean_dec(v_unused_5958_);
v___x_5922_ = v_fst_5893_;
v_isShared_5923_ = v_isSharedCheck_5955_;
goto v_resetjp_5921_;
}
else
{
lean_dec(v_fst_5893_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5955_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___f_5924_; lean_object* v_a_5925_; lean_object* v___x_5926_; lean_object* v___y_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; uint8_t v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___f_5924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5925_ = lean_array_uget_borrowed(v_as_5881_, v_i_5883_);
v___x_5926_ = lean_array_fget_borrowed(v_array_5908_, v_start_5909_);
lean_inc(v___x_5926_);
v___y_5927_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5927_, 0, v___x_5911_);
lean_closure_set(v___y_5927_, 1, v___x_5926_);
lean_inc(v_a_5925_);
v___x_5928_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5928_, 0, lean_box(0));
lean_closure_set(v___x_5928_, 1, v_a_5925_);
lean_closure_set(v___x_5928_, 2, v___y_5927_);
v___x_5929_ = lean_box(0);
v___x_5930_ = lean_box(0);
v___x_5931_ = lean_box(1);
v___x_5932_ = 0;
v___x_5933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5934_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5934_, 0, v___x_5929_);
lean_ctor_set(v___x_5934_, 1, v___x_5930_);
lean_ctor_set(v___x_5934_, 2, v___x_5929_);
lean_ctor_set(v___x_5934_, 3, v___f_5924_);
lean_ctor_set(v___x_5934_, 4, v___x_5931_);
lean_ctor_set(v___x_5934_, 5, v___x_5931_);
lean_ctor_set(v___x_5934_, 6, v___x_5929_);
lean_ctor_set(v___x_5934_, 7, v___x_5933_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8, v___x_5916_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 1, v___x_5916_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 2, v___x_5916_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 3, v___x_5916_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 4, v___x_5932_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 5, v___x_5932_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 6, v___x_5932_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 7, v___x_5932_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 8, v___x_5916_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 9, v___x_5932_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*8 + 10, v___x_5916_);
v___x_5935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5936_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5928_, v___x_5934_, v___x_5935_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
if (lean_obj_tag(v___x_5936_) == 0)
{
lean_object* v___x_5937_; lean_object* v___x_5939_; 
lean_dec_ref(v___x_5936_);
v___x_5937_ = lean_nat_add(v_start_5909_, v___x_5912_);
lean_dec(v_start_5909_);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 1, v___x_5937_);
v___x_5939_ = v___x_5922_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_array_5908_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5946_, 2, v_stop_5910_);
v___x_5939_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
lean_object* v___x_5941_; 
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 1, v___x_5915_);
lean_ctor_set(v___x_5895_, 0, v___x_5939_);
v___x_5941_ = v___x_5895_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v___x_5939_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v___x_5915_);
v___x_5941_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
size_t v___x_5942_; size_t v___x_5943_; 
v___x_5942_ = ((size_t)1ULL);
v___x_5943_ = lean_usize_add(v_i_5883_, v___x_5942_);
v_i_5883_ = v___x_5943_;
v_b_5884_ = v___x_5941_;
goto _start;
}
}
}
else
{
lean_object* v_a_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5954_; 
lean_del_object(v___x_5922_);
lean_dec_ref(v___x_5915_);
lean_dec(v_stop_5910_);
lean_dec(v_start_5909_);
lean_dec_ref(v_array_5908_);
lean_del_object(v___x_5895_);
v_a_5947_ = lean_ctor_get(v___x_5936_, 0);
v_isSharedCheck_5954_ = !lean_is_exclusive(v___x_5936_);
if (v_isSharedCheck_5954_ == 0)
{
v___x_5949_ = v___x_5936_;
v_isShared_5950_ = v_isSharedCheck_5954_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_a_5947_);
lean_dec(v___x_5936_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5954_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v___x_5952_; 
if (v_isShared_5950_ == 0)
{
v___x_5952_ = v___x_5949_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_a_5947_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5965_, lean_object* v_sz_5966_, lean_object* v_i_5967_, lean_object* v_b_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_){
_start:
{
size_t v_sz_boxed_5974_; size_t v_i_boxed_5975_; lean_object* v_res_5976_; 
v_sz_boxed_5974_ = lean_unbox_usize(v_sz_5966_);
lean_dec(v_sz_5966_);
v_i_boxed_5975_ = lean_unbox_usize(v_i_5967_);
lean_dec(v_i_5967_);
v_res_5976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5965_, v_sz_boxed_5974_, v_i_boxed_5975_, v_b_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
lean_dec(v___y_5972_);
lean_dec_ref(v___y_5971_);
lean_dec(v___y_5970_);
lean_dec_ref(v___y_5969_);
lean_dec_ref(v_as_5965_);
return v_res_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5977_, lean_object* v_decrTactics_5978_, lean_object* v_argsPacker_5979_, lean_object* v_funNames_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_){
_start:
{
lean_object* v___x_5986_; 
lean_inc_ref(v_value_5977_);
v___x_5986_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5977_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
if (lean_obj_tag(v___x_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v___x_5988_; 
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
lean_inc(v_a_5987_);
lean_dec_ref(v___x_5986_);
v___x_5988_ = l_Lean_Elab_WF_assignSubsumed(v_a_5987_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
lean_dec(v_a_5987_);
if (lean_obj_tag(v___x_5988_) == 0)
{
lean_object* v_a_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; 
v_a_5989_ = lean_ctor_get(v___x_5988_, 0);
lean_inc(v_a_5989_);
lean_dec_ref(v___x_5988_);
v___x_5990_ = lean_array_get_size(v_decrTactics_5978_);
v___x_5991_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5979_, v___x_5990_, v_a_5989_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
lean_dec(v_a_5989_);
if (lean_obj_tag(v___x_5991_) == 0)
{
lean_object* v_a_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; size_t v_sz_5998_; size_t v___x_5999_; lean_object* v___x_6000_; 
v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
lean_inc(v_a_5992_);
lean_dec_ref(v___x_5991_);
v___x_5993_ = lean_unsigned_to_nat(0u);
v___x_5994_ = lean_array_get_size(v_a_5992_);
v___x_5995_ = l_Array_toSubarray___redArg(v_a_5992_, v___x_5993_, v___x_5994_);
v___x_5996_ = l_Array_toSubarray___redArg(v_decrTactics_5978_, v___x_5993_, v___x_5990_);
v___x_5997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5995_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v_sz_5998_ = lean_array_size(v_funNames_5980_);
v___x_5999_ = ((size_t)0ULL);
v___x_6000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5980_, v_sz_5998_, v___x_5999_, v___x_5997_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
if (lean_obj_tag(v___x_6000_) == 0)
{
lean_object* v___x_6001_; 
lean_dec_ref(v___x_6000_);
v___x_6001_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5977_, v___y_5982_);
return v___x_6001_;
}
else
{
lean_object* v_a_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6009_; 
lean_dec_ref(v_value_5977_);
v_a_6002_ = lean_ctor_get(v___x_6000_, 0);
v_isSharedCheck_6009_ = !lean_is_exclusive(v___x_6000_);
if (v_isSharedCheck_6009_ == 0)
{
v___x_6004_ = v___x_6000_;
v_isShared_6005_ = v_isSharedCheck_6009_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_a_6002_);
lean_dec(v___x_6000_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6009_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
lean_object* v___x_6007_; 
if (v_isShared_6005_ == 0)
{
v___x_6007_ = v___x_6004_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_a_6002_);
v___x_6007_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6006_;
}
v_reusejp_6006_:
{
return v___x_6007_;
}
}
}
}
else
{
lean_object* v_a_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6017_; 
lean_dec_ref(v_decrTactics_5978_);
lean_dec_ref(v_value_5977_);
v_a_6010_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6012_ = v___x_5991_;
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_a_6010_);
lean_dec(v___x_5991_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6015_; 
if (v_isShared_6013_ == 0)
{
v___x_6015_ = v___x_6012_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_dec_ref(v_decrTactics_5978_);
lean_dec_ref(v_value_5977_);
v_a_6018_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___x_5988_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_5988_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
else
{
lean_object* v_a_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6033_; 
lean_dec_ref(v_decrTactics_5978_);
lean_dec_ref(v_value_5977_);
v_a_6026_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_6033_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_6033_ == 0)
{
v___x_6028_ = v___x_5986_;
v_isShared_6029_ = v_isSharedCheck_6033_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_a_6026_);
lean_dec(v___x_5986_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6033_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
lean_object* v___x_6031_; 
if (v_isShared_6029_ == 0)
{
v___x_6031_ = v___x_6028_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v_a_6026_);
v___x_6031_ = v_reuseFailAlloc_6032_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
return v___x_6031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6034_, lean_object* v_decrTactics_6035_, lean_object* v_argsPacker_6036_, lean_object* v_funNames_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v_res_6043_; 
v_res_6043_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6034_, v_decrTactics_6035_, v_argsPacker_6036_, v_funNames_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_);
lean_dec(v___y_6041_);
lean_dec_ref(v___y_6040_);
lean_dec(v___y_6039_);
lean_dec_ref(v___y_6038_);
lean_dec_ref(v_funNames_6037_);
lean_dec_ref(v_argsPacker_6036_);
return v_res_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6044_, uint8_t v_isExporting_6045_, lean_object* v___x_6046_, lean_object* v___y_6047_, lean_object* v___x_6048_, lean_object* v_a_x3f_6049_){
_start:
{
lean_object* v___x_6051_; lean_object* v_env_6052_; lean_object* v_nextMacroScope_6053_; lean_object* v_ngen_6054_; lean_object* v_auxDeclNGen_6055_; lean_object* v_traceState_6056_; lean_object* v_messages_6057_; lean_object* v_infoState_6058_; lean_object* v_snapshotTasks_6059_; lean_object* v_newDecls_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6085_; 
v___x_6051_ = lean_st_ref_take(v___y_6044_);
v_env_6052_ = lean_ctor_get(v___x_6051_, 0);
v_nextMacroScope_6053_ = lean_ctor_get(v___x_6051_, 1);
v_ngen_6054_ = lean_ctor_get(v___x_6051_, 2);
v_auxDeclNGen_6055_ = lean_ctor_get(v___x_6051_, 3);
v_traceState_6056_ = lean_ctor_get(v___x_6051_, 4);
v_messages_6057_ = lean_ctor_get(v___x_6051_, 6);
v_infoState_6058_ = lean_ctor_get(v___x_6051_, 7);
v_snapshotTasks_6059_ = lean_ctor_get(v___x_6051_, 8);
v_newDecls_6060_ = lean_ctor_get(v___x_6051_, 9);
v_isSharedCheck_6085_ = !lean_is_exclusive(v___x_6051_);
if (v_isSharedCheck_6085_ == 0)
{
lean_object* v_unused_6086_; 
v_unused_6086_ = lean_ctor_get(v___x_6051_, 5);
lean_dec(v_unused_6086_);
v___x_6062_ = v___x_6051_;
v_isShared_6063_ = v_isSharedCheck_6085_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_newDecls_6060_);
lean_inc(v_snapshotTasks_6059_);
lean_inc(v_infoState_6058_);
lean_inc(v_messages_6057_);
lean_inc(v_traceState_6056_);
lean_inc(v_auxDeclNGen_6055_);
lean_inc(v_ngen_6054_);
lean_inc(v_nextMacroScope_6053_);
lean_inc(v_env_6052_);
lean_dec(v___x_6051_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6085_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6064_; lean_object* v___x_6066_; 
v___x_6064_ = l_Lean_Environment_setExporting(v_env_6052_, v_isExporting_6045_);
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 5, v___x_6046_);
lean_ctor_set(v___x_6062_, 0, v___x_6064_);
v___x_6066_ = v___x_6062_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6084_; 
v_reuseFailAlloc_6084_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6064_);
lean_ctor_set(v_reuseFailAlloc_6084_, 1, v_nextMacroScope_6053_);
lean_ctor_set(v_reuseFailAlloc_6084_, 2, v_ngen_6054_);
lean_ctor_set(v_reuseFailAlloc_6084_, 3, v_auxDeclNGen_6055_);
lean_ctor_set(v_reuseFailAlloc_6084_, 4, v_traceState_6056_);
lean_ctor_set(v_reuseFailAlloc_6084_, 5, v___x_6046_);
lean_ctor_set(v_reuseFailAlloc_6084_, 6, v_messages_6057_);
lean_ctor_set(v_reuseFailAlloc_6084_, 7, v_infoState_6058_);
lean_ctor_set(v_reuseFailAlloc_6084_, 8, v_snapshotTasks_6059_);
lean_ctor_set(v_reuseFailAlloc_6084_, 9, v_newDecls_6060_);
v___x_6066_ = v_reuseFailAlloc_6084_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v_mctx_6069_; lean_object* v_zetaDeltaFVarIds_6070_; lean_object* v_postponed_6071_; lean_object* v_diag_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6082_; 
v___x_6067_ = lean_st_ref_set(v___y_6044_, v___x_6066_);
v___x_6068_ = lean_st_ref_take(v___y_6047_);
v_mctx_6069_ = lean_ctor_get(v___x_6068_, 0);
v_zetaDeltaFVarIds_6070_ = lean_ctor_get(v___x_6068_, 2);
v_postponed_6071_ = lean_ctor_get(v___x_6068_, 3);
v_diag_6072_ = lean_ctor_get(v___x_6068_, 4);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6068_);
if (v_isSharedCheck_6082_ == 0)
{
lean_object* v_unused_6083_; 
v_unused_6083_ = lean_ctor_get(v___x_6068_, 1);
lean_dec(v_unused_6083_);
v___x_6074_ = v___x_6068_;
v_isShared_6075_ = v_isSharedCheck_6082_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_diag_6072_);
lean_inc(v_postponed_6071_);
lean_inc(v_zetaDeltaFVarIds_6070_);
lean_inc(v_mctx_6069_);
lean_dec(v___x_6068_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6082_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6077_; 
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 1, v___x_6048_);
v___x_6077_ = v___x_6074_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_mctx_6069_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v___x_6048_);
lean_ctor_set(v_reuseFailAlloc_6081_, 2, v_zetaDeltaFVarIds_6070_);
lean_ctor_set(v_reuseFailAlloc_6081_, 3, v_postponed_6071_);
lean_ctor_set(v_reuseFailAlloc_6081_, 4, v_diag_6072_);
v___x_6077_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; 
v___x_6078_ = lean_st_ref_set(v___y_6047_, v___x_6077_);
v___x_6079_ = lean_box(0);
v___x_6080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
return v___x_6080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6087_, lean_object* v_isExporting_6088_, lean_object* v___x_6089_, lean_object* v___y_6090_, lean_object* v___x_6091_, lean_object* v_a_x3f_6092_, lean_object* v___y_6093_){
_start:
{
uint8_t v_isExporting_boxed_6094_; lean_object* v_res_6095_; 
v_isExporting_boxed_6094_ = lean_unbox(v_isExporting_6088_);
v_res_6095_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6087_, v_isExporting_boxed_6094_, v___x_6089_, v___y_6090_, v___x_6091_, v_a_x3f_6092_);
lean_dec(v_a_x3f_6092_);
lean_dec(v___y_6090_);
lean_dec(v___y_6087_);
return v_res_6095_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6096_; 
v___x_6096_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6096_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; 
v___x_6097_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
return v___x_6098_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6099_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
return v___x_6100_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6102_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_6101_);
lean_ctor_set(v___x_6102_, 2, v___x_6101_);
lean_ctor_set(v___x_6102_, 3, v___x_6101_);
lean_ctor_set(v___x_6102_, 4, v___x_6101_);
lean_ctor_set(v___x_6102_, 5, v___x_6101_);
return v___x_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6103_, uint8_t v_isExporting_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v___x_6110_; lean_object* v_env_6111_; uint8_t v_isExporting_6112_; lean_object* v___x_6113_; lean_object* v_env_6114_; lean_object* v_nextMacroScope_6115_; lean_object* v_ngen_6116_; lean_object* v_auxDeclNGen_6117_; lean_object* v_traceState_6118_; lean_object* v_messages_6119_; lean_object* v_infoState_6120_; lean_object* v_snapshotTasks_6121_; lean_object* v_newDecls_6122_; lean_object* v___x_6124_; uint8_t v_isShared_6125_; uint8_t v_isSharedCheck_6176_; 
v___x_6110_ = lean_st_ref_get(v___y_6108_);
v_env_6111_ = lean_ctor_get(v___x_6110_, 0);
lean_inc_ref(v_env_6111_);
lean_dec(v___x_6110_);
v_isExporting_6112_ = lean_ctor_get_uint8(v_env_6111_, sizeof(void*)*8);
lean_dec_ref(v_env_6111_);
v___x_6113_ = lean_st_ref_take(v___y_6108_);
v_env_6114_ = lean_ctor_get(v___x_6113_, 0);
v_nextMacroScope_6115_ = lean_ctor_get(v___x_6113_, 1);
v_ngen_6116_ = lean_ctor_get(v___x_6113_, 2);
v_auxDeclNGen_6117_ = lean_ctor_get(v___x_6113_, 3);
v_traceState_6118_ = lean_ctor_get(v___x_6113_, 4);
v_messages_6119_ = lean_ctor_get(v___x_6113_, 6);
v_infoState_6120_ = lean_ctor_get(v___x_6113_, 7);
v_snapshotTasks_6121_ = lean_ctor_get(v___x_6113_, 8);
v_newDecls_6122_ = lean_ctor_get(v___x_6113_, 9);
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6113_);
if (v_isSharedCheck_6176_ == 0)
{
lean_object* v_unused_6177_; 
v_unused_6177_ = lean_ctor_get(v___x_6113_, 5);
lean_dec(v_unused_6177_);
v___x_6124_ = v___x_6113_;
v_isShared_6125_ = v_isSharedCheck_6176_;
goto v_resetjp_6123_;
}
else
{
lean_inc(v_newDecls_6122_);
lean_inc(v_snapshotTasks_6121_);
lean_inc(v_infoState_6120_);
lean_inc(v_messages_6119_);
lean_inc(v_traceState_6118_);
lean_inc(v_auxDeclNGen_6117_);
lean_inc(v_ngen_6116_);
lean_inc(v_nextMacroScope_6115_);
lean_inc(v_env_6114_);
lean_dec(v___x_6113_);
v___x_6124_ = lean_box(0);
v_isShared_6125_ = v_isSharedCheck_6176_;
goto v_resetjp_6123_;
}
v_resetjp_6123_:
{
lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6129_; 
v___x_6126_ = l_Lean_Environment_setExporting(v_env_6114_, v_isExporting_6104_);
v___x_6127_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6125_ == 0)
{
lean_ctor_set(v___x_6124_, 5, v___x_6127_);
lean_ctor_set(v___x_6124_, 0, v___x_6126_);
v___x_6129_ = v___x_6124_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v___x_6126_);
lean_ctor_set(v_reuseFailAlloc_6175_, 1, v_nextMacroScope_6115_);
lean_ctor_set(v_reuseFailAlloc_6175_, 2, v_ngen_6116_);
lean_ctor_set(v_reuseFailAlloc_6175_, 3, v_auxDeclNGen_6117_);
lean_ctor_set(v_reuseFailAlloc_6175_, 4, v_traceState_6118_);
lean_ctor_set(v_reuseFailAlloc_6175_, 5, v___x_6127_);
lean_ctor_set(v_reuseFailAlloc_6175_, 6, v_messages_6119_);
lean_ctor_set(v_reuseFailAlloc_6175_, 7, v_infoState_6120_);
lean_ctor_set(v_reuseFailAlloc_6175_, 8, v_snapshotTasks_6121_);
lean_ctor_set(v_reuseFailAlloc_6175_, 9, v_newDecls_6122_);
v___x_6129_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v_mctx_6132_; lean_object* v_zetaDeltaFVarIds_6133_; lean_object* v_postponed_6134_; lean_object* v_diag_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6173_; 
v___x_6130_ = lean_st_ref_set(v___y_6108_, v___x_6129_);
v___x_6131_ = lean_st_ref_take(v___y_6106_);
v_mctx_6132_ = lean_ctor_get(v___x_6131_, 0);
v_zetaDeltaFVarIds_6133_ = lean_ctor_get(v___x_6131_, 2);
v_postponed_6134_ = lean_ctor_get(v___x_6131_, 3);
v_diag_6135_ = lean_ctor_get(v___x_6131_, 4);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6131_);
if (v_isSharedCheck_6173_ == 0)
{
lean_object* v_unused_6174_; 
v_unused_6174_ = lean_ctor_get(v___x_6131_, 1);
lean_dec(v_unused_6174_);
v___x_6137_ = v___x_6131_;
v_isShared_6138_ = v_isSharedCheck_6173_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_diag_6135_);
lean_inc(v_postponed_6134_);
lean_inc(v_zetaDeltaFVarIds_6133_);
lean_inc(v_mctx_6132_);
lean_dec(v___x_6131_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6173_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6139_; lean_object* v___x_6141_; 
v___x_6139_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v___x_6139_);
v___x_6141_ = v___x_6137_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v_mctx_6132_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v___x_6139_);
lean_ctor_set(v_reuseFailAlloc_6172_, 2, v_zetaDeltaFVarIds_6133_);
lean_ctor_set(v_reuseFailAlloc_6172_, 3, v_postponed_6134_);
lean_ctor_set(v_reuseFailAlloc_6172_, 4, v_diag_6135_);
v___x_6141_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
lean_object* v___x_6142_; lean_object* v_r_6143_; 
v___x_6142_ = lean_st_ref_set(v___y_6106_, v___x_6141_);
lean_inc(v___y_6108_);
lean_inc_ref(v___y_6107_);
lean_inc(v___y_6106_);
lean_inc_ref(v___y_6105_);
v_r_6143_ = lean_apply_5(v_x_6103_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_, lean_box(0));
if (lean_obj_tag(v_r_6143_) == 0)
{
lean_object* v_a_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6160_; 
v_a_6144_ = lean_ctor_get(v_r_6143_, 0);
v_isSharedCheck_6160_ = !lean_is_exclusive(v_r_6143_);
if (v_isSharedCheck_6160_ == 0)
{
v___x_6146_ = v_r_6143_;
v_isShared_6147_ = v_isSharedCheck_6160_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_a_6144_);
lean_dec(v_r_6143_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6160_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6149_; 
lean_inc(v_a_6144_);
if (v_isShared_6147_ == 0)
{
lean_ctor_set_tag(v___x_6146_, 1);
v___x_6149_ = v___x_6146_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_a_6144_);
v___x_6149_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
lean_object* v___x_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6157_; 
v___x_6150_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6108_, v_isExporting_6112_, v___x_6127_, v___y_6106_, v___x_6139_, v___x_6149_);
lean_dec_ref(v___x_6149_);
v_isSharedCheck_6157_ = !lean_is_exclusive(v___x_6150_);
if (v_isSharedCheck_6157_ == 0)
{
lean_object* v_unused_6158_; 
v_unused_6158_ = lean_ctor_get(v___x_6150_, 0);
lean_dec(v_unused_6158_);
v___x_6152_ = v___x_6150_;
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
else
{
lean_dec(v___x_6150_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6155_; 
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 0, v_a_6144_);
v___x_6155_ = v___x_6152_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6144_);
v___x_6155_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
return v___x_6155_;
}
}
}
}
}
else
{
lean_object* v_a_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6170_; 
v_a_6161_ = lean_ctor_get(v_r_6143_, 0);
lean_inc(v_a_6161_);
lean_dec_ref(v_r_6143_);
v___x_6162_ = lean_box(0);
v___x_6163_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6108_, v_isExporting_6112_, v___x_6127_, v___y_6106_, v___x_6139_, v___x_6162_);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6170_ == 0)
{
lean_object* v_unused_6171_; 
v_unused_6171_ = lean_ctor_get(v___x_6163_, 0);
lean_dec(v_unused_6171_);
v___x_6165_ = v___x_6163_;
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
else
{
lean_dec(v___x_6163_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6168_; 
if (v_isShared_6166_ == 0)
{
lean_ctor_set_tag(v___x_6165_, 1);
lean_ctor_set(v___x_6165_, 0, v_a_6161_);
v___x_6168_ = v___x_6165_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6161_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
}
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
lean_dec_ref(v___x_6643_);
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
lean_dec_ref(v___x_6645_);
v___x_6647_ = l_Lean_Meta_getLevel(v_a_6646_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6647_) == 0)
{
lean_object* v_a_6648_; lean_object* v___x_6649_; 
v_a_6648_ = lean_ctor_get(v___x_6647_, 0);
lean_inc(v_a_6648_);
lean_dec_ref(v___x_6647_);
lean_inc_ref(v_type_6632_);
v___x_6649_ = l_Lean_Meta_getLevel(v_type_6632_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
if (lean_obj_tag(v___x_6649_) == 0)
{
lean_object* v_a_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; uint8_t v___x_6653_; uint8_t v___x_6654_; uint8_t v___x_6655_; lean_object* v___x_6656_; 
v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
lean_inc(v_a_6650_);
lean_dec_ref(v___x_6649_);
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
lean_dec_ref(v___x_6656_);
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
lean_dec_ref(v_a_6659_);
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
lean_dec_ref(v___x_6810_);
v___x_6812_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6797_, v_argsPacker_6798_, v_decrTactics_6799_, v_a_6811_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
if (lean_obj_tag(v___x_6812_) == 0)
{
lean_object* v_a_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6817_; uint8_t v___x_6818_; uint8_t v___x_6819_; lean_object* v___x_6820_; 
v_a_6813_ = lean_ctor_get(v___x_6812_, 0);
lean_inc(v_a_6813_);
lean_dec_ref(v___x_6812_);
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
lean_dec_ref(v___x_6820_);
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
lean_dec_ref(v___x_6916_);
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
lean_dec_ref(v___x_6923_);
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
lean_dec_ref(v___x_6927_);
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
lean_dec_ref(v___x_6929_);
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
