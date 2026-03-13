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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_local_ctx_is_empty(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "replaceRecApps"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 200, 98, 106, 253, 180, 239, 155)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 49, 183, 192, 189, 122, 168, 8)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 153, 95, 135, 30, 171, 176, 236)}};
static const lean_object* l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Type check every step of the well-founded definition translation"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 7, 223, 43, 113, 218, 153, 204)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(253, 66, 61, 195, 239, 57, 103, 30)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 40, 109, 48, 223, 99, 87, 96)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_5),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(255, 91, 253, 16, 215, 73, 25, 62)}};
static const lean_object* l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "replaceRecApp: eta-expanding"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3;
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_66_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_67_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_68_ = l_Lean_Option_register___at___00Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(v___x_65_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4____boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(lean_object* v_decreasingProp_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_ref_79_ = lean_ctor_get(v_a_76_, 5);
lean_inc(v_ref_79_);
v___x_80_ = l_Lean_mkRecAppWithSyntax(v_decreasingProp_73_, v_ref_79_);
v___x_81_ = lean_box(0);
lean_inc_ref(v_a_74_);
v___x_82_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_80_, v___x_81_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = l_Lean_Expr_mvarId_x21(v_a_83_);
v___x_85_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v___x_86_ = 1;
v___x_87_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v___x_84_, v___x_85_, v___x_86_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v___x_87_, 0);
lean_dec(v_unused_95_);
v___x_89_ = v___x_87_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_dec(v___x_87_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v_a_83_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_83_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_a_83_);
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___boxed(lean_object* v_decreasingProp_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v_decreasingProp_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object* v_decreasingProp_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v_decreasingProp_111_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___boxed(lean_object* v_decreasingProp_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(v_decreasingProp_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(lean_object* v_msg_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = l_Lean_instInhabitedLocalDecl_default;
v___x_131_ = lean_panic_fn(v___x_130_, v_msg_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(lean_object* v_msgData_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; lean_object* v___x_140_; lean_object* v_mctx_141_; lean_object* v_lctx_142_; lean_object* v_options_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = lean_st_ref_get(v___y_134_);
v_mctx_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_140_);
v_lctx_142_ = lean_ctor_get(v___y_133_, 2);
v_options_143_ = lean_ctor_get(v___y_135_, 2);
lean_inc_ref(v_options_143_);
lean_inc_ref(v_lctx_142_);
v___x_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_144_, 0, v_env_139_);
lean_ctor_set(v___x_144_, 1, v_mctx_141_);
lean_ctor_set(v___x_144_, 2, v_lctx_142_);
lean_ctor_set(v___x_144_, 3, v_options_143_);
v___x_145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_msgData_132_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1___boxed(lean_object* v_msgData_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msgData_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_ref_160_; lean_object* v___x_161_; lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_170_; 
v_ref_160_ = lean_ctor_get(v___y_157_, 5);
v___x_161_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_170_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_inc(v_ref_160_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_ref_160_);
lean_ctor_set(v___x_166_, 1, v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2));
v___x_182_ = lean_unsigned_to_nat(14u);
v___x_183_ = lean_unsigned_to_nat(22u);
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1));
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0));
v___x_186_ = l_mkPanicMessageWithDecl(v___x_185_, v___x_184_, v___x_183_, v___x_182_, v___x_181_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___y_196_; lean_object* v___y_200_; lean_object* v_lctx_204_; lean_object* v___x_205_; uint8_t v___x_215_; 
v_lctx_204_ = lean_ctor_get(v_a_190_, 2);
v___x_205_ = lean_box(0);
lean_inc_ref(v_lctx_204_);
v___x_215_ = lean_local_ctx_is_empty(v_lctx_204_);
if (v___x_215_ == 0)
{
lean_inc_ref(v_lctx_204_);
lean_dec_ref(v_a_190_);
goto v___jp_206_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v___x_216_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5);
v___x_217_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_216_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec_ref(v_a_190_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = l_Lean_LocalDecl_fvarId(v___y_196_);
lean_dec_ref(v___y_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
v___jp_199_:
{
if (lean_obj_tag(v___y_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3);
v___x_202_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(v___x_201_);
v___y_196_ = v___x_202_;
goto v___jp_195_;
}
else
{
lean_object* v_val_203_; 
v_val_203_ = lean_ctor_get(v___y_200_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v___y_200_);
v___y_196_ = v_val_203_;
goto v___jp_195_;
}
}
v___jp_206_:
{
lean_object* v_decls_207_; lean_object* v_size_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_decls_207_ = lean_ctor_get(v_lctx_204_, 1);
lean_inc_ref(v_decls_207_);
v_size_208_ = lean_ctor_get(v_decls_207_, 2);
v___x_209_ = l_Lean_LocalContext_size(v_lctx_204_);
lean_dec_ref(v_lctx_204_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_sub(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_nat_dec_lt(v___x_211_, v_size_208_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec(v___x_211_);
lean_dec_ref(v_decls_207_);
v___x_213_ = l_outOfBounds___redArg(v___x_205_);
v___y_200_ = v___x_213_;
goto v___jp_199_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_PersistentArray_get_x21___redArg(v___x_205_, v_decls_207_, v___x_211_);
lean_dec(v___x_211_);
v___y_200_ = v___x_214_;
goto v___jp_199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___boxed(lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(lean_object* v_00_u03b1_232_, lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___boxed(lean_object* v_00_u03b1_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(v_00_u03b1_240_, v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(lean_object* v_lctxid_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_lctx_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_lctx_251_ = lean_ctor_get(v_a_249_, 2);
lean_inc_ref(v_lctx_251_);
lean_dec_ref(v_a_249_);
v___x_252_ = l_Lean_LocalContext_contains(v_lctx_251_, v_lctxid_248_);
v___x_253_ = lean_box(v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg___boxed(lean_object* v_lctxid_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_255_, v_a_256_);
lean_dec(v_lctxid_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(lean_object* v_lctxid_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_259_, v_a_260_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___boxed(lean_object* v_lctxid_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(v_lctxid_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec(v_lctxid_266_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(lean_object* v_recFnName_273_, lean_object* v_e_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_277_ = lean_st_ref_take(v_a_275_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_push(v___x_279_, v_recFnName_273_);
v___x_281_ = l_Lean_HasConstCache_containsUnsafe(v___x_280_, v_e_274_, v___x_277_);
lean_dec_ref(v___x_280_);
v_fst_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_fst_282_);
v_snd_283_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_snd_283_);
lean_dec_ref(v___x_281_);
v___x_284_ = lean_st_ref_set(v_a_275_, v_snd_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_fst_282_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg___boxed(lean_object* v_recFnName_286_, lean_object* v_e_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_286_, v_e_287_, v_a_288_);
lean_dec(v_a_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object* v_recFnName_291_, lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_291_, v_e_292_, v_a_293_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object* v_recFnName_303_, lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(v_recFnName_303_, v_e_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object* v_cls_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_options_321_; uint8_t v_hasTrace_322_; 
v_options_321_ = lean_ctor_get(v___y_319_, 2);
v_hasTrace_322_ = lean_ctor_get_uint8(v_options_321_, sizeof(void*)*1);
if (v_hasTrace_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_cls_318_);
v___x_323_ = lean_box(v_hasTrace_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v_inheritedTraceOptions_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_inheritedTraceOptions_325_ = lean_ctor_get(v___y_319_, 13);
v___x_326_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_327_ = l_Lean_Name_append(v___x_326_, v_cls_318_);
v___x_328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_325_, v_options_321_, v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = lean_box(v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object* v_cls_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_331_, v___y_332_);
lean_dec_ref(v___y_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_335_, v___y_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0(lean_object* v_k_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_apply_9(v_k_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, lean_box(0));
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0___boxed(lean_object* v_k_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0(v_k_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_k_379_, uint8_t v_allowLevelAssignments_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___f_390_; lean_object* v___x_391_; 
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_390_, 0, v_k_379_);
lean_closure_set(v___f_390_, 1, v___y_381_);
lean_closure_set(v___f_390_, 2, v___y_382_);
lean_closure_set(v___f_390_, 3, v___y_383_);
lean_closure_set(v___f_390_, 4, v___y_384_);
v___x_391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_380_, v___f_390_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_391_) == 0)
{
return v___x_391_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_k_400_, lean_object* v_allowLevelAssignments_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_411_; lean_object* v_res_412_; 
v_allowLevelAssignments_boxed_411_ = lean_unbox(v_allowLevelAssignments_401_);
v_res_412_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_k_400_, v_allowLevelAssignments_boxed_411_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_ref_419_ = lean_ctor_get(v___y_416_, 5);
v___x_420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_ref_419_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_ref_419_);
lean_ctor_set(v___x_425_, 1, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_452_, lean_object* v_e_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___x_545_; 
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc_ref(v_a_452_);
v___x_545_ = l_Lean_Meta_isTypeCorrect(v_a_452_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; uint8_t v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_548_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_453_);
v___x_549_ = l_Lean_indentExpr(v_e_453_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_inc_ref(v_a_452_);
v___x_553_ = l_Lean_indentExpr(v_a_452_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_554_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec_ref(v___x_555_);
v___y_464_ = v___y_454_;
v___y_465_ = v___y_455_;
v___y_466_ = v___y_456_;
v___y_467_ = v___y_457_;
v___y_468_ = v___y_458_;
v___y_469_ = v___y_459_;
v___y_470_ = v___y_460_;
v___y_471_ = v___y_461_;
goto v___jp_463_;
}
else
{
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
return v___x_555_;
}
}
else
{
v___y_464_ = v___y_454_;
v___y_465_ = v___y_455_;
v___y_466_ = v___y_456_;
v___y_467_ = v___y_457_;
v___y_468_ = v___y_458_;
v___y_469_ = v___y_459_;
v___y_470_ = v___y_460_;
v___y_471_ = v___y_461_;
goto v___jp_463_;
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v_a_556_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_545_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
v___jp_463_:
{
lean_object* v___x_472_; 
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc_ref(v_e_453_);
v___x_472_ = lean_infer_type(v_e_453_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc_ref(v_a_452_);
v___x_474_ = lean_infer_type(v_a_452_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v___x_474_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v_a_475_);
lean_inc(v_a_473_);
v___x_476_ = l_Lean_Meta_isExprDefEq(v_a_473_, v_a_475_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_520_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_520_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_520_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_520_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; 
v___x_481_ = lean_unbox(v_a_477_);
lean_dec(v_a_477_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_del_object(v___x_479_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
v___x_482_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_473_, v_a_475_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_507_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
v_fst_484_ = lean_ctor_get(v_a_483_, 0);
v_snd_485_ = lean_ctor_get(v_a_483_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_483_);
if (v_isSharedCheck_507_ == 0)
{
v___x_487_ = v_a_483_;
v_isShared_488_ = v_isSharedCheck_507_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_inc(v_fst_484_);
lean_dec(v_a_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_507_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_490_ = l_Lean_indentExpr(v_e_453_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 7);
lean_ctor_set(v___x_487_, 1, v___x_490_);
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_506_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_493_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_indentExpr(v_a_452_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_indentExpr(v_fst_484_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_indentExpr(v_snd_485_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_504_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v_a_508_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_482_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_482_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v_a_475_);
lean_dec(v_a_473_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v___x_516_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_516_);
v___x_518_ = v___x_479_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_a_475_);
lean_dec(v_a_473_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v_a_521_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_476_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_476_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_a_473_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v_a_529_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_474_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_474_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_e_453_);
lean_dec_ref(v_a_452_);
v_a_537_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_472_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_472_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_564_, lean_object* v_e_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_564_, v_e_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec(v___y_566_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(lean_object* v_k_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_apply_10(v_k_576_, v_b_581_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed(lean_object* v_k_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(v_k_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v_b_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(lean_object* v_name_600_, uint8_t v_bi_601_, lean_object* v_type_602_, lean_object* v_k_603_, uint8_t v_kind_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_615_; 
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_614_, 0, v_k_603_);
lean_closure_set(v___f_614_, 1, v___y_605_);
lean_closure_set(v___f_614_, 2, v___y_606_);
lean_closure_set(v___f_614_, 3, v___y_607_);
lean_closure_set(v___f_614_, 4, v___y_608_);
v___x_615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_600_, v_bi_601_, v_type_602_, v___f_614_, v_kind_604_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_615_) == 0)
{
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___boxed(lean_object* v_name_624_, lean_object* v_bi_625_, lean_object* v_type_626_, lean_object* v_k_627_, lean_object* v_kind_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v_bi_boxed_638_; uint8_t v_kind_boxed_639_; lean_object* v_res_640_; 
v_bi_boxed_638_ = lean_unbox(v_bi_625_);
v_kind_boxed_639_ = lean_unbox(v_kind_628_);
v_res_640_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_name_624_, v_bi_boxed_638_, v_type_626_, v_k_627_, v_kind_boxed_639_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
lean_ctor_set(v___x_646_, 3, v___x_644_);
lean_ctor_set(v___x_646_, 4, v___x_644_);
lean_ctor_set(v___x_646_, 5, v___x_644_);
lean_ctor_set(v___x_646_, 6, v___x_644_);
lean_ctor_set(v___x_646_, 7, v___x_644_);
lean_ctor_set(v___x_646_, 8, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(32u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4(void){
_start:
{
size_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_650_ = ((size_t)5ULL);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_unsigned_to_nat(32u);
v___x_653_ = lean_mk_empty_array_with_capacity(v___x_652_);
v___x_654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__3);
v___x_655_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_651_);
lean_ctor_set(v___x_655_, 3, v___x_651_);
lean_ctor_set_usize(v___x_655_, 4, v___x_650_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_box(1);
v___x_657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__4);
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__1);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_656_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__6));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__8));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__10));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__12));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__14));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__16));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__18));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(lean_object* v_msg_681_, lean_object* v_declHint_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_env_686_; uint8_t v___x_687_; 
v___x_685_ = lean_st_ref_get(v___y_683_);
v_env_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_env_686_);
lean_dec(v___x_685_);
v___x_687_ = l_Lean_Name_isAnonymous(v_declHint_682_);
if (v___x_687_ == 0)
{
uint8_t v_isExporting_688_; 
v_isExporting_688_ = lean_ctor_get_uint8(v_env_686_, sizeof(void*)*8);
if (v_isExporting_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec_ref(v_env_686_);
lean_dec(v_declHint_682_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_msg_681_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; uint8_t v___x_691_; 
lean_inc_ref(v_env_686_);
v___x_690_ = l_Lean_Environment_setExporting(v_env_686_, v___x_687_);
lean_inc(v_declHint_682_);
lean_inc_ref(v___x_690_);
v___x_691_ = l_Lean_Environment_contains(v___x_690_, v_declHint_682_, v_isExporting_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
lean_dec_ref(v___x_690_);
lean_dec_ref(v_env_686_);
lean_dec(v_declHint_682_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_msg_681_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_c_698_; lean_object* v___x_699_; 
v___x_693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__2);
v___x_694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__5);
v___x_695_ = l_Lean_Options_empty;
v___x_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_696_, 0, v___x_690_);
lean_ctor_set(v___x_696_, 1, v___x_693_);
lean_ctor_set(v___x_696_, 2, v___x_694_);
lean_ctor_set(v___x_696_, 3, v___x_695_);
lean_inc(v_declHint_682_);
v___x_697_ = l_Lean_MessageData_ofConstName(v_declHint_682_, v___x_687_);
v_c_698_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_698_, 0, v___x_696_);
lean_ctor_set(v_c_698_, 1, v___x_697_);
v___x_699_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_686_, v_declHint_682_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v_env_686_);
lean_dec(v_declHint_682_);
v___x_700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_c_698_);
v___x_702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__9);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_MessageData_note(v___x_703_);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v_msg_681_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_742_; 
v_val_707_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_742_ == 0)
{
v___x_709_ = v___x_699_;
v_isShared_710_ = v_isSharedCheck_742_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_699_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_742_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_mod_714_; uint8_t v___x_715_; 
v___x_711_ = lean_box(0);
v___x_712_ = l_Lean_Environment_header(v_env_686_);
lean_dec_ref(v_env_686_);
v___x_713_ = l_Lean_EnvironmentHeader_moduleNames(v___x_712_);
v_mod_714_ = lean_array_get(v___x_711_, v___x_713_, v_val_707_);
lean_dec(v_val_707_);
lean_dec_ref(v___x_713_);
v___x_715_ = l_Lean_isPrivateName(v_declHint_682_);
lean_dec(v_declHint_682_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__11);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_c_698_);
v___x_718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__13);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_MessageData_ofName(v_mod_714_);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__15);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_MessageData_note(v___x_723_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v_msg_681_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v___x_725_);
v___x_727_ = v___x_709_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__7);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_c_698_);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__17);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = l_Lean_MessageData_ofName(v_mod_714_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___closed__19);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_MessageData_note(v___x_736_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v_msg_681_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v___x_738_);
v___x_740_ = v___x_709_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v_env_686_);
lean_dec(v_declHint_682_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_msg_681_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg___boxed(lean_object* v_msg_744_, lean_object* v_declHint_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(v_msg_744_, v_declHint_745_, v___y_746_);
lean_dec(v___y_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31(lean_object* v_msg_749_, lean_object* v_declHint_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_770_; 
v___x_760_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(v_msg_749_, v_declHint_750_, v___y_758_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_770_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = l_Lean_unknownIdentifierMessageTag;
v___x_766_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_a_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31___boxed(lean_object* v_msg_771_, lean_object* v_declHint_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31(v_msg_771_, v_declHint_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec(v___y_773_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(lean_object* v_ref_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_fileName_794_; lean_object* v_fileMap_795_; lean_object* v_options_796_; lean_object* v_currRecDepth_797_; lean_object* v_maxRecDepth_798_; lean_object* v_ref_799_; lean_object* v_currNamespace_800_; lean_object* v_openDecls_801_; lean_object* v_initHeartbeats_802_; lean_object* v_maxHeartbeats_803_; lean_object* v_quotContext_804_; lean_object* v_currMacroScope_805_; uint8_t v_diag_806_; lean_object* v_cancelTk_x3f_807_; uint8_t v_suppressElabErrors_808_; lean_object* v_inheritedTraceOptions_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_fileName_794_ = lean_ctor_get(v___y_791_, 0);
v_fileMap_795_ = lean_ctor_get(v___y_791_, 1);
v_options_796_ = lean_ctor_get(v___y_791_, 2);
v_currRecDepth_797_ = lean_ctor_get(v___y_791_, 3);
v_maxRecDepth_798_ = lean_ctor_get(v___y_791_, 4);
v_ref_799_ = lean_ctor_get(v___y_791_, 5);
v_currNamespace_800_ = lean_ctor_get(v___y_791_, 6);
v_openDecls_801_ = lean_ctor_get(v___y_791_, 7);
v_initHeartbeats_802_ = lean_ctor_get(v___y_791_, 8);
v_maxHeartbeats_803_ = lean_ctor_get(v___y_791_, 9);
v_quotContext_804_ = lean_ctor_get(v___y_791_, 10);
v_currMacroScope_805_ = lean_ctor_get(v___y_791_, 11);
v_diag_806_ = lean_ctor_get_uint8(v___y_791_, sizeof(void*)*14);
v_cancelTk_x3f_807_ = lean_ctor_get(v___y_791_, 12);
v_suppressElabErrors_808_ = lean_ctor_get_uint8(v___y_791_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_809_ = lean_ctor_get(v___y_791_, 13);
v_isSharedCheck_818_ = !lean_is_exclusive(v___y_791_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v___y_791_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_inheritedTraceOptions_809_);
lean_inc(v_cancelTk_x3f_807_);
lean_inc(v_currMacroScope_805_);
lean_inc(v_quotContext_804_);
lean_inc(v_maxHeartbeats_803_);
lean_inc(v_initHeartbeats_802_);
lean_inc(v_openDecls_801_);
lean_inc(v_currNamespace_800_);
lean_inc(v_ref_799_);
lean_inc(v_maxRecDepth_798_);
lean_inc(v_currRecDepth_797_);
lean_inc(v_options_796_);
lean_inc(v_fileMap_795_);
lean_inc(v_fileName_794_);
lean_dec(v___y_791_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_ref_813_; lean_object* v___x_815_; 
v_ref_813_ = l_Lean_replaceRef(v_ref_783_, v_ref_799_);
lean_dec(v_ref_799_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v_ref_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fileName_794_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_fileMap_795_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_options_796_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_currRecDepth_797_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_maxRecDepth_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_ref_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 6, v_currNamespace_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 7, v_openDecls_801_);
lean_ctor_set(v_reuseFailAlloc_817_, 8, v_initHeartbeats_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 9, v_maxHeartbeats_803_);
lean_ctor_set(v_reuseFailAlloc_817_, 10, v_quotContext_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 11, v_currMacroScope_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 12, v_cancelTk_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 13, v_inheritedTraceOptions_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_817_, sizeof(void*)*14, v_diag_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_817_, sizeof(void*)*14 + 1, v_suppressElabErrors_808_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_msg_784_, v___y_789_, v___y_790_, v___x_815_, v___y_792_);
lean_dec_ref(v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg___boxed(lean_object* v_ref_819_, lean_object* v_msg_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_819_, v_msg_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v_ref_819_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(lean_object* v_ref_831_, lean_object* v_msg_832_, lean_object* v_declHint_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31(v_msg_832_, v_declHint_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
v___x_845_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_831_, v_a_844_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg___boxed(lean_object* v_ref_846_, lean_object* v_msg_847_, lean_object* v_declHint_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_846_, v_msg_847_, v_declHint_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v_ref_846_);
return v_res_858_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__0));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__2));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(lean_object* v_ref_865_, lean_object* v_constName_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_876_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1);
v___x_877_ = 0;
lean_inc(v_constName_866_);
v___x_878_ = l_Lean_MessageData_ofConstName(v_constName_866_, v___x_877_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_865_, v___x_881_, v_constName_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___boxed(lean_object* v_ref_883_, lean_object* v_constName_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_883_, v_constName_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_885_);
lean_dec(v_ref_883_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(lean_object* v_constName_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_ref_905_; lean_object* v___x_906_; 
v_ref_905_ = lean_ctor_get(v___y_902_, 5);
lean_inc(v_ref_905_);
v___x_906_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_905_, v_constName_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v_ref_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg___boxed(lean_object* v_constName_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(lean_object* v_constName_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_env_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v___x_928_ = lean_st_ref_get(v___y_926_);
v_env_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_env_929_);
lean_dec(v___x_928_);
v___x_930_ = 0;
lean_inc(v_constName_918_);
v___x_931_ = l_Lean_Environment_find_x3f(v_env_929_, v_constName_918_, v___x_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_932_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___y_925_);
lean_dec(v_constName_918_);
v_val_933_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_931_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_val_933_);
lean_dec(v___x_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_val_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___boxed(lean_object* v_constName_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_constName_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec(v___y_942_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(lean_object* v_declName_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_env_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_st_ref_get(v___y_953_);
v_env_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc_ref(v_env_956_);
lean_dec(v___x_955_);
v___x_957_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_956_, v_declName_952_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg___boxed(lean_object* v_declName_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_959_, v___y_960_);
lean_dec(v___y_960_);
return v_res_962_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_toApplicative_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1075_; 
v___x_980_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0);
v___x_981_ = l_ReaderT_instMonad___redArg(v___x_980_);
v_toApplicative_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_981_, 1);
lean_dec(v_unused_1076_);
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1075_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_toApplicative_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1075_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_toFunctor_986_; lean_object* v_toSeq_987_; lean_object* v_toSeqLeft_988_; lean_object* v_toSeqRight_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1073_; 
v_toFunctor_986_ = lean_ctor_get(v_toApplicative_982_, 0);
v_toSeq_987_ = lean_ctor_get(v_toApplicative_982_, 2);
v_toSeqLeft_988_ = lean_ctor_get(v_toApplicative_982_, 3);
v_toSeqRight_989_ = lean_ctor_get(v_toApplicative_982_, 4);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_toApplicative_982_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_dec(v_unused_1074_);
v___x_991_ = v_toApplicative_982_;
v_isShared_992_ = v_isSharedCheck_1073_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toSeqRight_989_);
lean_inc(v_toSeqLeft_988_);
lean_inc(v_toSeq_987_);
lean_inc(v_toFunctor_986_);
lean_dec(v_toApplicative_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1073_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1002_; 
v___f_993_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__1));
v___f_994_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__2));
lean_inc_ref(v_toFunctor_986_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_995_, 0, v_toFunctor_986_);
v___f_996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_996_, 0, v_toFunctor_986_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___f_995_);
lean_ctor_set(v___x_997_, 1, v___f_996_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_998_, 0, v_toSeqRight_989_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_999_, 0, v_toSeqLeft_988_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toSeq_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v___f_998_);
lean_ctor_set(v___x_991_, 3, v___f_999_);
lean_ctor_set(v___x_991_, 2, v___f_1000_);
lean_ctor_set(v___x_991_, 1, v___f_993_);
lean_ctor_set(v___x_991_, 0, v___x_997_);
v___x_1002_ = v___x_991_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___f_999_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___f_998_);
v___x_1002_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___f_994_);
lean_ctor_set(v___x_984_, 0, v___x_1002_);
v___x_1004_ = v___x_984_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___f_994_);
v___x_1004_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v_toApplicative_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1069_; 
v___x_1005_ = l_ReaderT_instMonad___redArg(v___x_1004_);
v_toApplicative_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v___x_1005_, 1);
lean_dec(v_unused_1070_);
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1069_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_toApplicative_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1069_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_toFunctor_1010_; lean_object* v_toSeq_1011_; lean_object* v_toSeqLeft_1012_; lean_object* v_toSeqRight_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1067_; 
v_toFunctor_1010_ = lean_ctor_get(v_toApplicative_1006_, 0);
v_toSeq_1011_ = lean_ctor_get(v_toApplicative_1006_, 2);
v_toSeqLeft_1012_ = lean_ctor_get(v_toApplicative_1006_, 3);
v_toSeqRight_1013_ = lean_ctor_get(v_toApplicative_1006_, 4);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_toApplicative_1006_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_toApplicative_1006_, 1);
lean_dec(v_unused_1068_);
v___x_1015_ = v_toApplicative_1006_;
v_isShared_1016_ = v_isSharedCheck_1067_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_toSeqRight_1013_);
lean_inc(v_toSeqLeft_1012_);
lean_inc(v_toSeq_1011_);
lean_inc(v_toFunctor_1010_);
lean_dec(v_toApplicative_1006_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1067_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1026_; 
v___f_1017_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__3));
v___f_1018_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__4));
lean_inc_ref(v_toFunctor_1010_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toFunctor_1010_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toFunctor_1010_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___f_1019_);
lean_ctor_set(v___x_1021_, 1, v___f_1020_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeqRight_1013_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toSeqLeft_1012_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toSeq_1011_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 4, v___f_1022_);
lean_ctor_set(v___x_1015_, 3, v___f_1023_);
lean_ctor_set(v___x_1015_, 2, v___f_1024_);
lean_ctor_set(v___x_1015_, 1, v___f_1017_);
lean_ctor_set(v___x_1015_, 0, v___x_1021_);
v___x_1026_ = v___x_1015_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___f_1024_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v___f_1023_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v___f_1022_);
v___x_1026_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___f_1018_);
lean_ctor_set(v___x_1008_, 0, v___x_1026_);
v___x_1028_ = v___x_1008_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___f_1018_);
v___x_1028_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v_toApplicative_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1063_; 
v___x_1029_ = l_ReaderT_instMonad___redArg(v___x_1028_);
v_toApplicative_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1029_, 1);
lean_dec(v_unused_1064_);
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1063_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_toApplicative_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1063_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_toFunctor_1034_; lean_object* v_toSeq_1035_; lean_object* v_toSeqLeft_1036_; lean_object* v_toSeqRight_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1061_; 
v_toFunctor_1034_ = lean_ctor_get(v_toApplicative_1030_, 0);
v_toSeq_1035_ = lean_ctor_get(v_toApplicative_1030_, 2);
v_toSeqLeft_1036_ = lean_ctor_get(v_toApplicative_1030_, 3);
v_toSeqRight_1037_ = lean_ctor_get(v_toApplicative_1030_, 4);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_toApplicative_1030_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_toApplicative_1030_, 1);
lean_dec(v_unused_1062_);
v___x_1039_ = v_toApplicative_1030_;
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_toSeqRight_1037_);
lean_inc(v_toSeqLeft_1036_);
lean_inc(v_toSeq_1035_);
lean_inc(v_toFunctor_1034_);
lean_dec(v_toApplicative_1030_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1050_; 
v___f_1041_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__5));
v___f_1042_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__6));
lean_inc_ref(v_toFunctor_1034_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toFunctor_1034_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toFunctor_1034_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___f_1043_);
lean_ctor_set(v___x_1045_, 1, v___f_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toSeqRight_1037_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeqLeft_1036_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeq_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___f_1046_);
lean_ctor_set(v___x_1039_, 3, v___f_1047_);
lean_ctor_set(v___x_1039_, 2, v___f_1048_);
lean_ctor_set(v___x_1039_, 1, v___f_1041_);
lean_ctor_set(v___x_1039_, 0, v___x_1045_);
v___x_1050_ = v___x_1039_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___f_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___f_1046_);
v___x_1050_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___f_1042_);
lean_ctor_set(v___x_1032_, 0, v___x_1050_);
v___x_1052_ = v___x_1032_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_1042_);
v___x_1052_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_59442__overap_1057_; lean_object* v___x_1058_; 
v___x_1053_ = l_ReaderT_instMonad___redArg(v___x_1052_);
v___x_1054_ = l_ReaderT_instMonad___redArg(v___x_1053_);
v___x_1055_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1056_ = l_instInhabitedOfMonad___redArg(v___x_1054_, v___x_1055_);
v___x_59442__overap_1057_ = lean_panic_fn(v___x_1056_, v_msg_970_);
v___x_1058_ = lean_apply_9(v___x_59442__overap_1057_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
return v___x_1058_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___boxed(lean_object* v_msg_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(v_msg_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
return v_res_1087_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__2));
v___x_1092_ = lean_unsigned_to_nat(53u);
v___x_1093_ = lean_unsigned_to_nat(62u);
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__1));
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__0));
v___x_1096_ = l_mkPanicMessageWithDecl(v___x_1095_, v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(size_t v_sz_1097_, size_t v_i_1098_, lean_object* v_bs_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_usize_dec_lt(v_i_1098_, v_sz_1097_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_bs_1099_);
return v___x_1110_;
}
else
{
lean_object* v_v_1111_; lean_object* v___x_1112_; 
v_v_1111_ = lean_array_uget_borrowed(v_bs_1099_, v_i_1098_);
lean_inc_ref(v___y_1106_);
lean_inc(v_v_1111_);
v___x_1112_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_v_1111_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; lean_object* v_a_1117_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1099_, v_i_1098_, v___x_1114_);
if (lean_obj_tag(v_a_1113_) == 6)
{
lean_object* v_val_1122_; lean_object* v_numFields_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v_val_1122_ = lean_ctor_get(v_a_1113_, 0);
lean_inc_ref(v_val_1122_);
lean_dec_ref(v_a_1113_);
v_numFields_1123_ = lean_ctor_get(v_val_1122_, 4);
lean_inc(v_numFields_1123_);
lean_dec_ref(v_val_1122_);
v___x_1124_ = 0;
v___x_1125_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1125_, 0, v_numFields_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1114_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*2, v___x_1124_);
v_a_1117_ = v___x_1125_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_a_1113_);
v___x_1126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc(v___y_1100_);
v___x_1127_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(v___x_1126_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v_a_1117_ = v_a_1128_;
goto v___jp_1116_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_bs_x27_1115_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
v_a_1129_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1127_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
v___jp_1116_:
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1098_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1115_, v_i_1098_, v_a_1117_);
v_i_1098_ = v___x_1119_;
v_bs_1099_ = v___x_1120_;
goto _start;
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v_bs_1099_);
v_a_1137_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1112_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1112_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___boxed(lean_object* v_sz_1145_, lean_object* v_i_1146_, lean_object* v_bs_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1145_);
lean_dec(v_sz_1145_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(v_sz_boxed_1157_, v_i_boxed_1158_, v_bs_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v_res_1159_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0(void){
_start:
{
lean_object* v___x_1160_; lean_object* v_dummy_1161_; 
v___x_1160_ = lean_box(0);
v_dummy_1161_ = l_Lean_Expr_sort___override(v___x_1160_);
return v_dummy_1161_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_unsigned_to_nat(16u);
v___x_1164_ = lean_mk_array(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_e_1170_, uint8_t v_alsoCasesOn_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = l_Lean_Expr_isApp(v_e_1170_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Expr_getAppFn(v_e_1170_);
if (lean_obj_tag(v___x_1187_) == 4)
{
lean_object* v_declName_1188_; lean_object* v_us_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1345_; 
v_declName_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_declName_1188_);
v_us_1189_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_us_1189_);
lean_dec_ref(v___x_1187_);
lean_inc(v_declName_1188_);
v___x_1190_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_1188_, v___y_1179_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1345_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1345_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
if (lean_obj_tag(v_a_1191_) == 1)
{
lean_object* v_val_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
v_val_1195_ = lean_ctor_get(v_a_1191_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1191_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1197_ = v_a_1191_;
v_isShared_1198_ = v_isSharedCheck_1237_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_val_1195_);
lean_dec(v_a_1191_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1237_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_dummy_1199_; lean_object* v_nargs_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_args_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_dummy_1199_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_1200_ = l_Lean_Expr_getAppNumArgs(v_e_1170_);
lean_inc(v_nargs_1200_);
v___x_1201_ = lean_mk_array(v_nargs_1200_, v_dummy_1199_);
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_sub(v_nargs_1200_, v___x_1202_);
lean_dec(v_nargs_1200_);
v_args_1204_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1170_, v___x_1201_, v___x_1203_);
v___x_1205_ = lean_array_get_size(v_args_1204_);
v___x_1206_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1195_);
v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
lean_dec(v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v_numParams_1208_; lean_object* v_numDiscrs_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v_numParams_1208_ = lean_ctor_get(v_val_1195_, 0);
v_numDiscrs_1209_ = lean_ctor_get(v_val_1195_, 1);
v___x_1210_ = lean_array_mk(v_us_1189_);
v___x_1211_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1208_);
v___x_1212_ = l_Array_extract___redArg(v_args_1204_, v___x_1211_, v_numParams_1208_);
v___x_1213_ = l_Lean_instInhabitedExpr;
v___x_1214_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1195_);
v___x_1215_ = lean_array_get(v___x_1213_, v_args_1204_, v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_nat_add(v_numParams_1208_, v___x_1202_);
v___x_1217_ = lean_nat_add(v___x_1216_, v_numDiscrs_1209_);
lean_inc(v___x_1217_);
lean_inc_ref(v_args_1204_);
v___x_1218_ = l_Array_toSubarray___redArg(v_args_1204_, v___x_1216_, v___x_1217_);
v___x_1219_ = l_Subarray_copy___redArg(v___x_1218_);
v___x_1220_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1195_);
v___x_1221_ = lean_nat_add(v___x_1217_, v___x_1220_);
lean_dec(v___x_1220_);
lean_inc(v___x_1221_);
lean_inc_ref(v_args_1204_);
v___x_1222_ = l_Array_toSubarray___redArg(v_args_1204_, v___x_1217_, v___x_1221_);
v___x_1223_ = l_Subarray_copy___redArg(v___x_1222_);
v___x_1224_ = l_Array_toSubarray___redArg(v_args_1204_, v___x_1221_, v___x_1205_);
v___x_1225_ = l_Subarray_copy___redArg(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1226_, 0, v_val_1195_);
lean_ctor_set(v___x_1226_, 1, v_declName_1188_);
lean_ctor_set(v___x_1226_, 2, v___x_1210_);
lean_ctor_set(v___x_1226_, 3, v___x_1212_);
lean_ctor_set(v___x_1226_, 4, v___x_1215_);
lean_ctor_set(v___x_1226_, 5, v___x_1219_);
lean_ctor_set(v___x_1226_, 6, v___x_1223_);
lean_ctor_set(v___x_1226_, 7, v___x_1225_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1226_);
v___x_1228_ = v___x_1197_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1228_);
v___x_1230_ = v___x_1193_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
lean_dec_ref(v_args_1204_);
lean_del_object(v___x_1197_);
lean_dec(v_val_1195_);
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
v___x_1233_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1233_);
v___x_1235_ = v___x_1193_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v___x_1238_; 
lean_del_object(v___x_1193_);
lean_dec(v_a_1191_);
v___x_1238_ = lean_st_ref_get(v___y_1179_);
if (v_alsoCasesOn_1171_ == 0)
{
lean_dec(v___x_1238_);
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
goto v___jp_1181_;
}
else
{
lean_object* v_env_1239_; uint8_t v___x_1240_; 
v_env_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_env_1239_);
lean_dec(v___x_1238_);
lean_inc(v_declName_1188_);
v___x_1240_ = l_Lean_isCasesOnRecursor(v_env_1239_, v_declName_1188_);
if (v___x_1240_ == 0)
{
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
goto v___jp_1181_;
}
else
{
lean_object* v_indName_1241_; lean_object* v___x_1242_; 
v_indName_1241_ = l_Lean_Name_getPrefix(v_declName_1188_);
lean_inc_ref(v___y_1178_);
v___x_1242_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_indName_1241_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1336_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1336_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1336_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
if (lean_obj_tag(v_a_1243_) == 5)
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1331_; 
v_val_1247_ = lean_ctor_get(v_a_1243_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_a_1243_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1249_ = v_a_1243_;
v_isShared_1250_ = v_isSharedCheck_1331_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v_a_1243_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1331_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_toConstantVal_1251_; lean_object* v_numParams_1252_; lean_object* v_numIndices_1253_; lean_object* v_ctors_1254_; lean_object* v_nargs_1255_; lean_object* v_dummy_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_args_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_toConstantVal_1251_ = lean_ctor_get(v_val_1247_, 0);
lean_inc_ref(v_toConstantVal_1251_);
v_numParams_1252_ = lean_ctor_get(v_val_1247_, 1);
lean_inc(v_numParams_1252_);
v_numIndices_1253_ = lean_ctor_get(v_val_1247_, 2);
lean_inc(v_numIndices_1253_);
v_ctors_1254_ = lean_ctor_get(v_val_1247_, 4);
lean_inc(v_ctors_1254_);
v_nargs_1255_ = l_Lean_Expr_getAppNumArgs(v_e_1170_);
v_dummy_1256_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v_nargs_1255_);
v___x_1257_ = lean_mk_array(v_nargs_1255_, v_dummy_1256_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_sub(v_nargs_1255_, v___x_1258_);
lean_dec(v_nargs_1255_);
v_args_1260_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1170_, v___x_1257_, v___x_1259_);
v___x_1261_ = lean_nat_add(v_numParams_1252_, v___x_1258_);
v___x_1262_ = lean_nat_add(v___x_1261_, v_numIndices_1253_);
v___x_1263_ = lean_nat_add(v___x_1262_, v___x_1258_);
lean_dec(v___x_1262_);
v___x_1264_ = l_Lean_InductiveVal_numCtors(v_val_1247_);
lean_dec_ref(v_val_1247_);
v___x_1265_ = lean_nat_add(v___x_1263_, v___x_1264_);
lean_dec(v___x_1264_);
v___x_1266_ = lean_array_get_size(v_args_1260_);
v___x_1267_ = lean_nat_dec_le(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec(v___x_1265_);
lean_dec(v___x_1263_);
lean_dec(v___x_1261_);
lean_dec_ref(v_args_1260_);
lean_dec(v_ctors_1254_);
lean_dec(v_numIndices_1253_);
lean_dec(v_numParams_1252_);
lean_dec_ref(v_toConstantVal_1251_);
lean_del_object(v___x_1249_);
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
v___x_1268_ = lean_box(0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1268_);
v___x_1270_ = v___x_1245_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v_params_1273_; lean_object* v___x_1274_; lean_object* v_motive_1275_; lean_object* v_discrs_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_discrInfos_1279_; lean_object* v_alts_1280_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v_lower_1322_; lean_object* v_upper_1323_; uint8_t v___x_1330_; 
lean_del_object(v___x_1245_);
v___x_1272_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1252_);
lean_inc_ref(v_args_1260_);
v_params_1273_ = l_Array_toSubarray___redArg(v_args_1260_, v___x_1272_, v_numParams_1252_);
v___x_1274_ = l_Lean_instInhabitedExpr;
v_motive_1275_ = lean_array_get(v___x_1274_, v_args_1260_, v_numParams_1252_);
lean_dec(v_numParams_1252_);
lean_inc(v___x_1263_);
lean_inc_ref(v_args_1260_);
v_discrs_1276_ = l_Array_toSubarray___redArg(v_args_1260_, v___x_1261_, v___x_1263_);
v___x_1277_ = lean_nat_add(v_numIndices_1253_, v___x_1258_);
lean_dec(v_numIndices_1253_);
v___x_1278_ = lean_box(0);
v_discrInfos_1279_ = lean_mk_array(v___x_1277_, v___x_1278_);
lean_inc(v___x_1265_);
lean_inc_ref(v_args_1260_);
v_alts_1280_ = l_Array_toSubarray___redArg(v_args_1260_, v___x_1263_, v___x_1265_);
v___x_1330_ = lean_nat_dec_le(v___x_1265_, v___x_1272_);
if (v___x_1330_ == 0)
{
v_lower_1322_ = v___x_1265_;
v_upper_1323_ = v___x_1266_;
goto v___jp_1321_;
}
else
{
lean_dec(v___x_1265_);
v_lower_1322_ = v___x_1272_;
v_upper_1323_ = v___x_1266_;
goto v___jp_1321_;
}
v___jp_1281_:
{
lean_object* v___x_1284_; size_t v_sz_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_array_mk(v_ctors_1254_);
v_sz_1285_ = lean_array_size(v___x_1284_);
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(v_sz_1285_, v___x_1286_, v___x_1284_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1312_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_start_1292_; lean_object* v_stop_1293_; lean_object* v_start_1294_; lean_object* v_stop_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_start_1292_ = lean_ctor_get(v_params_1273_, 1);
lean_inc(v_start_1292_);
v_stop_1293_ = lean_ctor_get(v_params_1273_, 2);
lean_inc(v_stop_1293_);
v_start_1294_ = lean_ctor_get(v_discrs_1276_, 1);
lean_inc(v_start_1294_);
v_stop_1295_ = lean_ctor_get(v_discrs_1276_, 2);
lean_inc(v_stop_1295_);
v___x_1296_ = lean_nat_sub(v_stop_1293_, v_start_1292_);
lean_dec(v_start_1292_);
lean_dec(v_stop_1293_);
v___x_1297_ = lean_nat_sub(v_stop_1295_, v_start_1294_);
lean_dec(v_start_1294_);
lean_dec(v_stop_1295_);
v___x_1298_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2);
v___x_1299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1296_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v_a_1288_);
lean_ctor_set(v___x_1299_, 3, v___y_1283_);
lean_ctor_set(v___x_1299_, 4, v_discrInfos_1279_);
lean_ctor_set(v___x_1299_, 5, v___x_1298_);
v___x_1300_ = lean_array_mk(v_us_1189_);
v___x_1301_ = l_Subarray_copy___redArg(v_params_1273_);
v___x_1302_ = l_Subarray_copy___redArg(v_discrs_1276_);
v___x_1303_ = l_Subarray_copy___redArg(v_alts_1280_);
v___x_1304_ = l_Subarray_copy___redArg(v___y_1282_);
v___x_1305_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1299_);
lean_ctor_set(v___x_1305_, 1, v_declName_1188_);
lean_ctor_set(v___x_1305_, 2, v___x_1300_);
lean_ctor_set(v___x_1305_, 3, v___x_1301_);
lean_ctor_set(v___x_1305_, 4, v_motive_1275_);
lean_ctor_set(v___x_1305_, 5, v___x_1302_);
lean_ctor_set(v___x_1305_, 6, v___x_1303_);
lean_ctor_set(v___x_1305_, 7, v___x_1304_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 1);
lean_ctor_set(v___x_1249_, 0, v___x_1305_);
v___x_1307_ = v___x_1249_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1307_);
v___x_1309_ = v___x_1290_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_alts_1280_);
lean_dec_ref(v_discrInfos_1279_);
lean_dec_ref(v_discrs_1276_);
lean_dec(v_motive_1275_);
lean_dec_ref(v_params_1273_);
lean_del_object(v___x_1249_);
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
v_a_1313_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1287_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1287_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
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
v___jp_1321_:
{
lean_object* v_levelParams_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_levelParams_1324_ = lean_ctor_get(v_toConstantVal_1251_, 1);
lean_inc(v_levelParams_1324_);
lean_dec_ref(v_toConstantVal_1251_);
v___x_1325_ = l_Array_toSubarray___redArg(v_args_1260_, v_lower_1322_, v_upper_1323_);
v___x_1326_ = l_List_lengthTR___redArg(v_levelParams_1324_);
lean_dec(v_levelParams_1324_);
v___x_1327_ = l_List_lengthTR___redArg(v_us_1189_);
v___x_1328_ = lean_nat_dec_eq(v___x_1326_, v___x_1327_);
lean_dec(v___x_1327_);
lean_dec(v___x_1326_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3));
v___y_1282_ = v___x_1325_;
v___y_1283_ = v___x_1329_;
goto v___jp_1281_;
}
else
{
v___y_1282_ = v___x_1325_;
v___y_1283_ = v___x_1278_;
goto v___jp_1281_;
}
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_a_1243_);
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
v___x_1332_ = lean_box(0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1332_);
v___x_1334_ = v___x_1245_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_us_1189_);
lean_dec(v_declName_1188_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
v_a_1337_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1242_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1242_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
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
}
}
}
}
else
{
lean_dec_ref(v___x_1187_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_e_1170_);
goto v___jp_1181_;
}
}
v___jp_1181_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_e_1346_, lean_object* v_alsoCasesOn_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1357_; lean_object* v_res_1358_; 
v_alsoCasesOn_boxed_1357_ = lean_unbox(v_alsoCasesOn_1347_);
v_res_1358_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_1346_, v_alsoCasesOn_boxed_1357_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(lean_object* v_k_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v_b_1364_, lean_object* v_c_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_apply_11(v_k_1359_, v_b_1364_, v_c_1365_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, lean_box(0));
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed(lean_object* v_k_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v_b_1377_, lean_object* v_c_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(v_k_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v_b_1377_, v_c_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(lean_object* v_e_1385_, lean_object* v_maxFVars_1386_, lean_object* v_k_1387_, uint8_t v_cleanupAnnotations_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___f_1398_; uint8_t v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1398_, 0, v_k_1387_);
lean_closure_set(v___f_1398_, 1, v___y_1389_);
lean_closure_set(v___f_1398_, 2, v___y_1390_);
lean_closure_set(v___f_1398_, 3, v___y_1391_);
lean_closure_set(v___f_1398_, 4, v___y_1392_);
v___x_1399_ = 1;
v___x_1400_ = 0;
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_maxFVars_1386_);
v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1385_, v___x_1399_, v___x_1400_, v___x_1399_, v___x_1400_, v___x_1401_, v___f_1398_, v_cleanupAnnotations_1388_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
return v___x_1402_;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___boxed(lean_object* v_e_1411_, lean_object* v_maxFVars_1412_, lean_object* v_k_1413_, lean_object* v_cleanupAnnotations_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1424_; lean_object* v_res_1425_; 
v_cleanupAnnotations_boxed_1424_ = lean_unbox(v_cleanupAnnotations_1414_);
v_res_1425_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_1411_, v_maxFVars_1412_, v_k_1413_, v_cleanupAnnotations_boxed_1424_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(lean_object* v_name_1426_, lean_object* v_type_1427_, lean_object* v_val_1428_, lean_object* v_k_1429_, uint8_t v_nondep_1430_, uint8_t v_kind_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___f_1441_; lean_object* v___x_1442_; 
v___f_1441_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1441_, 0, v_k_1429_);
lean_closure_set(v___f_1441_, 1, v___y_1432_);
lean_closure_set(v___f_1441_, 2, v___y_1433_);
lean_closure_set(v___f_1441_, 3, v___y_1434_);
lean_closure_set(v___f_1441_, 4, v___y_1435_);
v___x_1442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1426_, v_type_1427_, v_val_1428_, v___f_1441_, v_nondep_1430_, v_kind_1431_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg___boxed(lean_object* v_name_1451_, lean_object* v_type_1452_, lean_object* v_val_1453_, lean_object* v_k_1454_, lean_object* v_nondep_1455_, lean_object* v_kind_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_nondep_boxed_1466_; uint8_t v_kind_boxed_1467_; lean_object* v_res_1468_; 
v_nondep_boxed_1466_ = lean_unbox(v_nondep_1455_);
v_kind_boxed_1467_ = lean_unbox(v_kind_1456_);
v_res_1468_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_1451_, v_type_1452_, v_val_1453_, v_k_1454_, v_nondep_boxed_1466_, v_kind_boxed_1467_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(lean_object* v_k_1469_, uint8_t v_usedLetOnly_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc_ref(v_x_1471_);
v___x_1481_ = lean_apply_10(v_k_1469_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_mk_empty_array_with_capacity(v___x_1483_);
v___x_1485_ = lean_array_push(v___x_1484_, v_x_1471_);
v___x_1486_ = 0;
v___x_1487_ = 1;
v___x_1488_ = l_Lean_Meta_mkLetFVars(v___x_1485_, v_a_1482_, v_usedLetOnly_1470_, v___x_1486_, v___x_1487_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___x_1485_);
return v___x_1488_;
}
else
{
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_x_1471_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed(lean_object* v_k_1489_, lean_object* v_usedLetOnly_1490_, lean_object* v_x_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_usedLetOnly_boxed_1501_; lean_object* v_res_1502_; 
v_usedLetOnly_boxed_1501_ = lean_unbox(v_usedLetOnly_1490_);
v_res_1502_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(v_k_1489_, v_usedLetOnly_boxed_1501_, v_x_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_name_1503_, lean_object* v_type_1504_, lean_object* v_val_1505_, lean_object* v_k_1506_, uint8_t v_nondep_1507_, uint8_t v_kind_1508_, uint8_t v_usedLetOnly_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(v_usedLetOnly_1509_);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1520_, 0, v_k_1506_);
lean_closure_set(v___f_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_1503_, v_type_1504_, v_val_1505_, v___f_1520_, v_nondep_1507_, v_kind_1508_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_name_1522_, lean_object* v_type_1523_, lean_object* v_val_1524_, lean_object* v_k_1525_, lean_object* v_nondep_1526_, lean_object* v_kind_1527_, lean_object* v_usedLetOnly_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_nondep_boxed_1538_; uint8_t v_kind_boxed_1539_; uint8_t v_usedLetOnly_boxed_1540_; lean_object* v_res_1541_; 
v_nondep_boxed_1538_ = lean_unbox(v_nondep_1526_);
v_kind_boxed_1539_ = lean_unbox(v_kind_1527_);
v_usedLetOnly_boxed_1540_ = lean_unbox(v_usedLetOnly_1528_);
v_res_1541_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_name_1522_, v_type_1523_, v_val_1524_, v_k_1525_, v_nondep_boxed_1538_, v_kind_boxed_1539_, v_usedLetOnly_boxed_1540_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_opts_1542_, lean_object* v_opt_1543_){
_start:
{
lean_object* v_name_1544_; lean_object* v_defValue_1545_; lean_object* v_map_1546_; lean_object* v___x_1547_; 
v_name_1544_ = lean_ctor_get(v_opt_1543_, 0);
v_defValue_1545_ = lean_ctor_get(v_opt_1543_, 1);
v_map_1546_ = lean_ctor_get(v_opts_1542_, 0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1546_, v_name_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_unbox(v_defValue_1545_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1549_);
lean_dec_ref(v___x_1547_);
if (lean_obj_tag(v_val_1549_) == 1)
{
uint8_t v_v_1550_; 
v_v_1550_ = lean_ctor_get_uint8(v_val_1549_, 0);
lean_dec_ref(v_val_1549_);
return v_v_1550_;
}
else
{
uint8_t v___x_1551_; 
lean_dec(v_val_1549_);
v___x_1551_ = lean_unbox(v_defValue_1545_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_opts_1552_, lean_object* v_opt_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_opts_1552_, v_opt_1553_);
lean_dec_ref(v_opt_1553_);
lean_dec_ref(v_opts_1552_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
uint8_t v___x_1558_; 
v___x_1558_ = 0;
return v___x_1558_;
}
else
{
lean_object* v_key_1559_; lean_object* v_tail_1560_; uint8_t v___x_1561_; 
v_key_1559_ = lean_ctor_get(v_x_1557_, 0);
v_tail_1560_ = lean_ctor_get(v_x_1557_, 2);
v___x_1561_ = lean_expr_eqv(v_key_1559_, v_a_1556_);
if (v___x_1561_ == 0)
{
v_x_1557_ = v_tail_1560_;
goto _start;
}
else
{
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg___boxed(lean_object* v_a_1563_, lean_object* v_x_1564_){
_start:
{
uint8_t v_res_1565_; lean_object* v_r_1566_; 
v_res_1565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_1563_, v_x_1564_);
lean_dec(v_x_1564_);
lean_dec_ref(v_a_1563_);
v_r_1566_ = lean_box(v_res_1565_);
return v_r_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(lean_object* v_a_1567_, lean_object* v_b_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_dec(v_b_1568_);
lean_dec_ref(v_a_1567_);
return v_x_1569_;
}
else
{
lean_object* v_key_1570_; lean_object* v_value_1571_; lean_object* v_tail_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1584_; 
v_key_1570_ = lean_ctor_get(v_x_1569_, 0);
v_value_1571_ = lean_ctor_get(v_x_1569_, 1);
v_tail_1572_ = lean_ctor_get(v_x_1569_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1574_ = v_x_1569_;
v_isShared_1575_ = v_isSharedCheck_1584_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_tail_1572_);
lean_inc(v_value_1571_);
lean_inc(v_key_1570_);
lean_dec(v_x_1569_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1584_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_expr_eqv(v_key_1570_, v_a_1567_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_1567_, v_b_1568_, v_tail_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 2, v___x_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_key_1570_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_value_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
else
{
lean_object* v___x_1582_; 
lean_dec(v_value_1571_);
lean_dec(v_key_1570_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v_b_1568_);
lean_ctor_set(v___x_1574_, 0, v_a_1567_);
v___x_1582_ = v___x_1574_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1567_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_b_1568_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_tail_1572_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
if (lean_obj_tag(v_x_1586_) == 0)
{
return v_x_1585_;
}
else
{
lean_object* v_key_1587_; lean_object* v_value_1588_; lean_object* v_tail_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1612_; 
v_key_1587_ = lean_ctor_get(v_x_1586_, 0);
v_value_1588_ = lean_ctor_get(v_x_1586_, 1);
v_tail_1589_ = lean_ctor_get(v_x_1586_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1591_ = v_x_1586_;
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_tail_1589_);
lean_inc(v_value_1588_);
lean_inc(v_key_1587_);
lean_dec(v_x_1586_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; uint64_t v___x_1594_; uint64_t v___x_1595_; uint64_t v___x_1596_; uint64_t v_fold_1597_; uint64_t v___x_1598_; uint64_t v___x_1599_; uint64_t v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1593_ = lean_array_get_size(v_x_1585_);
v___x_1594_ = l_Lean_Expr_hash(v_key_1587_);
v___x_1595_ = 32ULL;
v___x_1596_ = lean_uint64_shift_right(v___x_1594_, v___x_1595_);
v_fold_1597_ = lean_uint64_xor(v___x_1594_, v___x_1596_);
v___x_1598_ = 16ULL;
v___x_1599_ = lean_uint64_shift_right(v_fold_1597_, v___x_1598_);
v___x_1600_ = lean_uint64_xor(v_fold_1597_, v___x_1599_);
v___x_1601_ = lean_uint64_to_usize(v___x_1600_);
v___x_1602_ = lean_usize_of_nat(v___x_1593_);
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_sub(v___x_1602_, v___x_1603_);
v___x_1605_ = lean_usize_land(v___x_1601_, v___x_1604_);
v___x_1606_ = lean_array_uget_borrowed(v_x_1585_, v___x_1605_);
lean_inc(v___x_1606_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 2, v___x_1606_);
v___x_1608_ = v___x_1591_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_key_1587_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_value_1588_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_array_uset(v_x_1585_, v___x_1605_, v___x_1608_);
v_x_1585_ = v___x_1609_;
v_x_1586_ = v_tail_1589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(lean_object* v_i_1613_, lean_object* v_source_1614_, lean_object* v_target_1615_){
_start:
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = lean_array_get_size(v_source_1614_);
v___x_1617_ = lean_nat_dec_lt(v_i_1613_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_source_1614_);
lean_dec(v_i_1613_);
return v_target_1615_;
}
else
{
lean_object* v_es_1618_; lean_object* v___x_1619_; lean_object* v_source_1620_; lean_object* v_target_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_es_1618_ = lean_array_fget(v_source_1614_, v_i_1613_);
v___x_1619_ = lean_box(0);
v_source_1620_ = lean_array_fset(v_source_1614_, v_i_1613_, v___x_1619_);
v_target_1621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(v_target_1615_, v_es_1618_);
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_add(v_i_1613_, v___x_1622_);
lean_dec(v_i_1613_);
v_i_1613_ = v___x_1623_;
v_source_1614_ = v_source_1620_;
v_target_1615_ = v_target_1621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(lean_object* v_data_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_nbuckets_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1626_ = lean_array_get_size(v_data_1625_);
v___x_1627_ = lean_unsigned_to_nat(2u);
v_nbuckets_1628_ = lean_nat_mul(v___x_1626_, v___x_1627_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_mk_array(v_nbuckets_1628_, v___x_1630_);
v___x_1632_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(v___x_1629_, v_data_1625_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(lean_object* v_m_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_){
_start:
{
lean_object* v_size_1636_; lean_object* v_buckets_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1680_; 
v_size_1636_ = lean_ctor_get(v_m_1633_, 0);
v_buckets_1637_ = lean_ctor_get(v_m_1633_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_m_1633_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1639_ = v_m_1633_;
v_isShared_1640_ = v_isSharedCheck_1680_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_buckets_1637_);
lean_inc(v_size_1636_);
lean_dec(v_m_1633_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1680_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v_fold_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v_bkt_1654_; uint8_t v___x_1655_; 
v___x_1641_ = lean_array_get_size(v_buckets_1637_);
v___x_1642_ = l_Lean_Expr_hash(v_a_1634_);
v___x_1643_ = 32ULL;
v___x_1644_ = lean_uint64_shift_right(v___x_1642_, v___x_1643_);
v_fold_1645_ = lean_uint64_xor(v___x_1642_, v___x_1644_);
v___x_1646_ = 16ULL;
v___x_1647_ = lean_uint64_shift_right(v_fold_1645_, v___x_1646_);
v___x_1648_ = lean_uint64_xor(v_fold_1645_, v___x_1647_);
v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
v___x_1650_ = lean_usize_of_nat(v___x_1641_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_sub(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_usize_land(v___x_1649_, v___x_1652_);
v_bkt_1654_ = lean_array_uget_borrowed(v_buckets_1637_, v___x_1653_);
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_1634_, v_bkt_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v_size_x27_1657_; lean_object* v___x_1658_; lean_object* v_buckets_x27_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1656_ = lean_unsigned_to_nat(1u);
v_size_x27_1657_ = lean_nat_add(v_size_1636_, v___x_1656_);
lean_dec(v_size_1636_);
lean_inc(v_bkt_1654_);
v___x_1658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1658_, 0, v_a_1634_);
lean_ctor_set(v___x_1658_, 1, v_b_1635_);
lean_ctor_set(v___x_1658_, 2, v_bkt_1654_);
v_buckets_x27_1659_ = lean_array_uset(v_buckets_1637_, v___x_1653_, v___x_1658_);
v___x_1660_ = lean_unsigned_to_nat(4u);
v___x_1661_ = lean_nat_mul(v_size_x27_1657_, v___x_1660_);
v___x_1662_ = lean_unsigned_to_nat(3u);
v___x_1663_ = lean_nat_div(v___x_1661_, v___x_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_array_get_size(v_buckets_x27_1659_);
v___x_1665_ = lean_nat_dec_le(v___x_1663_, v___x_1664_);
lean_dec(v___x_1663_);
if (v___x_1665_ == 0)
{
lean_object* v_val_1666_; lean_object* v___x_1668_; 
v_val_1666_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(v_buckets_x27_1659_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v_val_1666_);
lean_ctor_set(v___x_1639_, 0, v_size_x27_1657_);
v___x_1668_ = v___x_1639_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_size_x27_1657_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_val_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v___x_1671_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v_buckets_x27_1659_);
lean_ctor_set(v___x_1639_, 0, v_size_x27_1657_);
v___x_1671_ = v___x_1639_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_size_x27_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_buckets_x27_1659_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v_buckets_x27_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_inc(v_bkt_1654_);
v___x_1673_ = lean_box(0);
v_buckets_x27_1674_ = lean_array_uset(v_buckets_1637_, v___x_1653_, v___x_1673_);
v___x_1675_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_1634_, v_b_1635_, v_bkt_1654_);
v___x_1676_ = lean_array_uset(v_buckets_x27_1674_, v___x_1653_, v___x_1675_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v___x_1676_);
v___x_1678_ = v___x_1639_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_size_1636_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(lean_object* v_a_1681_, lean_object* v_x_1682_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg___boxed(lean_object* v_a_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_1690_, v_x_1691_);
lean_dec(v_x_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(lean_object* v_m_1693_, lean_object* v_a_1694_){
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
v___x_1710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_1694_, v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_m_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_1711_, v_a_1712_);
lean_dec_ref(v_a_1712_);
lean_dec_ref(v_m_1711_);
return v_res_1713_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1714_; double v___x_1715_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_float_of_nat(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(lean_object* v_cls_1719_, lean_object* v_msg_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_ref_1726_; lean_object* v___x_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1772_; 
v_ref_1726_ = lean_ctor_get(v___y_1723_, 5);
v___x_1727_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1772_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1772_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v_traceState_1733_; lean_object* v_env_1734_; lean_object* v_nextMacroScope_1735_; lean_object* v_ngen_1736_; lean_object* v_auxDeclNGen_1737_; lean_object* v_cache_1738_; lean_object* v_messages_1739_; lean_object* v_infoState_1740_; lean_object* v_snapshotTasks_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1771_; 
v___x_1732_ = lean_st_ref_take(v___y_1724_);
v_traceState_1733_ = lean_ctor_get(v___x_1732_, 4);
v_env_1734_ = lean_ctor_get(v___x_1732_, 0);
v_nextMacroScope_1735_ = lean_ctor_get(v___x_1732_, 1);
v_ngen_1736_ = lean_ctor_get(v___x_1732_, 2);
v_auxDeclNGen_1737_ = lean_ctor_get(v___x_1732_, 3);
v_cache_1738_ = lean_ctor_get(v___x_1732_, 5);
v_messages_1739_ = lean_ctor_get(v___x_1732_, 6);
v_infoState_1740_ = lean_ctor_get(v___x_1732_, 7);
v_snapshotTasks_1741_ = lean_ctor_get(v___x_1732_, 8);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1743_ = v___x_1732_;
v_isShared_1744_ = v_isSharedCheck_1771_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snapshotTasks_1741_);
lean_inc(v_infoState_1740_);
lean_inc(v_messages_1739_);
lean_inc(v_cache_1738_);
lean_inc(v_traceState_1733_);
lean_inc(v_auxDeclNGen_1737_);
lean_inc(v_ngen_1736_);
lean_inc(v_nextMacroScope_1735_);
lean_inc(v_env_1734_);
lean_dec(v___x_1732_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1771_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
uint64_t v_tid_1745_; lean_object* v_traces_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1770_; 
v_tid_1745_ = lean_ctor_get_uint64(v_traceState_1733_, sizeof(void*)*1);
v_traces_1746_ = lean_ctor_get(v_traceState_1733_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_traceState_1733_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1748_ = v_traceState_1733_;
v_isShared_1749_ = v_isSharedCheck_1770_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_traces_1746_);
lean_dec(v_traceState_1733_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1770_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; double v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0);
v___x_1752_ = 0;
v___x_1753_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1));
v___x_1754_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1754_, 0, v_cls_1719_);
lean_ctor_set(v___x_1754_, 1, v___x_1750_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
lean_ctor_set_float(v___x_1754_, sizeof(void*)*3, v___x_1751_);
lean_ctor_set_float(v___x_1754_, sizeof(void*)*3 + 8, v___x_1751_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*3 + 16, v___x_1752_);
v___x_1755_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2));
v___x_1756_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v_a_1728_);
lean_ctor_set(v___x_1756_, 2, v___x_1755_);
lean_inc(v_ref_1726_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_ref_1726_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_PersistentArray_push___redArg(v_traces_1746_, v___x_1757_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1758_);
v___x_1760_ = v___x_1748_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1758_);
lean_ctor_set_uint64(v_reuseFailAlloc_1769_, sizeof(void*)*1, v_tid_1745_);
v___x_1760_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 4, v___x_1760_);
v___x_1762_ = v___x_1743_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_env_1734_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_nextMacroScope_1735_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_ngen_1736_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_auxDeclNGen_1737_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1768_, 5, v_cache_1738_);
lean_ctor_set(v_reuseFailAlloc_1768_, 6, v_messages_1739_);
lean_ctor_set(v_reuseFailAlloc_1768_, 7, v_infoState_1740_);
lean_ctor_set(v_reuseFailAlloc_1768_, 8, v_snapshotTasks_1741_);
v___x_1762_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_st_ref_set(v___y_1724_, v___x_1762_);
v___x_1764_ = lean_box(0);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1764_);
v___x_1766_ = v___x_1730_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___boxed(lean_object* v_cls_1773_, lean_object* v_msg_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_1773_, v_msg_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1781_, lean_object* v_b_1782_){
_start:
{
lean_object* v_array_1783_; lean_object* v_start_1784_; lean_object* v_stop_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1798_; 
v_array_1783_ = lean_ctor_get(v_a_1781_, 0);
v_start_1784_ = lean_ctor_get(v_a_1781_, 1);
v_stop_1785_ = lean_ctor_get(v_a_1781_, 2);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_a_1781_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1787_ = v_a_1781_;
v_isShared_1788_ = v_isSharedCheck_1798_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_stop_1785_);
lean_inc(v_start_1784_);
lean_inc(v_array_1783_);
lean_dec(v_a_1781_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1798_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_lt(v_start_1784_, v_stop_1785_);
if (v___x_1789_ == 0)
{
lean_del_object(v___x_1787_);
lean_dec(v_stop_1785_);
lean_dec(v_start_1784_);
lean_dec_ref(v_array_1783_);
return v_b_1782_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_add(v_start_1784_, v___x_1790_);
lean_inc_ref(v_array_1783_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1791_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_array_1783_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_stop_1785_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_array_fget(v_array_1783_, v_start_1784_);
lean_dec(v_start_1784_);
lean_dec_ref(v_array_1783_);
v___x_1795_ = lean_array_push(v_b_1782_, v___x_1794_);
v_a_1781_ = v___x_1793_;
v_b_1782_ = v___x_1795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1799_, lean_object* v_recFnName_1800_, lean_object* v_fixedPrefixSize_1801_, lean_object* v_F_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_expr_instantiate1(v_body_1799_, v_x_1803_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
v___x_1814_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1800_, v_fixedPrefixSize_1801_, v_F_1802_, v___x_1813_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; uint8_t v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1816_);
v___x_1818_ = lean_array_push(v___x_1817_, v_x_1803_);
v___x_1819_ = 0;
v___x_1820_ = 1;
v___x_1821_ = 1;
v___x_1822_ = l_Lean_Meta_mkLambdaFVars(v___x_1818_, v_a_1815_, v___x_1819_, v___x_1820_, v___x_1819_, v___x_1820_, v___x_1821_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___x_1818_);
return v___x_1822_;
}
else
{
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_x_1803_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1823_, lean_object* v_recFnName_1824_, lean_object* v_fixedPrefixSize_1825_, lean_object* v_F_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1823_, v_recFnName_1824_, v_fixedPrefixSize_1825_, v_F_1826_, v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v_body_1823_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1838_, lean_object* v_recFnName_1839_, lean_object* v_fixedPrefixSize_1840_, lean_object* v_F_1841_, lean_object* v_x_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_expr_instantiate1(v_body_1838_, v_x_1842_);
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1847_);
v___x_1853_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1839_, v_fixedPrefixSize_1840_, v_F_1841_, v___x_1852_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; uint8_t v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1857_ = lean_array_push(v___x_1856_, v_x_1842_);
v___x_1858_ = 0;
v___x_1859_ = 1;
v___x_1860_ = 1;
v___x_1861_ = l_Lean_Meta_mkForallFVars(v___x_1857_, v_a_1854_, v___x_1858_, v___x_1859_, v___x_1859_, v___x_1860_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___x_1857_);
return v___x_1861_;
}
else
{
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v_x_1842_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1862_, lean_object* v_recFnName_1863_, lean_object* v_fixedPrefixSize_1864_, lean_object* v_F_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1862_, v_recFnName_1863_, v_fixedPrefixSize_1864_, v_F_1865_, v_x_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec_ref(v_body_1862_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1877_, lean_object* v_recFnName_1878_, lean_object* v_fixedPrefixSize_1879_, lean_object* v_F_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1877_, v_recFnName_1878_, v_fixedPrefixSize_1879_, v_F_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec_ref(v_x_1881_);
lean_dec_ref(v_body_1877_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1894_, lean_object* v_fixedPrefixSize_1895_, lean_object* v_F_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_bs_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v_F_1896_);
lean_dec(v_fixedPrefixSize_1895_);
lean_dec(v_recFnName_1894_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_bs_1899_);
return v___x_1910_;
}
else
{
lean_object* v_v_1911_; lean_object* v___x_1912_; 
v_v_1911_ = lean_array_uget_borrowed(v_bs_1899_, v_i_1898_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc(v___y_1900_);
lean_inc(v_v_1911_);
lean_inc_ref(v_F_1896_);
lean_inc(v_fixedPrefixSize_1895_);
lean_inc(v_recFnName_1894_);
v___x_1912_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1894_, v_fixedPrefixSize_1895_, v_F_1896_, v_v_1911_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v_bs_x27_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v_bs_x27_1915_ = lean_array_uset(v_bs_1899_, v_i_1898_, v___x_1914_);
v___x_1916_ = ((size_t)1ULL);
v___x_1917_ = lean_usize_add(v_i_1898_, v___x_1916_);
v___x_1918_ = lean_array_uset(v_bs_x27_1915_, v_i_1898_, v_a_1913_);
v_i_1898_ = v___x_1917_;
v_bs_1899_ = v___x_1918_;
goto _start;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v_bs_1899_);
lean_dec_ref(v_F_1896_);
lean_dec(v_fixedPrefixSize_1895_);
lean_dec(v_recFnName_1894_);
v_a_1920_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1912_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1912_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1935_, lean_object* v_fixedPrefixSize_1936_, lean_object* v_F_1937_, lean_object* v_e_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1960_ = l_Lean_Expr_getAppNumArgs(v_e_1938_);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_add(v_fixedPrefixSize_1936_, v___x_1961_);
v___x_1963_ = lean_nat_dec_lt(v___x_1960_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v_dummy_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_args_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_dummy_1964_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_1960_);
v___x_1965_ = lean_mk_array(v___x_1960_, v_dummy_1964_);
v___x_1966_ = lean_nat_sub(v___x_1960_, v___x_1961_);
lean_dec(v___x_1960_);
v_args_1967_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1938_, v___x_1965_, v___x_1966_);
v___x_1968_ = l_Lean_instInhabitedExpr;
v___x_1969_ = lean_array_get(v___x_1968_, v_args_1967_, v_fixedPrefixSize_1936_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
lean_inc(v_a_1940_);
lean_inc(v_a_1939_);
lean_inc_ref(v_F_1937_);
lean_inc(v_fixedPrefixSize_1936_);
lean_inc(v_recFnName_1935_);
v___x_1970_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1935_, v_fixedPrefixSize_1936_, v_F_1937_, v___x_1969_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
lean_inc_ref(v_F_1937_);
v___x_1972_ = l_Lean_Expr_app___override(v_F_1937_, v_a_1971_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc_ref(v___x_1972_);
v___x_1973_ = lean_infer_type(v___x_1972_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_1975_ = lean_whnf(v_a_1974_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_Expr_bindingDomain_x21(v_a_1976_);
lean_dec(v_a_1976_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_1978_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1977_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v_lower_1982_; lean_object* v_upper_1983_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = l_Lean_Expr_app___override(v___x_1972_, v_a_1979_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_array_get_size(v_args_1967_);
v___x_2009_ = lean_nat_dec_le(v___x_1962_, v___x_2007_);
if (v___x_2009_ == 0)
{
v_lower_1982_ = v___x_1962_;
v_upper_1983_ = v___x_2008_;
goto v___jp_1981_;
}
else
{
lean_dec(v___x_1962_);
v_lower_1982_ = v___x_2007_;
v_upper_1983_ = v___x_2008_;
goto v___jp_1981_;
}
v___jp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; size_t v_sz_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1984_ = l_Array_toSubarray___redArg(v_args_1967_, v_lower_1982_, v_upper_1983_);
v___x_1985_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1986_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1984_, v___x_1985_);
v_sz_1987_ = lean_array_size(v___x_1986_);
v___x_1988_ = ((size_t)0ULL);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1935_, v_fixedPrefixSize_1936_, v_F_1937_, v_sz_1987_, v___x_1988_, v___x_1986_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_mkAppN(v___x_1980_, v_a_1990_);
lean_dec(v_a_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___x_1980_);
v_a_1999_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1989_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1989_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1972_);
lean_dec_ref(v_args_1967_);
lean_dec(v___x_1962_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
return v___x_1978_;
}
}
else
{
lean_dec_ref(v___x_1972_);
lean_dec_ref(v_args_1967_);
lean_dec(v___x_1962_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
return v___x_1975_;
}
}
else
{
lean_dec_ref(v___x_1972_);
lean_dec_ref(v_args_1967_);
lean_dec(v___x_1962_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
return v___x_1973_;
}
}
else
{
lean_dec_ref(v_args_1967_);
lean_dec(v___x_1962_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
return v___x_1970_;
}
}
else
{
lean_object* v_cls_2010_; lean_object* v___x_2011_; 
lean_dec(v___x_1962_);
lean_dec(v___x_1960_);
v_cls_2010_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_2011_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2010_, v_a_1945_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = lean_unbox(v_a_2012_);
lean_dec(v_a_2012_);
if (v___x_2013_ == 0)
{
v___y_1949_ = v_a_1939_;
v___y_1950_ = v_a_1940_;
v___y_1951_ = v_a_1941_;
v___y_1952_ = v_a_1942_;
v___y_1953_ = v_a_1943_;
v___y_1954_ = v_a_1944_;
v___y_1955_ = v_a_1945_;
v___y_1956_ = v_a_1946_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3);
lean_inc_ref(v_e_1938_);
v___x_2015_ = l_Lean_indentExpr(v_e_1938_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_2010_, v___x_2016_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref(v___x_2017_);
v___y_1949_ = v_a_1939_;
v___y_1950_ = v_a_1940_;
v___y_1951_ = v_a_1941_;
v___y_1952_ = v_a_1942_;
v___y_1953_ = v_a_1943_;
v___y_1954_ = v_a_1944_;
v___y_1955_ = v_a_1945_;
v___y_1956_ = v_a_1946_;
goto v___jp_1948_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_e_1938_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
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
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_e_1938_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
v_a_2026_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2011_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2011_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
v___jp_1948_:
{
lean_object* v___x_1957_; 
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
v___x_1957_ = l_Lean_Meta_etaExpand(v_e_1938_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1935_, v_fixedPrefixSize_1936_, v_F_1937_, v_a_1958_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1959_;
}
else
{
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v_F_1937_);
lean_dec(v_fixedPrefixSize_1936_);
lean_dec(v_recFnName_1935_);
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(lean_object* v_recFnName_2034_, lean_object* v_fixedPrefixSize_2035_, lean_object* v_F_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 5)
{
lean_object* v_fn_2049_; lean_object* v_arg_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_fn_2049_ = lean_ctor_get(v_x_2037_, 0);
lean_inc_ref(v_fn_2049_);
v_arg_2050_ = lean_ctor_get(v_x_2037_, 1);
lean_inc_ref(v_arg_2050_);
lean_dec_ref(v_x_2037_);
v___x_2051_ = lean_array_set(v_x_2038_, v_x_2039_, v_arg_2050_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_sub(v_x_2039_, v___x_2052_);
lean_dec(v_x_2039_);
v_x_2037_ = v_fn_2049_;
v_x_2038_ = v___x_2051_;
v_x_2039_ = v___x_2053_;
goto _start;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_x_2039_);
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v_F_2036_);
lean_inc(v_fixedPrefixSize_2035_);
lean_inc(v_recFnName_2034_);
v___x_2055_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2034_, v_fixedPrefixSize_2035_, v_F_2036_, v_x_2037_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; size_t v_sz_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v_sz_2057_ = lean_array_size(v_x_2038_);
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2034_, v_fixedPrefixSize_2035_, v_F_2036_, v_sz_2057_, v___x_2058_, v_x_2038_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_mkAppN(v_a_2056_, v_a_2060_);
lean_dec(v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2056_);
v_a_2069_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2059_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2059_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v_x_2038_);
lean_dec_ref(v_F_2036_);
lean_dec(v_fixedPrefixSize_2035_);
lean_dec(v_recFnName_2034_);
return v___x_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2077_, lean_object* v_fixedPrefixSize_2078_, lean_object* v_F_2079_, lean_object* v_e_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_isAppOf(v_e_2080_, v_recFnName_2077_);
if (v___x_2090_ == 0)
{
lean_object* v_dummy_2091_; lean_object* v_nargs_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_dummy_2091_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_2092_ = l_Lean_Expr_getAppNumArgs(v_e_2080_);
lean_inc(v_nargs_2092_);
v___x_2093_ = lean_mk_array(v_nargs_2092_, v_dummy_2091_);
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_sub(v_nargs_2092_, v___x_2094_);
lean_dec(v_nargs_2092_);
v___x_2096_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2077_, v_fixedPrefixSize_2078_, v_F_2079_, v_e_2080_, v___x_2093_, v___x_2095_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2077_, v_fixedPrefixSize_2078_, v_F_2079_, v_e_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2097_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0));
v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
return v___x_2100_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(lean_object* v___x_2104_, lean_object* v_b_2105_, lean_object* v_recFnName_2106_, lean_object* v_fixedPrefixSize_2107_, uint8_t v___x_2108_, lean_object* v___x_2109_, lean_object* v_a_2110_, lean_object* v_e_2111_, lean_object* v_xs_2112_, lean_object* v_altBody_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_array_get_size(v_xs_2112_);
v___x_2131_ = lean_nat_dec_eq(v___x_2130_, v___x_2109_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v_altBody_2113_);
lean_dec(v_fixedPrefixSize_2107_);
lean_dec(v_recFnName_2106_);
lean_dec_ref(v___x_2104_);
v___x_2132_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1);
v___x_2133_ = l_Lean_indentExpr(v_a_2110_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3);
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_indentExpr(v_e_2111_);
v___x_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_2138_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
lean_dec_ref(v_e_2111_);
lean_dec_ref(v_a_2110_);
goto v___jp_2123_;
}
v___jp_2123_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_array_get_borrowed(v___x_2104_, v_xs_2112_, v_b_2105_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___x_2124_);
v___x_2125_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2106_, v_fixedPrefixSize_2107_, v___x_2124_, v_altBody_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; uint8_t v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = 0;
v___x_2128_ = 1;
v___x_2129_ = l_Lean_Meta_mkLambdaFVars(v_xs_2112_, v_a_2126_, v___x_2127_, v___x_2108_, v___x_2127_, v___x_2108_, v___x_2128_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v___x_2129_;
}
else
{
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed(lean_object** _args){
lean_object* v___x_2148_ = _args[0];
lean_object* v_b_2149_ = _args[1];
lean_object* v_recFnName_2150_ = _args[2];
lean_object* v_fixedPrefixSize_2151_ = _args[3];
lean_object* v___x_2152_ = _args[4];
lean_object* v___x_2153_ = _args[5];
lean_object* v_a_2154_ = _args[6];
lean_object* v_e_2155_ = _args[7];
lean_object* v_xs_2156_ = _args[8];
lean_object* v_altBody_2157_ = _args[9];
lean_object* v___y_2158_ = _args[10];
lean_object* v___y_2159_ = _args[11];
lean_object* v___y_2160_ = _args[12];
lean_object* v___y_2161_ = _args[13];
lean_object* v___y_2162_ = _args[14];
lean_object* v___y_2163_ = _args[15];
lean_object* v___y_2164_ = _args[16];
lean_object* v___y_2165_ = _args[17];
lean_object* v___y_2166_ = _args[18];
_start:
{
uint8_t v___x_67857__boxed_2167_; lean_object* v_res_2168_; 
v___x_67857__boxed_2167_ = lean_unbox(v___x_2152_);
v_res_2168_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(v___x_2148_, v_b_2149_, v_recFnName_2150_, v_fixedPrefixSize_2151_, v___x_67857__boxed_2167_, v___x_2153_, v_a_2154_, v_e_2155_, v_xs_2156_, v_altBody_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec_ref(v_xs_2156_);
lean_dec(v___x_2153_);
lean_dec(v_b_2149_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(lean_object* v_recFnName_2169_, lean_object* v_fixedPrefixSize_2170_, lean_object* v_e_2171_, lean_object* v_as_2172_, lean_object* v_bs_2173_, lean_object* v_i_2174_, lean_object* v_cs_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_array_get_size(v_as_2172_);
v___x_2186_ = lean_nat_dec_lt(v_i_2174_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec(v_i_2174_);
lean_dec_ref(v_e_2171_);
lean_dec(v_fixedPrefixSize_2170_);
lean_dec(v_recFnName_2169_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_cs_2175_);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_array_get_size(v_bs_2173_);
v___x_2189_ = lean_nat_dec_lt(v_i_2174_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec(v_i_2174_);
lean_dec_ref(v_e_2171_);
lean_dec(v_fixedPrefixSize_2170_);
lean_dec(v_recFnName_2169_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_cs_2175_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v_a_2192_; lean_object* v_b_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___f_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
v___x_2191_ = l_Lean_instInhabitedExpr;
v_a_2192_ = lean_array_fget_borrowed(v_as_2172_, v_i_2174_);
v_b_2193_ = lean_array_fget_borrowed(v_bs_2173_, v_i_2174_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_b_2193_, v___x_2194_);
v___x_2196_ = lean_box(v___x_2189_);
lean_inc_ref(v_e_2171_);
lean_inc(v_a_2192_);
lean_inc(v___x_2195_);
lean_inc(v_fixedPrefixSize_2170_);
lean_inc(v_recFnName_2169_);
lean_inc(v_b_2193_);
v___f_2197_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2197_, 0, v___x_2191_);
lean_closure_set(v___f_2197_, 1, v_b_2193_);
lean_closure_set(v___f_2197_, 2, v_recFnName_2169_);
lean_closure_set(v___f_2197_, 3, v_fixedPrefixSize_2170_);
lean_closure_set(v___f_2197_, 4, v___x_2196_);
lean_closure_set(v___f_2197_, 5, v___x_2195_);
lean_closure_set(v___f_2197_, 6, v_a_2192_);
lean_closure_set(v___f_2197_, 7, v_e_2171_);
v___x_2198_ = 0;
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc(v___y_2176_);
lean_inc(v_a_2192_);
v___x_2199_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_a_2192_, v___x_2195_, v___f_2197_, v___x_2198_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = lean_nat_add(v_i_2174_, v___x_2194_);
lean_dec(v_i_2174_);
v___x_2202_ = lean_array_push(v_cs_2175_, v_a_2200_);
v_i_2174_ = v___x_2201_;
v_cs_2175_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v_cs_2175_);
lean_dec(v_i_2174_);
lean_dec_ref(v_e_2171_);
lean_dec(v_fixedPrefixSize_2170_);
lean_dec(v_recFnName_2169_);
v_a_2204_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2199_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2199_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2212_, lean_object* v_fixedPrefixSize_2213_, lean_object* v_F_2214_, lean_object* v_e_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
switch(lean_obj_tag(v_e_2215_))
{
case 6:
{
lean_object* v_binderName_2225_; lean_object* v_binderType_2226_; lean_object* v_body_2227_; uint8_t v_binderInfo_2228_; lean_object* v___x_2229_; 
v_binderName_2225_ = lean_ctor_get(v_e_2215_, 0);
lean_inc(v_binderName_2225_);
v_binderType_2226_ = lean_ctor_get(v_e_2215_, 1);
lean_inc_ref(v_binderType_2226_);
v_body_2227_ = lean_ctor_get(v_e_2215_, 2);
lean_inc_ref(v_body_2227_);
v_binderInfo_2228_ = lean_ctor_get_uint8(v_e_2215_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2215_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_F_2214_);
lean_inc(v_fixedPrefixSize_2213_);
lean_inc(v_recFnName_2212_);
v___x_2229_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_binderType_2226_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___f_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2231_, 0, v_body_2227_);
lean_closure_set(v___f_2231_, 1, v_recFnName_2212_);
lean_closure_set(v___f_2231_, 2, v_fixedPrefixSize_2213_);
lean_closure_set(v___f_2231_, 3, v_F_2214_);
v___x_2232_ = 0;
v___x_2233_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2225_, v_binderInfo_2228_, v_a_2230_, v___f_2231_, v___x_2232_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2233_;
}
else
{
lean_dec_ref(v_body_2227_);
lean_dec(v_binderName_2225_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
return v___x_2229_;
}
}
case 7:
{
lean_object* v_binderName_2234_; lean_object* v_binderType_2235_; lean_object* v_body_2236_; uint8_t v_binderInfo_2237_; lean_object* v___x_2238_; 
v_binderName_2234_ = lean_ctor_get(v_e_2215_, 0);
lean_inc(v_binderName_2234_);
v_binderType_2235_ = lean_ctor_get(v_e_2215_, 1);
lean_inc_ref(v_binderType_2235_);
v_body_2236_ = lean_ctor_get(v_e_2215_, 2);
lean_inc_ref(v_body_2236_);
v_binderInfo_2237_ = lean_ctor_get_uint8(v_e_2215_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2215_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_F_2214_);
lean_inc(v_fixedPrefixSize_2213_);
lean_inc(v_recFnName_2212_);
v___x_2238_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_binderType_2235_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___f_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___f_2240_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2240_, 0, v_body_2236_);
lean_closure_set(v___f_2240_, 1, v_recFnName_2212_);
lean_closure_set(v___f_2240_, 2, v_fixedPrefixSize_2213_);
lean_closure_set(v___f_2240_, 3, v_F_2214_);
v___x_2241_ = 0;
v___x_2242_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2234_, v_binderInfo_2237_, v_a_2239_, v___f_2240_, v___x_2241_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2242_;
}
else
{
lean_dec_ref(v_body_2236_);
lean_dec(v_binderName_2234_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
return v___x_2238_;
}
}
case 8:
{
lean_object* v_declName_2243_; lean_object* v_type_2244_; lean_object* v_value_2245_; lean_object* v_body_2246_; uint8_t v_nondep_2247_; lean_object* v___x_2248_; 
v_declName_2243_ = lean_ctor_get(v_e_2215_, 0);
lean_inc(v_declName_2243_);
v_type_2244_ = lean_ctor_get(v_e_2215_, 1);
lean_inc_ref(v_type_2244_);
v_value_2245_ = lean_ctor_get(v_e_2215_, 2);
lean_inc_ref(v_value_2245_);
v_body_2246_ = lean_ctor_get(v_e_2215_, 3);
lean_inc_ref(v_body_2246_);
v_nondep_2247_ = lean_ctor_get_uint8(v_e_2215_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2215_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_F_2214_);
lean_inc(v_fixedPrefixSize_2213_);
lean_inc(v_recFnName_2212_);
v___x_2248_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_type_2244_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2248_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_F_2214_);
lean_inc(v_fixedPrefixSize_2213_);
lean_inc(v_recFnName_2212_);
v___x_2250_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_value_2245_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___f_2252_; uint8_t v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref(v___x_2250_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2252_, 0, v_body_2246_);
lean_closure_set(v___f_2252_, 1, v_recFnName_2212_);
lean_closure_set(v___f_2252_, 2, v_fixedPrefixSize_2213_);
lean_closure_set(v___f_2252_, 3, v_F_2214_);
v___x_2253_ = 0;
v___x_2254_ = 0;
v___x_2255_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_declName_2243_, v_a_2249_, v_a_2251_, v___f_2252_, v_nondep_2247_, v___x_2253_, v___x_2254_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2255_;
}
else
{
lean_dec(v_a_2249_);
lean_dec_ref(v_body_2246_);
lean_dec(v_declName_2243_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
return v___x_2250_;
}
}
else
{
lean_dec_ref(v_body_2246_);
lean_dec_ref(v_value_2245_);
lean_dec(v_declName_2243_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
return v___x_2248_;
}
}
case 10:
{
lean_object* v_data_2256_; lean_object* v_expr_2257_; lean_object* v___x_2258_; 
v_data_2256_ = lean_ctor_get(v_e_2215_, 0);
lean_inc(v_data_2256_);
v_expr_2257_ = lean_ctor_get(v_e_2215_, 1);
lean_inc_ref(v_expr_2257_);
v___x_2258_ = l_Lean_getRecAppSyntax_x3f(v_e_2215_);
lean_dec_ref(v_e_2215_);
if (lean_obj_tag(v___x_2258_) == 1)
{
lean_object* v_val_2259_; lean_object* v_fileName_2260_; lean_object* v_fileMap_2261_; lean_object* v_options_2262_; lean_object* v_currRecDepth_2263_; lean_object* v_maxRecDepth_2264_; lean_object* v_ref_2265_; lean_object* v_currNamespace_2266_; lean_object* v_openDecls_2267_; lean_object* v_initHeartbeats_2268_; lean_object* v_maxHeartbeats_2269_; lean_object* v_quotContext_2270_; lean_object* v_currMacroScope_2271_; uint8_t v_diag_2272_; lean_object* v_cancelTk_x3f_2273_; uint8_t v_suppressElabErrors_2274_; lean_object* v_inheritedTraceOptions_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_data_2256_);
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref(v___x_2258_);
v_fileName_2260_ = lean_ctor_get(v_a_2222_, 0);
v_fileMap_2261_ = lean_ctor_get(v_a_2222_, 1);
v_options_2262_ = lean_ctor_get(v_a_2222_, 2);
v_currRecDepth_2263_ = lean_ctor_get(v_a_2222_, 3);
v_maxRecDepth_2264_ = lean_ctor_get(v_a_2222_, 4);
v_ref_2265_ = lean_ctor_get(v_a_2222_, 5);
v_currNamespace_2266_ = lean_ctor_get(v_a_2222_, 6);
v_openDecls_2267_ = lean_ctor_get(v_a_2222_, 7);
v_initHeartbeats_2268_ = lean_ctor_get(v_a_2222_, 8);
v_maxHeartbeats_2269_ = lean_ctor_get(v_a_2222_, 9);
v_quotContext_2270_ = lean_ctor_get(v_a_2222_, 10);
v_currMacroScope_2271_ = lean_ctor_get(v_a_2222_, 11);
v_diag_2272_ = lean_ctor_get_uint8(v_a_2222_, sizeof(void*)*14);
v_cancelTk_x3f_2273_ = lean_ctor_get(v_a_2222_, 12);
v_suppressElabErrors_2274_ = lean_ctor_get_uint8(v_a_2222_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2275_ = lean_ctor_get(v_a_2222_, 13);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2277_ = v_a_2222_;
v_isShared_2278_ = v_isSharedCheck_2284_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_inheritedTraceOptions_2275_);
lean_inc(v_cancelTk_x3f_2273_);
lean_inc(v_currMacroScope_2271_);
lean_inc(v_quotContext_2270_);
lean_inc(v_maxHeartbeats_2269_);
lean_inc(v_initHeartbeats_2268_);
lean_inc(v_openDecls_2267_);
lean_inc(v_currNamespace_2266_);
lean_inc(v_ref_2265_);
lean_inc(v_maxRecDepth_2264_);
lean_inc(v_currRecDepth_2263_);
lean_inc(v_options_2262_);
lean_inc(v_fileMap_2261_);
lean_inc(v_fileName_2260_);
lean_dec(v_a_2222_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2284_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_ref_2279_; lean_object* v___x_2281_; 
v_ref_2279_ = l_Lean_replaceRef(v_val_2259_, v_ref_2265_);
lean_dec(v_ref_2265_);
lean_dec(v_val_2259_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 5, v_ref_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_fileName_2260_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_fileMap_2261_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_options_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_currRecDepth_2263_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_maxRecDepth_2264_);
lean_ctor_set(v_reuseFailAlloc_2283_, 5, v_ref_2279_);
lean_ctor_set(v_reuseFailAlloc_2283_, 6, v_currNamespace_2266_);
lean_ctor_set(v_reuseFailAlloc_2283_, 7, v_openDecls_2267_);
lean_ctor_set(v_reuseFailAlloc_2283_, 8, v_initHeartbeats_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 9, v_maxHeartbeats_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 10, v_quotContext_2270_);
lean_ctor_set(v_reuseFailAlloc_2283_, 11, v_currMacroScope_2271_);
lean_ctor_set(v_reuseFailAlloc_2283_, 12, v_cancelTk_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2283_, 13, v_inheritedTraceOptions_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*14, v_diag_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*14 + 1, v_suppressElabErrors_2274_);
v___x_2281_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_expr_2257_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v___x_2281_, v_a_2223_);
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2285_; 
lean_dec(v___x_2258_);
v___x_2285_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_expr_2257_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = l_Lean_mkMData(v_data_2256_, v_a_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2290_);
v___x_2292_ = v___x_2288_;
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
lean_dec(v_data_2256_);
return v___x_2285_;
}
}
}
case 11:
{
lean_object* v_typeName_2295_; lean_object* v_idx_2296_; lean_object* v_struct_2297_; lean_object* v___x_2298_; 
v_typeName_2295_ = lean_ctor_get(v_e_2215_, 0);
lean_inc(v_typeName_2295_);
v_idx_2296_ = lean_ctor_get(v_e_2215_, 1);
lean_inc(v_idx_2296_);
v_struct_2297_ = lean_ctor_get(v_e_2215_, 2);
lean_inc_ref(v_struct_2297_);
lean_dec_ref(v_e_2215_);
v___x_2298_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_struct_2297_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2307_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2307_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2307_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = l_Lean_mkProj(v_typeName_2295_, v_idx_2296_, v_a_2299_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
else
{
lean_dec(v_idx_2296_);
lean_dec(v_typeName_2295_);
return v___x_2298_;
}
}
case 4:
{
uint8_t v___x_2308_; 
v___x_2308_ = l_Lean_Expr_isConstOf(v_e_2215_, v_recFnName_2212_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_e_2215_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_e_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2310_;
}
}
case 5:
{
uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = 1;
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_e_2215_);
v___x_2312_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_2215_, v___x_2311_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
if (lean_obj_tag(v_a_2313_) == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_e_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2314_;
}
else
{
lean_object* v_val_2315_; lean_object* v___x_2316_; 
v_val_2315_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_val_2315_);
lean_dec_ref(v_a_2313_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc_ref(v_F_2214_);
v___x_2316_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2315_, v_F_2214_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
if (lean_obj_tag(v_a_2317_) == 1)
{
lean_object* v_val_2318_; lean_object* v_toMatcherInfo_2319_; lean_object* v_matcherName_2320_; lean_object* v_matcherLevels_2321_; lean_object* v_params_2322_; lean_object* v_motive_2323_; lean_object* v_discrs_2324_; lean_object* v_alts_2325_; lean_object* v_remaining_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_val_2318_ = lean_ctor_get(v_a_2317_, 0);
lean_inc(v_val_2318_);
lean_dec_ref(v_a_2317_);
v_toMatcherInfo_2319_ = lean_ctor_get(v_val_2318_, 0);
lean_inc_ref(v_toMatcherInfo_2319_);
v_matcherName_2320_ = lean_ctor_get(v_val_2318_, 1);
lean_inc(v_matcherName_2320_);
v_matcherLevels_2321_ = lean_ctor_get(v_val_2318_, 2);
lean_inc_ref(v_matcherLevels_2321_);
v_params_2322_ = lean_ctor_get(v_val_2318_, 3);
lean_inc_ref(v_params_2322_);
v_motive_2323_ = lean_ctor_get(v_val_2318_, 4);
lean_inc_ref(v_motive_2323_);
v_discrs_2324_ = lean_ctor_get(v_val_2318_, 5);
lean_inc_ref(v_discrs_2324_);
v_alts_2325_ = lean_ctor_get(v_val_2318_, 6);
lean_inc_ref(v_alts_2325_);
v_remaining_2326_ = lean_ctor_get(v_val_2318_, 7);
lean_inc_ref(v_remaining_2326_);
v___x_2327_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2318_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc(v_fixedPrefixSize_2213_);
lean_inc(v_recFnName_2212_);
v___x_2330_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_e_2215_, v_alts_2325_, v___x_2327_, v___x_2328_, v___x_2329_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_alts_2325_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; size_t v_sz_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v_sz_2332_ = lean_array_size(v_discrs_2324_);
v___x_2333_ = ((size_t)0ULL);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_sz_2332_, v___x_2333_, v_discrs_2324_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2344_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2339_, 0, v_toMatcherInfo_2319_);
lean_ctor_set(v___x_2339_, 1, v_matcherName_2320_);
lean_ctor_set(v___x_2339_, 2, v_matcherLevels_2321_);
lean_ctor_set(v___x_2339_, 3, v_params_2322_);
lean_ctor_set(v___x_2339_, 4, v_motive_2323_);
lean_ctor_set(v___x_2339_, 5, v_a_2335_);
lean_ctor_set(v___x_2339_, 6, v_a_2331_);
lean_ctor_set(v___x_2339_, 7, v_remaining_2326_);
v___x_2340_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2339_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2340_);
v___x_2342_ = v___x_2337_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2331_);
lean_dec_ref(v_remaining_2326_);
lean_dec_ref(v_motive_2323_);
lean_dec_ref(v_params_2322_);
lean_dec_ref(v_matcherLevels_2321_);
lean_dec(v_matcherName_2320_);
lean_dec_ref(v_toMatcherInfo_2319_);
v_a_2345_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2334_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2334_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_remaining_2326_);
lean_dec_ref(v_discrs_2324_);
lean_dec_ref(v_motive_2323_);
lean_dec_ref(v_params_2322_);
lean_dec_ref(v_matcherLevels_2321_);
lean_dec(v_matcherName_2320_);
lean_dec_ref(v_toMatcherInfo_2319_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
v_a_2353_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2330_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2330_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v___x_2361_; 
lean_dec(v_a_2317_);
v___x_2361_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2212_, v_fixedPrefixSize_2213_, v_F_2214_, v_e_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2361_;
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_e_2215_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
v_a_2362_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2316_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2316_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_e_2215_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
lean_dec(v_recFnName_2212_);
v_a_2370_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2312_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2312_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
default: 
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_F_2214_);
lean_dec(v_fixedPrefixSize_2213_);
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_mk_empty_array_with_capacity(v___x_2378_);
v___x_2380_ = lean_array_push(v___x_2379_, v_recFnName_2212_);
lean_inc_ref(v_e_2215_);
v___x_2381_ = l_Lean_Elab_ensureNoRecFn(v___x_2380_, v_e_2215_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v___x_2381_, 0);
lean_dec(v_unused_2389_);
v___x_2383_ = v___x_2381_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v___x_2381_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v_e_2215_);
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_e_2215_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_e_2215_);
v_a_2390_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2381_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2381_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
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
uint8_t v___x_2398_; uint64_t v___x_2399_; 
v___x_2398_ = 0;
v___x_2399_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2400_, lean_object* v_fixedPrefixSize_2401_, lean_object* v_F_2402_, lean_object* v_e_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; 
lean_inc_ref(v_e_2403_);
lean_inc(v_recFnName_2400_);
v___x_2413_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2400_, v_e_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2565_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2565_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2565_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_unbox(v_a_2414_);
lean_dec(v_a_2414_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2420_; 
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_F_2402_);
lean_dec(v_fixedPrefixSize_2401_);
lean_dec(v_recFnName_2400_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_e_2403_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_e_2403_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___x_2543_; 
lean_del_object(v___x_2416_);
v___x_2422_ = lean_st_ref_get(v_a_2405_);
v___x_2423_ = 0;
v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v___x_2422_, v_e_2403_);
lean_dec(v___x_2422_);
if (lean_obj_tag(v___x_2543_) == 1)
{
lean_object* v_val_2544_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___x_2547_; 
v_val_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref(v___x_2543_);
v_fst_2545_ = lean_ctor_get(v_val_2544_, 0);
lean_inc(v_fst_2545_);
v_snd_2546_ = lean_ctor_get(v_val_2544_, 1);
lean_inc(v_snd_2546_);
lean_dec(v_val_2544_);
lean_inc_ref(v_a_2408_);
v___x_2547_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2546_, v_a_2408_);
lean_dec(v_snd_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2556_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_unbox(v_a_2548_);
lean_dec(v_a_2548_);
if (v___x_2552_ == 0)
{
lean_del_object(v___x_2550_);
lean_dec(v_fst_2545_);
v___y_2425_ = v_a_2404_;
v___y_2426_ = v_a_2405_;
v___y_2427_ = v_a_2406_;
v___y_2428_ = v_a_2407_;
v___y_2429_ = v_a_2408_;
v___y_2430_ = v_a_2409_;
v___y_2431_ = v_a_2410_;
v___y_2432_ = v_a_2411_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2554_; 
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_e_2403_);
lean_dec_ref(v_F_2402_);
lean_dec(v_fixedPrefixSize_2401_);
lean_dec(v_recFnName_2400_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v_fst_2545_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_fst_2545_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_fst_2545_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_e_2403_);
lean_dec_ref(v_F_2402_);
lean_dec(v_fixedPrefixSize_2401_);
lean_dec(v_recFnName_2400_);
v_a_2557_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2547_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2547_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_dec(v___x_2543_);
v___y_2425_ = v_a_2404_;
v___y_2426_ = v_a_2405_;
v___y_2427_ = v_a_2406_;
v___y_2428_ = v_a_2407_;
v___y_2429_ = v_a_2408_;
v___y_2430_ = v_a_2409_;
v___y_2431_ = v_a_2410_;
v___y_2432_ = v_a_2411_;
goto v___jp_2424_;
}
v___jp_2424_:
{
lean_object* v___x_2433_; 
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
lean_inc(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v_e_2403_);
v___x_2433_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2400_, v_fixedPrefixSize_2401_, v_F_2402_, v_e_2403_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v___x_2433_);
lean_inc_ref(v___y_2429_);
v___x_2435_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2534_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2534_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2534_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_options_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2440_ = lean_st_ref_take(v___y_2426_);
lean_inc(v_a_2434_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2434_);
lean_ctor_set(v___x_2441_, 1, v_a_2436_);
lean_inc_ref(v_e_2403_);
v___x_2442_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v___x_2440_, v_e_2403_, v___x_2441_);
v___x_2443_ = lean_st_ref_set(v___y_2426_, v___x_2442_);
v_options_2444_ = lean_ctor_get(v___y_2431_, 2);
v___x_2445_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2446_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_options_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2448_; 
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v_e_2403_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2434_);
v___x_2448_ = v___x_2438_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2434_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
lean_object* v___x_2450_; uint8_t v_foApprox_2451_; uint8_t v_ctxApprox_2452_; uint8_t v_quasiPatternApprox_2453_; uint8_t v_constApprox_2454_; uint8_t v_isDefEqStuckEx_2455_; uint8_t v_unificationHints_2456_; uint8_t v_proofIrrelevance_2457_; uint8_t v_assignSyntheticOpaque_2458_; uint8_t v_offsetCnstrs_2459_; uint8_t v_etaStruct_2460_; uint8_t v_univApprox_2461_; uint8_t v_iota_2462_; uint8_t v_beta_2463_; uint8_t v_proj_2464_; uint8_t v_zeta_2465_; uint8_t v_zetaDelta_2466_; uint8_t v_zetaUnused_2467_; uint8_t v_zetaHave_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2533_; 
lean_del_object(v___x_2438_);
v___x_2450_ = l_Lean_Meta_Context_config(v___y_2429_);
v_foApprox_2451_ = lean_ctor_get_uint8(v___x_2450_, 0);
v_ctxApprox_2452_ = lean_ctor_get_uint8(v___x_2450_, 1);
v_quasiPatternApprox_2453_ = lean_ctor_get_uint8(v___x_2450_, 2);
v_constApprox_2454_ = lean_ctor_get_uint8(v___x_2450_, 3);
v_isDefEqStuckEx_2455_ = lean_ctor_get_uint8(v___x_2450_, 4);
v_unificationHints_2456_ = lean_ctor_get_uint8(v___x_2450_, 5);
v_proofIrrelevance_2457_ = lean_ctor_get_uint8(v___x_2450_, 6);
v_assignSyntheticOpaque_2458_ = lean_ctor_get_uint8(v___x_2450_, 7);
v_offsetCnstrs_2459_ = lean_ctor_get_uint8(v___x_2450_, 8);
v_etaStruct_2460_ = lean_ctor_get_uint8(v___x_2450_, 10);
v_univApprox_2461_ = lean_ctor_get_uint8(v___x_2450_, 11);
v_iota_2462_ = lean_ctor_get_uint8(v___x_2450_, 12);
v_beta_2463_ = lean_ctor_get_uint8(v___x_2450_, 13);
v_proj_2464_ = lean_ctor_get_uint8(v___x_2450_, 14);
v_zeta_2465_ = lean_ctor_get_uint8(v___x_2450_, 15);
v_zetaDelta_2466_ = lean_ctor_get_uint8(v___x_2450_, 16);
v_zetaUnused_2467_ = lean_ctor_get_uint8(v___x_2450_, 17);
v_zetaHave_2468_ = lean_ctor_get_uint8(v___x_2450_, 18);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2470_ = v___x_2450_;
v_isShared_2471_ = v_isSharedCheck_2533_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v___x_2450_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2533_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v_trackZetaDelta_2472_; lean_object* v_zetaDeltaSet_2473_; lean_object* v_lctx_2474_; lean_object* v_localInstances_2475_; lean_object* v_defEqCtx_x3f_2476_; lean_object* v_synthPendingDepth_2477_; lean_object* v_canUnfold_x3f_2478_; uint8_t v_univApprox_2479_; uint8_t v_inTypeClassResolution_2480_; uint8_t v_cacheInferType_2481_; uint8_t v___x_2482_; lean_object* v_config_2484_; 
v_trackZetaDelta_2472_ = lean_ctor_get_uint8(v___y_2429_, sizeof(void*)*7);
v_zetaDeltaSet_2473_ = lean_ctor_get(v___y_2429_, 1);
lean_inc(v_zetaDeltaSet_2473_);
v_lctx_2474_ = lean_ctor_get(v___y_2429_, 2);
lean_inc_ref(v_lctx_2474_);
v_localInstances_2475_ = lean_ctor_get(v___y_2429_, 3);
lean_inc_ref(v_localInstances_2475_);
v_defEqCtx_x3f_2476_ = lean_ctor_get(v___y_2429_, 4);
lean_inc(v_defEqCtx_x3f_2476_);
v_synthPendingDepth_2477_ = lean_ctor_get(v___y_2429_, 5);
lean_inc(v_synthPendingDepth_2477_);
v_canUnfold_x3f_2478_ = lean_ctor_get(v___y_2429_, 6);
lean_inc(v_canUnfold_x3f_2478_);
v_univApprox_2479_ = lean_ctor_get_uint8(v___y_2429_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2480_ = lean_ctor_get_uint8(v___y_2429_, sizeof(void*)*7 + 2);
v_cacheInferType_2481_ = lean_ctor_get_uint8(v___y_2429_, sizeof(void*)*7 + 3);
v___x_2482_ = 0;
if (v_isShared_2471_ == 0)
{
v_config_2484_ = v___x_2470_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 0, v_foApprox_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 1, v_ctxApprox_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 2, v_quasiPatternApprox_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 3, v_constApprox_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 4, v_isDefEqStuckEx_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 5, v_unificationHints_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 6, v_proofIrrelevance_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 7, v_assignSyntheticOpaque_2458_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 8, v_offsetCnstrs_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 10, v_etaStruct_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 11, v_univApprox_2461_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 12, v_iota_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 13, v_beta_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 14, v_proj_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 15, v_zeta_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 16, v_zetaDelta_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 17, v_zetaUnused_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, 18, v_zetaHave_2468_);
v_config_2484_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
uint64_t v___x_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2524_; 
lean_ctor_set_uint8(v_config_2484_, 9, v___x_2482_);
v___x_2485_ = l_Lean_Meta_Context_configKey(v___y_2429_);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___y_2429_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; lean_object* v_unused_2531_; 
v_unused_2525_ = lean_ctor_get(v___y_2429_, 6);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v___y_2429_, 5);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v___y_2429_, 4);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v___y_2429_, 3);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v___y_2429_, 2);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v___y_2429_, 1);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v___y_2429_, 0);
lean_dec(v_unused_2531_);
v___x_2487_ = v___y_2429_;
v_isShared_2488_ = v_isSharedCheck_2524_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v___y_2429_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2524_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
uint64_t v___x_2489_; uint64_t v___x_2490_; lean_object* v___f_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v_key_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2489_ = 2ULL;
v___x_2490_ = lean_uint64_shift_right(v___x_2485_, v___x_2489_);
lean_inc(v_a_2434_);
v___f_2491_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2491_, 0, v_a_2434_);
lean_closure_set(v___f_2491_, 1, v_e_2403_);
v___x_2492_ = lean_uint64_shift_left(v___x_2490_, v___x_2489_);
v___x_2493_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2494_ = lean_uint64_lor(v___x_2492_, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2495_, 0, v_config_2484_);
lean_ctor_set_uint64(v___x_2495_, sizeof(void*)*1, v_key_2494_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_zetaDeltaSet_2473_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_lctx_2474_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_localInstances_2475_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_defEqCtx_x3f_2476_);
lean_ctor_set(v_reuseFailAlloc_2523_, 5, v_synthPendingDepth_2477_);
lean_ctor_set(v_reuseFailAlloc_2523_, 6, v_canUnfold_x3f_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*7, v_trackZetaDelta_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*7 + 1, v_univApprox_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*7 + 3, v_cacheInferType_2481_);
v___x_2497_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___f_2491_, v___x_2423_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___x_2497_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2506_);
v___x_2500_ = v___x_2498_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v___x_2498_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v_a_2434_);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2434_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2514_);
v___x_2508_ = v___x_2498_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v___x_2498_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2434_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2434_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_a_2434_);
v_a_2515_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2498_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2498_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
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
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2434_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v_e_2403_);
v_a_2535_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2435_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2435_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v_e_2403_);
return v___x_2433_;
}
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_e_2403_);
lean_dec_ref(v_F_2402_);
lean_dec(v_fixedPrefixSize_2401_);
lean_dec(v_recFnName_2400_);
v_a_2566_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2413_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2413_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2574_, lean_object* v_recFnName_2575_, lean_object* v_fixedPrefixSize_2576_, lean_object* v_F_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_expr_instantiate1(v_body_2574_, v_x_2578_);
v___x_2589_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2575_, v_fixedPrefixSize_2576_, v_F_2577_, v___x_2588_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2590_, lean_object* v_fixedPrefixSize_2591_, lean_object* v_F_2592_, lean_object* v_e_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2590_, v_fixedPrefixSize_2591_, v_F_2592_, v_e_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2604_, lean_object* v_fixedPrefixSize_2605_, lean_object* v_F_2606_, lean_object* v_sz_2607_, lean_object* v_i_2608_, lean_object* v_bs_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
size_t v_sz_boxed_2619_; size_t v_i_boxed_2620_; lean_object* v_res_2621_; 
v_sz_boxed_2619_ = lean_unbox_usize(v_sz_2607_);
lean_dec(v_sz_2607_);
v_i_boxed_2620_ = lean_unbox_usize(v_i_2608_);
lean_dec(v_i_2608_);
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2604_, v_fixedPrefixSize_2605_, v_F_2606_, v_sz_boxed_2619_, v_i_boxed_2620_, v_bs_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17___boxed(lean_object* v_recFnName_2622_, lean_object* v_fixedPrefixSize_2623_, lean_object* v_F_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2622_, v_fixedPrefixSize_2623_, v_F_2624_, v_x_2625_, v_x_2626_, v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___boxed(lean_object* v_recFnName_2638_, lean_object* v_fixedPrefixSize_2639_, lean_object* v_e_2640_, lean_object* v_as_2641_, lean_object* v_bs_2642_, lean_object* v_i_2643_, lean_object* v_cs_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2638_, v_fixedPrefixSize_2639_, v_e_2640_, v_as_2641_, v_bs_2642_, v_i_2643_, v_cs_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec_ref(v_bs_2642_);
lean_dec_ref(v_as_2641_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2655_, lean_object* v_fixedPrefixSize_2656_, lean_object* v_F_2657_, lean_object* v_e_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2655_, v_fixedPrefixSize_2656_, v_F_2657_, v_e_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2669_, lean_object* v_fixedPrefixSize_2670_, lean_object* v_F_2671_, lean_object* v_e_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2669_, v_fixedPrefixSize_2670_, v_F_2671_, v_e_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2683_, lean_object* v_fixedPrefixSize_2684_, lean_object* v_F_2685_, lean_object* v_e_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2683_, v_fixedPrefixSize_2684_, v_F_2685_, v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b1_2697_, lean_object* v_k_2698_, uint8_t v_allowLevelAssignments_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_k_2698_, v_allowLevelAssignments_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_k_2711_, lean_object* v_allowLevelAssignments_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2722_; lean_object* v_res_2723_; 
v_allowLevelAssignments_boxed_2722_ = lean_unbox(v_allowLevelAssignments_2712_);
v_res_2723_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b1_2710_, v_k_2711_, v_allowLevelAssignments_boxed_2722_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_00_u03b1_2724_, lean_object* v_name_2725_, uint8_t v_bi_2726_, lean_object* v_type_2727_, lean_object* v_k_2728_, uint8_t v_kind_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_name_2725_, v_bi_2726_, v_type_2727_, v_k_2728_, v_kind_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_name_2741_, lean_object* v_bi_2742_, lean_object* v_type_2743_, lean_object* v_k_2744_, lean_object* v_kind_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
uint8_t v_bi_boxed_2755_; uint8_t v_kind_boxed_2756_; lean_object* v_res_2757_; 
v_bi_boxed_2755_ = lean_unbox(v_bi_2742_);
v_kind_boxed_2756_ = lean_unbox(v_kind_2745_);
v_res_2757_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_00_u03b1_2740_, v_name_2741_, v_bi_boxed_2755_, v_type_2743_, v_k_2744_, v_kind_boxed_2756_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_00_u03b1_2758_, lean_object* v_e_2759_, lean_object* v_maxFVars_2760_, lean_object* v_k_2761_, uint8_t v_cleanupAnnotations_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_2759_, v_maxFVars_2760_, v_k_2761_, v_cleanupAnnotations_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_e_2774_, lean_object* v_maxFVars_2775_, lean_object* v_k_2776_, lean_object* v_cleanupAnnotations_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2787_; lean_object* v_res_2788_; 
v_cleanupAnnotations_boxed_2787_ = lean_unbox(v_cleanupAnnotations_2777_);
v_res_2788_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_00_u03b1_2773_, v_e_2774_, v_maxFVars_2775_, v_k_2776_, v_cleanupAnnotations_boxed_2787_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2789_, lean_object* v_R_2790_, lean_object* v_a_2791_, lean_object* v_b_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2791_, v_b_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3(lean_object* v_cls_2794_, lean_object* v_msg_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_2794_, v_msg_2795_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___boxed(lean_object* v_cls_2806_, lean_object* v_msg_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3(v_cls_2806_, v_msg_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_00_u03b2_2818_, lean_object* v_m_2819_, lean_object* v_a_2820_, lean_object* v_b_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v_m_2819_, v_a_2820_, v_b_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2823_, lean_object* v_msg_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_msg_2824_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2835_, lean_object* v_msg_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2835_, v_msg_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(lean_object* v_00_u03b2_2847_, lean_object* v_m_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_2848_, v_a_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b2_2851_, lean_object* v_m_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(v_00_u03b2_2851_, v_m_2852_, v_a_2853_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_m_2852_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16(lean_object* v_00_u03b1_2855_, lean_object* v_name_2856_, lean_object* v_type_2857_, lean_object* v_val_2858_, lean_object* v_k_2859_, uint8_t v_nondep_2860_, uint8_t v_kind_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_2856_, v_type_2857_, v_val_2858_, v_k_2859_, v_nondep_2860_, v_kind_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_name_2873_, lean_object* v_type_2874_, lean_object* v_val_2875_, lean_object* v_k_2876_, lean_object* v_nondep_2877_, lean_object* v_kind_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v_nondep_boxed_2888_; uint8_t v_kind_boxed_2889_; lean_object* v_res_2890_; 
v_nondep_boxed_2888_ = lean_unbox(v_nondep_2877_);
v_kind_boxed_2889_ = lean_unbox(v_kind_2878_);
v_res_2890_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16(v_00_u03b1_2872_, v_name_2873_, v_type_2874_, v_val_2875_, v_k_2876_, v_nondep_boxed_2888_, v_kind_boxed_2889_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(lean_object* v_declName_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_2891_, v___y_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___boxed(lean_object* v_declName_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(v_declName_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec(v___y_2903_);
return v_res_2912_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5(lean_object* v_00_u03b2_2913_, lean_object* v_a_2914_, lean_object* v_x_2915_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_2914_, v_x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___boxed(lean_object* v_00_u03b2_2917_, lean_object* v_a_2918_, lean_object* v_x_2919_){
_start:
{
uint8_t v_res_2920_; lean_object* v_r_2921_; 
v_res_2920_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5(v_00_u03b2_2917_, v_a_2918_, v_x_2919_);
lean_dec(v_x_2919_);
lean_dec_ref(v_a_2918_);
v_r_2921_ = lean_box(v_res_2920_);
return v_r_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6(lean_object* v_00_u03b2_2922_, lean_object* v_data_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(v_data_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7(lean_object* v_00_u03b2_2925_, lean_object* v_a_2926_, lean_object* v_b_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_2926_, v_b_2927_, v_x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12(lean_object* v_00_u03b2_2930_, lean_object* v_a_2931_, lean_object* v_x_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_2931_, v_x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2934_, lean_object* v_a_2935_, lean_object* v_x_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12(v_00_u03b2_2934_, v_a_2935_, v_x_2936_);
lean_dec(v_x_2936_);
lean_dec_ref(v_a_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13(lean_object* v_00_u03b2_2938_, lean_object* v_i_2939_, lean_object* v_source_2940_, lean_object* v_target_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(v_i_2939_, v_source_2940_, v_target_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22(lean_object* v_00_u03b1_2943_, lean_object* v_constName_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___boxed(lean_object* v_00_u03b1_2955_, lean_object* v_constName_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22(v_00_u03b1_2955_, v_constName_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23(lean_object* v_00_u03b2_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(v_x_2968_, v_x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28(lean_object* v_00_u03b1_2971_, lean_object* v_ref_2972_, lean_object* v_constName_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_2972_, v_constName_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2984_, lean_object* v_ref_2985_, lean_object* v_constName_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28(v_00_u03b1_2984_, v_ref_2985_, v_constName_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v_ref_2985_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30(lean_object* v_00_u03b1_2997_, lean_object* v_ref_2998_, lean_object* v_msg_2999_, lean_object* v_declHint_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_2998_, v_msg_2999_, v_declHint_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_ref_3012_, lean_object* v_msg_3013_, lean_object* v_declHint_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30(v_00_u03b1_3011_, v_ref_3012_, v_msg_3013_, v_declHint_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v_ref_3012_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32(lean_object* v_msg_3025_, lean_object* v_declHint_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(v_msg_3025_, v_declHint_3026_, v___y_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___boxed(lean_object* v_msg_3037_, lean_object* v_declHint_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32(v_msg_3037_, v_declHint_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec(v___y_3039_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32(lean_object* v_00_u03b1_3049_, lean_object* v_ref_3050_, lean_object* v_msg_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_3050_, v_msg_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___boxed(lean_object* v_00_u03b1_3062_, lean_object* v_ref_3063_, lean_object* v_msg_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32(v_00_u03b1_3062_, v_ref_3063_, v_msg_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec(v_ref_3063_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_options_3078_; uint8_t v_hasTrace_3079_; 
v_options_3078_ = lean_ctor_get(v___y_3076_, 2);
v_hasTrace_3079_ = lean_ctor_get_uint8(v_options_3078_, sizeof(void*)*1);
if (v_hasTrace_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v_cls_3075_);
v___x_3080_ = lean_box(v_hasTrace_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
else
{
lean_object* v_inheritedTraceOptions_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_inheritedTraceOptions_3082_ = lean_ctor_get(v___y_3076_, 13);
v___x_3083_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3084_ = l_Lean_Name_append(v___x_3083_, v_cls_3075_);
v___x_3085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3082_, v_options_3078_, v___x_3084_);
lean_dec(v___x_3084_);
v___x_3086_ = lean_box(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3088_, v___y_3089_);
lean_dec_ref(v___y_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3092_, v___y_3097_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(lean_object* v_cls_3110_, lean_object* v_msg_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_ref_3117_; lean_object* v___x_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3163_; 
v_ref_3117_ = lean_ctor_get(v___y_3114_, 5);
v___x_3118_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3163_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3163_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v_traceState_3124_; lean_object* v_env_3125_; lean_object* v_nextMacroScope_3126_; lean_object* v_ngen_3127_; lean_object* v_auxDeclNGen_3128_; lean_object* v_cache_3129_; lean_object* v_messages_3130_; lean_object* v_infoState_3131_; lean_object* v_snapshotTasks_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3162_; 
v___x_3123_ = lean_st_ref_take(v___y_3115_);
v_traceState_3124_ = lean_ctor_get(v___x_3123_, 4);
v_env_3125_ = lean_ctor_get(v___x_3123_, 0);
v_nextMacroScope_3126_ = lean_ctor_get(v___x_3123_, 1);
v_ngen_3127_ = lean_ctor_get(v___x_3123_, 2);
v_auxDeclNGen_3128_ = lean_ctor_get(v___x_3123_, 3);
v_cache_3129_ = lean_ctor_get(v___x_3123_, 5);
v_messages_3130_ = lean_ctor_get(v___x_3123_, 6);
v_infoState_3131_ = lean_ctor_get(v___x_3123_, 7);
v_snapshotTasks_3132_ = lean_ctor_get(v___x_3123_, 8);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3134_ = v___x_3123_;
v_isShared_3135_ = v_isSharedCheck_3162_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_snapshotTasks_3132_);
lean_inc(v_infoState_3131_);
lean_inc(v_messages_3130_);
lean_inc(v_cache_3129_);
lean_inc(v_traceState_3124_);
lean_inc(v_auxDeclNGen_3128_);
lean_inc(v_ngen_3127_);
lean_inc(v_nextMacroScope_3126_);
lean_inc(v_env_3125_);
lean_dec(v___x_3123_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3162_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
uint64_t v_tid_3136_; lean_object* v_traces_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3161_; 
v_tid_3136_ = lean_ctor_get_uint64(v_traceState_3124_, sizeof(void*)*1);
v_traces_3137_ = lean_ctor_get(v_traceState_3124_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_traceState_3124_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3139_ = v_traceState_3124_;
v_isShared_3140_ = v_isSharedCheck_3161_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_traces_3137_);
lean_dec(v_traceState_3124_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3161_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; double v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0);
v___x_3143_ = 0;
v___x_3144_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1));
v___x_3145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3145_, 0, v_cls_3110_);
lean_ctor_set(v___x_3145_, 1, v___x_3141_);
lean_ctor_set(v___x_3145_, 2, v___x_3144_);
lean_ctor_set_float(v___x_3145_, sizeof(void*)*3, v___x_3142_);
lean_ctor_set_float(v___x_3145_, sizeof(void*)*3 + 8, v___x_3142_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*3 + 16, v___x_3143_);
v___x_3146_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2));
v___x_3147_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v_a_3119_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
lean_inc(v_ref_3117_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_ref_3117_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l_Lean_PersistentArray_push___redArg(v_traces_3137_, v___x_3148_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3149_);
v___x_3151_ = v___x_3139_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3149_);
lean_ctor_set_uint64(v_reuseFailAlloc_3160_, sizeof(void*)*1, v_tid_3136_);
v___x_3151_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3153_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 4, v___x_3151_);
v___x_3153_ = v___x_3134_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_env_3125_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_nextMacroScope_3126_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_ngen_3127_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_auxDeclNGen_3128_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_cache_3129_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_messages_3130_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_infoState_3131_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_snapshotTasks_3132_);
v___x_3153_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_st_ref_set(v___y_3115_, v___x_3153_);
v___x_3155_ = lean_box(0);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3155_);
v___x_3157_ = v___x_3121_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg___boxed(lean_object* v_cls_3164_, lean_object* v_msg_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3164_, v_msg_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3171_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_unsigned_to_nat(16u);
v___x_3174_ = lean_mk_array(v___x_3173_, v___x_3172_);
return v___x_3174_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3176_ = lean_unsigned_to_nat(0u);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3175_);
return v___x_3177_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3187_, lean_object* v_fixedPrefixSize_3188_, lean_object* v_F_3189_, lean_object* v_e_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v_cls_3219_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___x_3248_; lean_object* v_a_3249_; uint8_t v___x_3250_; 
v_cls_3219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3248_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3219_, v_a_3195_);
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = lean_unbox(v_a_3249_);
lean_dec(v_a_3249_);
if (v___x_3250_ == 0)
{
v___y_3221_ = v_a_3191_;
v___y_3222_ = v_a_3192_;
v___y_3223_ = v_a_3193_;
v___y_3224_ = v_a_3194_;
v___y_3225_ = v_a_3195_;
v___y_3226_ = v_a_3196_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3190_);
v___x_3252_ = l_Lean_indentExpr(v_e_3190_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3219_, v___x_3253_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref(v___x_3254_);
v___y_3221_ = v_a_3191_;
v___y_3222_ = v_a_3192_;
v___y_3223_ = v_a_3193_;
v___y_3224_ = v_a_3194_;
v___y_3225_ = v_a_3195_;
v___y_3226_ = v_a_3196_;
goto v___jp_3220_;
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec_ref(v_e_3190_);
lean_dec_ref(v_F_3189_);
lean_dec(v_fixedPrefixSize_3188_);
lean_dec(v_recFnName_3187_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
v___jp_3198_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3205_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3206_ = lean_st_mk_ref(v___x_3205_);
v___x_3207_ = lean_st_mk_ref(v___x_3205_);
lean_inc(v___x_3206_);
lean_inc(v___x_3207_);
v___x_3208_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3187_, v_fixedPrefixSize_3188_, v_F_3189_, v_e_3190_, v___x_3207_, v___x_3206_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3218_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3213_ = lean_st_ref_get(v___x_3207_);
lean_dec(v___x_3207_);
lean_dec(v___x_3213_);
v___x_3214_ = lean_st_ref_get(v___x_3206_);
lean_dec(v___x_3206_);
lean_dec(v___x_3214_);
if (v_isShared_3212_ == 0)
{
v___x_3216_ = v___x_3211_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3209_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
lean_dec(v___x_3207_);
lean_dec(v___x_3206_);
return v___x_3208_;
}
}
v___jp_3220_:
{
lean_object* v___x_3227_; lean_object* v_a_3228_; uint8_t v___x_3229_; 
v___x_3227_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3219_, v___y_3225_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = lean_unbox(v_a_3228_);
lean_dec(v_a_3228_);
if (v___x_3229_ == 0)
{
v___y_3199_ = v___y_3221_;
v___y_3200_ = v___y_3222_;
v___y_3201_ = v___y_3223_;
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3226_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3230_; 
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc_ref(v_F_3189_);
v___x_3230_ = lean_infer_type(v_F_3189_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref(v___x_3230_);
v___x_3232_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3189_);
v___x_3233_ = l_Lean_MessageData_ofExpr(v_F_3189_);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Lean_indentExpr(v_a_3231_);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3219_, v___x_3238_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref(v___x_3239_);
v___y_3199_ = v___y_3221_;
v___y_3200_ = v___y_3222_;
v___y_3201_ = v___y_3223_;
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3226_;
goto v___jp_3198_;
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v_e_3190_);
lean_dec_ref(v_F_3189_);
lean_dec(v_fixedPrefixSize_3188_);
lean_dec(v_recFnName_3187_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v_e_3190_);
lean_dec_ref(v_F_3189_);
lean_dec(v_fixedPrefixSize_3188_);
lean_dec(v_recFnName_3187_);
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3263_, lean_object* v_fixedPrefixSize_3264_, lean_object* v_F_3265_, lean_object* v_e_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3263_, v_fixedPrefixSize_3264_, v_F_3265_, v_e_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1(lean_object* v_cls_3275_, lean_object* v_msg_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3275_, v_msg_3276_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___boxed(lean_object* v_cls_3285_, lean_object* v_msg_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1(v_cls_3285_, v_msg_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v_b_3298_, lean_object* v_c_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_apply_9(v_k_3295_, v_b_3298_, v_c_3299_, v___y_3296_, v___y_3297_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, lean_box(0));
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v_b_3309_, lean_object* v_c_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3306_, v___y_3307_, v___y_3308_, v_b_3309_, v_c_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3317_, lean_object* v_maxFVars_3318_, lean_object* v_k_3319_, uint8_t v_cleanupAnnotations_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___f_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3328_, 0, v_k_3319_);
lean_closure_set(v___f_3328_, 1, v___y_3321_);
lean_closure_set(v___f_3328_, 2, v___y_3322_);
v___x_3329_ = 1;
v___x_3330_ = 0;
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_maxFVars_3318_);
v___x_3332_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3317_, v___x_3329_, v___x_3330_, v___x_3329_, v___x_3330_, v___x_3331_, v___f_3328_, v_cleanupAnnotations_3320_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec_ref(v___x_3331_);
if (lean_obj_tag(v___x_3332_) == 0)
{
return v___x_3332_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3341_, lean_object* v_maxFVars_3342_, lean_object* v_k_3343_, lean_object* v_cleanupAnnotations_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3352_; lean_object* v_res_3353_; 
v_cleanupAnnotations_boxed_3352_ = lean_unbox(v_cleanupAnnotations_3344_);
v_res_3353_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3341_, v_maxFVars_3342_, v_k_3343_, v_cleanupAnnotations_boxed_3352_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3354_, lean_object* v_e_3355_, lean_object* v_maxFVars_3356_, lean_object* v_k_3357_, uint8_t v_cleanupAnnotations_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3355_, v_maxFVars_3356_, v_k_3357_, v_cleanupAnnotations_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3367_, lean_object* v_e_3368_, lean_object* v_maxFVars_3369_, lean_object* v_k_3370_, lean_object* v_cleanupAnnotations_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3379_; lean_object* v_res_3380_; 
v_cleanupAnnotations_boxed_3379_ = lean_unbox(v_cleanupAnnotations_3371_);
v_res_3380_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3367_, v_e_3368_, v_maxFVars_3369_, v_k_3370_, v_cleanupAnnotations_boxed_3379_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3381_, lean_object* v_k_3382_, uint8_t v_cleanupAnnotations_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___f_3391_; uint8_t v___x_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3391_, 0, v_k_3382_);
lean_closure_set(v___f_3391_, 1, v___y_3384_);
lean_closure_set(v___f_3391_, 2, v___y_3385_);
v___x_3392_ = 1;
v___x_3393_ = 0;
v___x_3394_ = lean_box(0);
v___x_3395_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3381_, v___x_3392_, v___x_3393_, v___x_3392_, v___x_3393_, v___x_3394_, v___f_3391_, v_cleanupAnnotations_3383_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3395_) == 0)
{
return v___x_3395_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3404_, lean_object* v_k_3405_, lean_object* v_cleanupAnnotations_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3414_; lean_object* v_res_3415_; 
v_cleanupAnnotations_boxed_3414_ = lean_unbox(v_cleanupAnnotations_3406_);
v_res_3415_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3404_, v_k_3405_, v_cleanupAnnotations_boxed_3414_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3416_, lean_object* v_e_3417_, lean_object* v_k_3418_, uint8_t v_cleanupAnnotations_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3417_, v_k_3418_, v_cleanupAnnotations_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_e_3429_, lean_object* v_k_3430_, lean_object* v_cleanupAnnotations_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3439_; lean_object* v_res_3440_; 
v_cleanupAnnotations_boxed_3439_ = lean_unbox(v_cleanupAnnotations_3431_);
v_res_3440_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3428_, v_e_3429_, v_k_3430_, v_cleanupAnnotations_boxed_3439_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v_x_3444_, uint8_t v___x_3445_, lean_object* v_xs_3446_, lean_object* v_type_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3455_ = l_Lean_LocalDecl_type(v_a_3441_);
v___x_3456_ = lean_array_get_borrowed(v___x_3442_, v_xs_3446_, v___x_3443_);
v___x_3457_ = l_Lean_Expr_replaceFVar(v___x_3455_, v_x_3444_, v___x_3456_);
lean_dec_ref(v___x_3455_);
lean_inc(v___y_3453_);
lean_inc_ref(v___y_3452_);
v___x_3458_ = l_Lean_mkArrow(v___x_3457_, v_type_3447_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; uint8_t v___x_3460_; uint8_t v___x_3461_; lean_object* v___x_3462_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3458_);
v___x_3460_ = 0;
v___x_3461_ = 1;
lean_inc(v_a_3459_);
v___x_3462_ = l_Lean_Meta_mkLambdaFVars(v_xs_3446_, v_a_3459_, v___x_3460_, v___x_3445_, v___x_3460_, v___x_3445_, v___x_3461_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = l_Lean_Meta_getLevel(v_a_3459_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3473_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v_a_3463_);
lean_ctor_set(v___x_3469_, 1, v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3469_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_a_3463_);
v_a_3474_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3464_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3464_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v_a_3459_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
v_a_3482_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3462_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3462_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
v_a_3490_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3458_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3458_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3498_, lean_object* v___x_3499_, lean_object* v___x_3500_, lean_object* v_x_3501_, lean_object* v___x_3502_, lean_object* v_xs_3503_, lean_object* v_type_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
uint8_t v___x_6837__boxed_3512_; lean_object* v_res_3513_; 
v___x_6837__boxed_3512_ = lean_unbox(v___x_3502_);
v_res_3513_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3498_, v___x_3499_, v___x_3500_, v_x_3501_, v___x_6837__boxed_3512_, v_xs_3503_, v_type_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v_xs_3503_);
lean_dec(v___x_3500_);
lean_dec_ref(v_a_3498_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_apply_8(v_k_3514_, v_b_3517_, v___y_3515_, v___y_3516_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, lean_box(0));
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v_b_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3524_, v___y_3525_, v___y_3526_, v_b_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3534_, uint8_t v_bi_3535_, lean_object* v_type_3536_, lean_object* v_k_3537_, uint8_t v_kind_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___f_3546_; lean_object* v___x_3547_; 
v___f_3546_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3546_, 0, v_k_3537_);
lean_closure_set(v___f_3546_, 1, v___y_3539_);
lean_closure_set(v___f_3546_, 2, v___y_3540_);
v___x_3547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3534_, v_bi_3535_, v_type_3536_, v___f_3546_, v_kind_3538_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3547_) == 0)
{
return v___x_3547_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3556_, lean_object* v_bi_3557_, lean_object* v_type_3558_, lean_object* v_k_3559_, lean_object* v_kind_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
uint8_t v_bi_boxed_3568_; uint8_t v_kind_boxed_3569_; lean_object* v_res_3570_; 
v_bi_boxed_3568_ = lean_unbox(v_bi_3557_);
v_kind_boxed_3569_ = lean_unbox(v_kind_3560_);
v_res_3570_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3556_, v_bi_boxed_3568_, v_type_3558_, v_k_3559_, v_kind_boxed_3569_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3571_, lean_object* v_type_3572_, lean_object* v_k_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = 0;
v___x_3582_ = 0;
v___x_3583_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3571_, v___x_3581_, v_type_3572_, v_k_3573_, v___x_3582_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3584_, lean_object* v_type_3585_, lean_object* v_k_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3584_, v_type_3585_, v_k_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3608_, lean_object* v_F_3609_, lean_object* v_val_3610_, lean_object* v_k_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
uint8_t v___y_3620_; uint8_t v___x_3735_; 
v___x_3735_ = l_Lean_Expr_isFVar(v_x_3608_);
if (v___x_3735_ == 0)
{
v___y_3620_ = v___x_3735_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3737_ = lean_unsigned_to_nat(6u);
v___x_3738_ = l_Lean_Expr_isAppOfArity(v_val_3610_, v___x_3736_, v___x_3737_);
v___y_3620_ = v___x_3738_;
goto v___jp_3619_;
}
v___jp_3619_:
{
if (v___y_3620_ == 0)
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_apply_10(v_k_3611_, v_x_3608_, v_F_3609_, v_val_3610_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, lean_box(0));
return v___x_3621_;
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3622_ = lean_unsigned_to_nat(3u);
v___x_3623_ = l_Lean_Expr_getAppNumArgs(v_val_3610_);
v___x_3624_ = lean_nat_sub(v___x_3623_, v___x_3622_);
v___x_3625_ = lean_unsigned_to_nat(1u);
v___x_3626_ = lean_nat_sub(v___x_3624_, v___x_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = l_Lean_Expr_getRevArg_x21(v_val_3610_, v___x_3626_);
v___x_3628_ = lean_expr_eqv(v___x_3627_, v_x_3608_);
lean_dec_ref(v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
lean_dec(v___x_3623_);
v___x_3629_ = lean_apply_10(v_k_3611_, v_x_3608_, v_F_3609_, v_val_3610_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, lean_box(0));
return v___x_3629_;
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3630_ = lean_unsigned_to_nat(4u);
v___x_3631_ = lean_nat_sub(v___x_3623_, v___x_3630_);
v___x_3632_ = lean_nat_sub(v___x_3631_, v___x_3625_);
lean_dec(v___x_3631_);
v___x_3633_ = l_Lean_Expr_getRevArg_x21(v_val_3610_, v___x_3632_);
v___x_3634_ = l_Lean_Expr_isLambda(v___x_3633_);
lean_dec_ref(v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec(v___x_3623_);
v___x_3635_ = lean_apply_10(v_k_3611_, v_x_3608_, v_F_3609_, v_val_3610_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, lean_box(0));
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3636_ = lean_unsigned_to_nat(5u);
v___x_3637_ = lean_nat_sub(v___x_3623_, v___x_3636_);
v___x_3638_ = lean_nat_sub(v___x_3637_, v___x_3625_);
lean_dec(v___x_3637_);
v___x_3639_ = l_Lean_Expr_getRevArg_x21(v_val_3610_, v___x_3638_);
v___x_3640_ = l_Lean_Expr_isLambda(v___x_3639_);
lean_dec_ref(v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_dec(v___x_3623_);
v___x_3641_ = lean_apply_10(v_k_3611_, v_x_3608_, v_F_3609_, v_val_3610_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, lean_box(0));
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = l_Lean_Expr_fvarId_x21(v_F_3609_);
lean_inc_ref(v_a_3614_);
v___x_3643_ = l_Lean_FVarId_getDecl___redArg(v___x_3642_, v_a_3614_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v_dummy_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_args_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v_00_u03b1_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; lean_object* v_00_u03b2_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3643_);
v_dummy_3645_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_3623_);
v___x_3646_ = lean_mk_array(v___x_3623_, v_dummy_3645_);
v___x_3647_ = lean_nat_sub(v___x_3623_, v___x_3625_);
lean_dec(v___x_3623_);
v_args_3648_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3610_, v___x_3646_, v___x_3647_);
v___x_3649_ = l_Lean_instInhabitedExpr;
v___x_3650_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3651_ = lean_array_get(v___x_3649_, v_args_3648_, v___x_3650_);
v___x_3652_ = lean_box(v___x_3634_);
lean_inc_ref(v_x_3608_);
lean_inc(v_a_3644_);
v___f_3653_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3653_, 0, v_a_3644_);
lean_closure_set(v___f_3653_, 1, v___x_3649_);
lean_closure_set(v___f_3653_, 2, v___x_3650_);
lean_closure_set(v___f_3653_, 3, v_x_3608_);
lean_closure_set(v___f_3653_, 4, v___x_3652_);
v_00_u03b2_3654_ = lean_array_get(v___x_3649_, v_args_3648_, v___x_3625_);
v___x_3655_ = lean_unsigned_to_nat(2u);
v___x_3656_ = lean_array_get(v___x_3649_, v_args_3648_, v___x_3655_);
v___x_3657_ = 0;
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
v___x_3658_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3656_, v___f_3653_, v___x_3657_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v_fst_3660_; lean_object* v_snd_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3718_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v_fst_3660_ = lean_ctor_get(v_a_3659_, 0);
v_snd_3661_ = lean_ctor_get(v_a_3659_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_a_3659_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3663_ = v_a_3659_;
v_isShared_3664_ = v_isSharedCheck_3718_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_snd_3661_);
lean_inc(v_fst_3660_);
lean_dec(v_a_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3718_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3666_ = lean_array_get(v___x_3649_, v_args_3648_, v___x_3630_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc_ref(v_x_3608_);
lean_inc(v_a_3644_);
lean_inc_ref(v_k_3611_);
lean_inc(v_00_u03b2_3654_);
lean_inc(v_00_u03b1_3651_);
v___x_3667_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3649_, v___x_3650_, v_00_u03b1_3651_, v_00_u03b2_3654_, v___x_3622_, v_k_3611_, v___x_3655_, v___x_3657_, v___x_3634_, v_a_3644_, v_x_3608_, v___x_3625_, v___x_3665_, v___x_3666_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
v___x_3669_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3670_ = lean_array_get(v___x_3649_, v_args_3648_, v___x_3636_);
lean_dec_ref(v_args_3648_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc_ref(v_x_3608_);
lean_inc(v_00_u03b2_3654_);
lean_inc(v_00_u03b1_3651_);
v___x_3671_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3649_, v___x_3650_, v_00_u03b1_3651_, v_00_u03b2_3654_, v___x_3622_, v_k_3611_, v___x_3655_, v___x_3657_, v___x_3634_, v_a_3644_, v_x_3608_, v___x_3625_, v___x_3669_, v___x_3670_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_00_u03b1_3651_);
v___x_3673_ = l_Lean_Meta_getLevel(v_00_u03b1_3651_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
lean_inc(v_00_u03b2_3654_);
v___x_3675_ = l_Lean_Meta_getLevel(v_00_u03b2_3654_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3701_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3701_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3701_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3680_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3681_ = lean_box(0);
if (v_isShared_3664_ == 0)
{
lean_ctor_set_tag(v___x_3663_, 1);
lean_ctor_set(v___x_3663_, 1, v___x_3681_);
lean_ctor_set(v___x_3663_, 0, v_a_3676_);
v___x_3683_ = v___x_3663_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3676_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3684_, 0, v_a_3674_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_snd_3661_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = l_Lean_mkConst(v___x_3680_, v___x_3685_);
v___x_3687_ = lean_unsigned_to_nat(7u);
v___x_3688_ = lean_mk_empty_array_with_capacity(v___x_3687_);
v___x_3689_ = lean_array_push(v___x_3688_, v_00_u03b1_3651_);
v___x_3690_ = lean_array_push(v___x_3689_, v_00_u03b2_3654_);
v___x_3691_ = lean_array_push(v___x_3690_, v_fst_3660_);
v___x_3692_ = lean_array_push(v___x_3691_, v_x_3608_);
v___x_3693_ = lean_array_push(v___x_3692_, v_a_3668_);
v___x_3694_ = lean_array_push(v___x_3693_, v_a_3672_);
v___x_3695_ = lean_array_push(v___x_3694_, v_F_3609_);
v___x_3696_ = l_Lean_mkAppN(v___x_3686_, v___x_3695_);
lean_dec_ref(v___x_3695_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3696_);
v___x_3698_ = v___x_3678_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_dec(v_a_3674_);
lean_dec(v_a_3672_);
lean_dec(v_a_3668_);
lean_del_object(v___x_3663_);
lean_dec(v_snd_3661_);
lean_dec(v_fst_3660_);
lean_dec(v_00_u03b2_3654_);
lean_dec(v_00_u03b1_3651_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
v_a_3702_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3675_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3675_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_a_3672_);
lean_dec(v_a_3668_);
lean_del_object(v___x_3663_);
lean_dec(v_snd_3661_);
lean_dec(v_fst_3660_);
lean_dec(v_00_u03b2_3654_);
lean_dec(v_00_u03b1_3651_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
v_a_3710_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3673_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3673_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_dec(v_a_3668_);
lean_del_object(v___x_3663_);
lean_dec(v_snd_3661_);
lean_dec(v_fst_3660_);
lean_dec(v_00_u03b2_3654_);
lean_dec(v_00_u03b1_3651_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
return v___x_3671_;
}
}
else
{
lean_del_object(v___x_3663_);
lean_dec(v_snd_3661_);
lean_dec(v_fst_3660_);
lean_dec(v_00_u03b2_3654_);
lean_dec(v_00_u03b1_3651_);
lean_dec_ref(v_args_3648_);
lean_dec(v_a_3644_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec_ref(v_k_3611_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
return v___x_3667_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_00_u03b2_3654_);
lean_dec(v_00_u03b1_3651_);
lean_dec_ref(v_args_3648_);
lean_dec(v_a_3644_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec_ref(v_k_3611_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
v_a_3719_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3658_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3658_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v___x_3623_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec_ref(v_k_3611_);
lean_dec_ref(v_val_3610_);
lean_dec_ref(v_F_3609_);
lean_dec_ref(v_x_3608_);
v_a_3727_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3643_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3643_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3739_, lean_object* v_body_3740_, lean_object* v_k_3741_, lean_object* v___x_3742_, uint8_t v___x_3743_, uint8_t v___x_3744_, lean_object* v_FNew_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
lean_inc(v___y_3751_);
lean_inc_ref(v___y_3750_);
lean_inc(v___y_3749_);
lean_inc_ref(v___y_3748_);
lean_inc_ref(v_FNew_3745_);
lean_inc_ref(v___x_3739_);
v___x_3753_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3739_, v_FNew_3745_, v_body_3740_, v_k_3741_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; lean_object* v___x_3759_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = lean_mk_empty_array_with_capacity(v___x_3742_);
v___x_3756_ = lean_array_push(v___x_3755_, v___x_3739_);
v___x_3757_ = lean_array_push(v___x_3756_, v_FNew_3745_);
v___x_3758_ = 1;
v___x_3759_ = l_Lean_Meta_mkLambdaFVars(v___x_3757_, v_a_3754_, v___x_3743_, v___x_3744_, v___x_3743_, v___x_3744_, v___x_3758_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec_ref(v___x_3757_);
return v___x_3759_;
}
else
{
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec_ref(v_FNew_3745_);
lean_dec_ref(v___x_3739_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3760_, lean_object* v_body_3761_, lean_object* v_k_3762_, lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v___x_3765_, lean_object* v_FNew_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
uint8_t v___x_7083__boxed_3774_; uint8_t v___x_7084__boxed_3775_; lean_object* v_res_3776_; 
v___x_7083__boxed_3774_ = lean_unbox(v___x_3764_);
v___x_7084__boxed_3775_ = lean_unbox(v___x_3765_);
v_res_3776_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3760_, v_body_3761_, v_k_3762_, v___x_3763_, v___x_7083__boxed_3774_, v___x_7084__boxed_3775_, v_FNew_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___x_3763_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3777_, lean_object* v___x_3778_, lean_object* v_00_u03b1_3779_, lean_object* v_00_u03b2_3780_, lean_object* v___x_3781_, lean_object* v_ctorName_3782_, lean_object* v_k_3783_, lean_object* v___x_3784_, uint8_t v___x_3785_, uint8_t v___x_3786_, lean_object* v_a_3787_, lean_object* v_x_3788_, lean_object* v_xs_3789_, lean_object* v_body_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3798_ = lean_array_get_borrowed(v___x_3777_, v_xs_3789_, v___x_3778_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_00_u03b1_3779_);
v___x_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3800_, 0, v_00_u03b2_3780_);
lean_inc(v___x_3798_);
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3798_);
v___x_3802_ = lean_mk_empty_array_with_capacity(v___x_3781_);
v___x_3803_ = lean_array_push(v___x_3802_, v___x_3799_);
v___x_3804_ = lean_array_push(v___x_3803_, v___x_3800_);
v___x_3805_ = lean_array_push(v___x_3804_, v___x_3801_);
lean_inc(v___y_3796_);
lean_inc_ref(v___y_3795_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
v___x_3806_ = l_Lean_Meta_mkAppOptM(v_ctorName_3782_, v___x_3805_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___f_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = lean_box(v___x_3785_);
v___x_3809_ = lean_box(v___x_3786_);
lean_inc(v___x_3798_);
v___f_3810_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3810_, 0, v___x_3798_);
lean_closure_set(v___f_3810_, 1, v_body_3790_);
lean_closure_set(v___f_3810_, 2, v_k_3783_);
lean_closure_set(v___f_3810_, 3, v___x_3784_);
lean_closure_set(v___f_3810_, 4, v___x_3808_);
lean_closure_set(v___f_3810_, 5, v___x_3809_);
v___x_3811_ = l_Lean_LocalDecl_type(v_a_3787_);
v___x_3812_ = l_Lean_Expr_replaceFVar(v___x_3811_, v_x_3788_, v_a_3807_);
lean_dec(v_a_3807_);
lean_dec_ref(v___x_3811_);
v___x_3813_ = l_Lean_LocalDecl_userName(v_a_3787_);
v___x_3814_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3813_, v___x_3812_, v___f_3810_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3814_;
}
else
{
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_body_3790_);
lean_dec_ref(v_x_3788_);
lean_dec(v___x_3784_);
lean_dec_ref(v_k_3783_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3815_ = _args[0];
lean_object* v___x_3816_ = _args[1];
lean_object* v_00_u03b1_3817_ = _args[2];
lean_object* v_00_u03b2_3818_ = _args[3];
lean_object* v___x_3819_ = _args[4];
lean_object* v_ctorName_3820_ = _args[5];
lean_object* v_k_3821_ = _args[6];
lean_object* v___x_3822_ = _args[7];
lean_object* v___x_3823_ = _args[8];
lean_object* v___x_3824_ = _args[9];
lean_object* v_a_3825_ = _args[10];
lean_object* v_x_3826_ = _args[11];
lean_object* v_xs_3827_ = _args[12];
lean_object* v_body_3828_ = _args[13];
lean_object* v___y_3829_ = _args[14];
lean_object* v___y_3830_ = _args[15];
lean_object* v___y_3831_ = _args[16];
lean_object* v___y_3832_ = _args[17];
lean_object* v___y_3833_ = _args[18];
lean_object* v___y_3834_ = _args[19];
lean_object* v___y_3835_ = _args[20];
_start:
{
uint8_t v___x_7104__boxed_3836_; uint8_t v___x_7105__boxed_3837_; lean_object* v_res_3838_; 
v___x_7104__boxed_3836_ = lean_unbox(v___x_3823_);
v___x_7105__boxed_3837_ = lean_unbox(v___x_3824_);
v_res_3838_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3815_, v___x_3816_, v_00_u03b1_3817_, v_00_u03b2_3818_, v___x_3819_, v_ctorName_3820_, v_k_3821_, v___x_3822_, v___x_7104__boxed_3836_, v___x_7105__boxed_3837_, v_a_3825_, v_x_3826_, v_xs_3827_, v_body_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec_ref(v_xs_3827_);
lean_dec_ref(v_a_3825_);
lean_dec(v___x_3819_);
lean_dec(v___x_3816_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_00_u03b1_3841_, lean_object* v_00_u03b2_3842_, lean_object* v___x_3843_, lean_object* v_k_3844_, lean_object* v___x_3845_, uint8_t v___x_3846_, uint8_t v___x_3847_, lean_object* v_a_3848_, lean_object* v_x_3849_, lean_object* v___x_3850_, lean_object* v_ctorName_3851_, lean_object* v_minor_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___f_3862_; lean_object* v___x_3863_; 
v___x_3860_ = lean_box(v___x_3846_);
v___x_3861_ = lean_box(v___x_3847_);
v___f_3862_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3862_, 0, v___x_3839_);
lean_closure_set(v___f_3862_, 1, v___x_3840_);
lean_closure_set(v___f_3862_, 2, v_00_u03b1_3841_);
lean_closure_set(v___f_3862_, 3, v_00_u03b2_3842_);
lean_closure_set(v___f_3862_, 4, v___x_3843_);
lean_closure_set(v___f_3862_, 5, v_ctorName_3851_);
lean_closure_set(v___f_3862_, 6, v_k_3844_);
lean_closure_set(v___f_3862_, 7, v___x_3845_);
lean_closure_set(v___f_3862_, 8, v___x_3860_);
lean_closure_set(v___f_3862_, 9, v___x_3861_);
lean_closure_set(v___f_3862_, 10, v_a_3848_);
lean_closure_set(v___f_3862_, 11, v_x_3849_);
v___x_3863_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3852_, v___x_3850_, v___f_3862_, v___x_3846_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3864_ = _args[0];
lean_object* v___x_3865_ = _args[1];
lean_object* v_00_u03b1_3866_ = _args[2];
lean_object* v_00_u03b2_3867_ = _args[3];
lean_object* v___x_3868_ = _args[4];
lean_object* v_k_3869_ = _args[5];
lean_object* v___x_3870_ = _args[6];
lean_object* v___x_3871_ = _args[7];
lean_object* v___x_3872_ = _args[8];
lean_object* v_a_3873_ = _args[9];
lean_object* v_x_3874_ = _args[10];
lean_object* v___x_3875_ = _args[11];
lean_object* v_ctorName_3876_ = _args[12];
lean_object* v_minor_3877_ = _args[13];
lean_object* v___y_3878_ = _args[14];
lean_object* v___y_3879_ = _args[15];
lean_object* v___y_3880_ = _args[16];
lean_object* v___y_3881_ = _args[17];
lean_object* v___y_3882_ = _args[18];
lean_object* v___y_3883_ = _args[19];
lean_object* v___y_3884_ = _args[20];
_start:
{
uint8_t v___x_7068__boxed_3885_; uint8_t v___x_7069__boxed_3886_; lean_object* v_res_3887_; 
v___x_7068__boxed_3885_ = lean_unbox(v___x_3871_);
v___x_7069__boxed_3886_ = lean_unbox(v___x_3872_);
v_res_3887_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3864_, v___x_3865_, v_00_u03b1_3866_, v_00_u03b2_3867_, v___x_3868_, v_k_3869_, v___x_3870_, v___x_7068__boxed_3885_, v___x_7069__boxed_3886_, v_a_3873_, v_x_3874_, v___x_3875_, v_ctorName_3876_, v_minor_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3888_, lean_object* v_F_3889_, lean_object* v_val_3890_, lean_object* v_k_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3888_, v_F_3889_, v_val_3890_, v_k_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3900_, lean_object* v_name_3901_, uint8_t v_bi_3902_, lean_object* v_type_3903_, lean_object* v_k_3904_, uint8_t v_kind_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3901_, v_bi_3902_, v_type_3903_, v_k_3904_, v_kind_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3914_, lean_object* v_name_3915_, lean_object* v_bi_3916_, lean_object* v_type_3917_, lean_object* v_k_3918_, lean_object* v_kind_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v_bi_boxed_3927_; uint8_t v_kind_boxed_3928_; lean_object* v_res_3929_; 
v_bi_boxed_3927_ = lean_unbox(v_bi_3916_);
v_kind_boxed_3928_ = lean_unbox(v_kind_3919_);
v_res_3929_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3914_, v_name_3915_, v_bi_boxed_3927_, v_type_3917_, v_k_3918_, v_kind_boxed_3928_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3930_, lean_object* v_name_3931_, lean_object* v_type_3932_, lean_object* v_k_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3931_, v_type_3932_, v_k_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3942_, lean_object* v_name_3943_, lean_object* v_type_3944_, lean_object* v_k_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3942_, v_name_3943_, v_type_3944_, v_k_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v_res_3953_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3942__overap_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3942__overap_3964_ = lean_panic_fn(v___x_3963_, v_msg_3955_);
v___x_3965_ = lean_apply_7(v___x_3942__overap_3964_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, lean_box(0));
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
return v_res_3974_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3978_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3979_ = lean_unsigned_to_nat(49u);
v___x_3980_ = lean_unsigned_to_nat(186u);
v___x_3981_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3983_ = l_mkPanicMessageWithDecl(v___x_3982_, v___x_3981_, v___x_3980_, v___x_3979_, v___x_3978_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3989_, lean_object* v_a_3990_, lean_object* v_k_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v___x_3995_, lean_object* v___x_3996_, lean_object* v_FNew_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
uint8_t v___x_4110__boxed_4005_; uint8_t v___x_4111__boxed_4006_; uint8_t v___x_4112__boxed_4007_; lean_object* v_res_4008_; 
v___x_4110__boxed_4005_ = lean_unbox(v___x_3994_);
v___x_4111__boxed_4006_ = lean_unbox(v___x_3995_);
v___x_4112__boxed_4007_ = lean_unbox(v___x_3996_);
v_res_4008_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3989_, v_a_3990_, v_k_3991_, v___x_3992_, v___x_3993_, v___x_4110__boxed_4005_, v___x_4111__boxed_4006_, v___x_4112__boxed_4007_, v_FNew_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___x_3992_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, uint8_t v___x_4013_, uint8_t v___x_4014_, lean_object* v_00_u03b1_4015_, lean_object* v_00_u03b2_4016_, lean_object* v___x_4017_, lean_object* v_k_4018_, lean_object* v___x_4019_, lean_object* v_a_4020_, lean_object* v_x_4021_, lean_object* v_xs_4022_, lean_object* v_body_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; lean_object* v___x_4037_; 
lean_inc_ref(v___x_4009_);
v___x_4031_ = lean_array_get(v___x_4009_, v_xs_4022_, v___x_4010_);
v___x_4032_ = lean_array_get(v___x_4009_, v_xs_4022_, v___x_4011_);
v___x_4033_ = lean_array_get_size(v_xs_4022_);
v___x_4034_ = l_Array_toSubarray___redArg(v_xs_4022_, v___x_4012_, v___x_4033_);
v___x_4035_ = l_Subarray_copy___redArg(v___x_4034_);
v___x_4036_ = 1;
v___x_4037_ = l_Lean_Meta_mkLambdaFVars(v___x_4035_, v_body_4023_, v___x_4013_, v___x_4014_, v___x_4013_, v___x_4014_, v___x_4036_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec_ref(v___x_4035_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4064_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4064_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4064_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4042_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_4041_ == 0)
{
lean_ctor_set_tag(v___x_4040_, 1);
lean_ctor_set(v___x_4040_, 0, v_00_u03b1_4015_);
v___x_4044_ = v___x_4040_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_00_u03b1_4015_);
v___x_4044_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_00_u03b2_4016_);
lean_inc(v___x_4031_);
v___x_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4031_);
lean_inc(v___x_4032_);
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4032_);
v___x_4048_ = lean_mk_empty_array_with_capacity(v___x_4017_);
v___x_4049_ = lean_array_push(v___x_4048_, v___x_4044_);
v___x_4050_ = lean_array_push(v___x_4049_, v___x_4045_);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_4046_);
v___x_4052_ = lean_array_push(v___x_4051_, v___x_4047_);
lean_inc(v___y_4029_);
lean_inc_ref(v___y_4028_);
lean_inc(v___y_4027_);
lean_inc_ref(v___y_4026_);
v___x_4053_ = l_Lean_Meta_mkAppOptM(v___x_4042_, v___x_4052_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = lean_box(v___x_4013_);
v___x_4056_ = lean_box(v___x_4014_);
v___x_4057_ = lean_box(v___x_4036_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4058_, 0, v___x_4032_);
lean_closure_set(v___f_4058_, 1, v_a_4038_);
lean_closure_set(v___f_4058_, 2, v_k_4018_);
lean_closure_set(v___f_4058_, 3, v___x_4019_);
lean_closure_set(v___f_4058_, 4, v___x_4031_);
lean_closure_set(v___f_4058_, 5, v___x_4055_);
lean_closure_set(v___f_4058_, 6, v___x_4056_);
lean_closure_set(v___f_4058_, 7, v___x_4057_);
v___x_4059_ = l_Lean_LocalDecl_type(v_a_4020_);
v___x_4060_ = l_Lean_Expr_replaceFVar(v___x_4059_, v_x_4021_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v___x_4059_);
v___x_4061_ = l_Lean_LocalDecl_userName(v_a_4020_);
v___x_4062_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4061_, v___x_4060_, v___f_4058_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
return v___x_4062_;
}
else
{
lean_dec(v_a_4038_);
lean_dec(v___x_4032_);
lean_dec(v___x_4031_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec_ref(v_x_4021_);
lean_dec(v___x_4019_);
lean_dec_ref(v_k_4018_);
return v___x_4053_;
}
}
}
}
else
{
lean_dec(v___x_4032_);
lean_dec(v___x_4031_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec_ref(v_x_4021_);
lean_dec(v___x_4019_);
lean_dec_ref(v_k_4018_);
lean_dec_ref(v_00_u03b2_4016_);
lean_dec_ref(v_00_u03b1_4015_);
return v___x_4037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_4065_ = _args[0];
lean_object* v___x_4066_ = _args[1];
lean_object* v___x_4067_ = _args[2];
lean_object* v___x_4068_ = _args[3];
lean_object* v___x_4069_ = _args[4];
lean_object* v___x_4070_ = _args[5];
lean_object* v_00_u03b1_4071_ = _args[6];
lean_object* v_00_u03b2_4072_ = _args[7];
lean_object* v___x_4073_ = _args[8];
lean_object* v_k_4074_ = _args[9];
lean_object* v___x_4075_ = _args[10];
lean_object* v_a_4076_ = _args[11];
lean_object* v_x_4077_ = _args[12];
lean_object* v_xs_4078_ = _args[13];
lean_object* v_body_4079_ = _args[14];
lean_object* v___y_4080_ = _args[15];
lean_object* v___y_4081_ = _args[16];
lean_object* v___y_4082_ = _args[17];
lean_object* v___y_4083_ = _args[18];
lean_object* v___y_4084_ = _args[19];
lean_object* v___y_4085_ = _args[20];
lean_object* v___y_4086_ = _args[21];
_start:
{
uint8_t v___x_4137__boxed_4087_; uint8_t v___x_4138__boxed_4088_; lean_object* v_res_4089_; 
v___x_4137__boxed_4087_ = lean_unbox(v___x_4069_);
v___x_4138__boxed_4088_ = lean_unbox(v___x_4070_);
v_res_4089_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_4065_, v___x_4066_, v___x_4067_, v___x_4068_, v___x_4137__boxed_4087_, v___x_4138__boxed_4088_, v_00_u03b1_4071_, v_00_u03b2_4072_, v___x_4073_, v_k_4074_, v___x_4075_, v_a_4076_, v_x_4077_, v_xs_4078_, v_body_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec_ref(v_a_4076_);
lean_dec(v___x_4073_);
lean_dec(v___x_4067_);
lean_dec(v___x_4066_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_4093_, lean_object* v_F_4094_, lean_object* v_val_4095_, lean_object* v_k_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4114_; uint8_t v___x_4206_; 
v___x_4206_ = l_Lean_Expr_isFVar(v_x_4093_);
if (v___x_4206_ == 0)
{
v___y_4114_ = v___x_4206_;
goto v___jp_4113_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v___x_4207_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4208_ = lean_unsigned_to_nat(5u);
v___x_4209_ = l_Lean_Expr_isAppOfArity(v_val_4095_, v___x_4207_, v___x_4208_);
v___y_4114_ = v___x_4209_;
goto v___jp_4113_;
}
v___jp_4104_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4112_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4111_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
return v___x_4112_;
}
v___jp_4113_:
{
if (v___y_4114_ == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref(v_x_4093_);
v___x_4115_ = lean_apply_9(v_k_4096_, v_F_4094_, v_val_4095_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
return v___x_4115_;
}
else
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4116_ = lean_unsigned_to_nat(3u);
v___x_4117_ = l_Lean_Expr_getAppNumArgs(v_val_4095_);
v___x_4118_ = lean_nat_sub(v___x_4117_, v___x_4116_);
v___x_4119_ = lean_unsigned_to_nat(1u);
v___x_4120_ = lean_nat_sub(v___x_4118_, v___x_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = l_Lean_Expr_getRevArg_x21(v_val_4095_, v___x_4120_);
v___x_4122_ = lean_expr_eqv(v___x_4121_, v_x_4093_);
lean_dec_ref(v___x_4121_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; 
lean_dec(v___x_4117_);
lean_dec_ref(v_x_4093_);
v___x_4123_ = lean_apply_9(v_k_4096_, v_F_4094_, v_val_4095_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
return v___x_4123_;
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4124_ = lean_unsigned_to_nat(4u);
v___x_4125_ = lean_nat_sub(v___x_4117_, v___x_4124_);
v___x_4126_ = lean_nat_sub(v___x_4125_, v___x_4119_);
lean_dec(v___x_4125_);
v___x_4127_ = l_Lean_Expr_getRevArg_x21(v_val_4095_, v___x_4126_);
v___x_4128_ = l_Lean_Expr_isLambda(v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; 
lean_dec_ref(v___x_4127_);
lean_dec(v___x_4117_);
lean_dec_ref(v_x_4093_);
v___x_4129_ = lean_apply_9(v_k_4096_, v_F_4094_, v_val_4095_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
return v___x_4129_;
}
else
{
lean_object* v___x_4130_; uint8_t v___x_4131_; 
v___x_4130_ = l_Lean_Expr_bindingBody_x21(v___x_4127_);
lean_dec_ref(v___x_4127_);
v___x_4131_ = l_Lean_Expr_isLambda(v___x_4130_);
lean_dec_ref(v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
lean_dec(v___x_4117_);
lean_dec_ref(v_x_4093_);
v___x_4132_ = lean_apply_9(v_k_4096_, v_F_4094_, v_val_4095_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
return v___x_4132_;
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = l_Lean_Expr_getAppFn(v_val_4095_);
v___x_4134_ = l_Lean_Expr_constLevels_x21(v___x_4133_);
lean_dec_ref(v___x_4133_);
if (lean_obj_tag(v___x_4134_) == 1)
{
lean_object* v_tail_4135_; 
v_tail_4135_ = lean_ctor_get(v___x_4134_, 1);
lean_inc(v_tail_4135_);
lean_dec_ref(v___x_4134_);
if (lean_obj_tag(v_tail_4135_) == 1)
{
lean_object* v_tail_4136_; 
v_tail_4136_ = lean_ctor_get(v_tail_4135_, 1);
lean_inc(v_tail_4136_);
if (lean_obj_tag(v_tail_4136_) == 1)
{
lean_object* v_tail_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4204_; 
v_tail_4137_ = lean_ctor_get(v_tail_4136_, 1);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_tail_4136_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v_tail_4136_, 0);
lean_dec(v_unused_4205_);
v___x_4139_ = v_tail_4136_;
v_isShared_4140_ = v_isSharedCheck_4204_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_tail_4137_);
lean_dec(v_tail_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4204_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
if (lean_obj_tag(v_tail_4137_) == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = l_Lean_Expr_fvarId_x21(v_F_4094_);
lean_inc_ref(v_a_4099_);
v___x_4142_ = l_Lean_FVarId_getDecl___redArg(v___x_4141_, v_a_4099_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v_dummy_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v_args_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v_00_u03b1_4150_; lean_object* v___x_4151_; lean_object* v___f_4152_; lean_object* v_00_u03b2_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v_dummy_4144_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_4117_);
v___x_4145_ = lean_mk_array(v___x_4117_, v_dummy_4144_);
v___x_4146_ = lean_nat_sub(v___x_4117_, v___x_4119_);
lean_dec(v___x_4117_);
v_args_4147_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_4095_, v___x_4145_, v___x_4146_);
v___x_4148_ = l_Lean_instInhabitedExpr;
v___x_4149_ = lean_unsigned_to_nat(0u);
v_00_u03b1_4150_ = lean_array_get(v___x_4148_, v_args_4147_, v___x_4149_);
v___x_4151_ = lean_box(v___x_4128_);
lean_inc_ref(v_x_4093_);
lean_inc(v_a_4143_);
v___f_4152_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4152_, 0, v_a_4143_);
lean_closure_set(v___f_4152_, 1, v___x_4148_);
lean_closure_set(v___f_4152_, 2, v___x_4149_);
lean_closure_set(v___f_4152_, 3, v_x_4093_);
lean_closure_set(v___f_4152_, 4, v___x_4151_);
v_00_u03b2_4153_ = lean_array_get(v___x_4148_, v_args_4147_, v___x_4119_);
v___x_4154_ = lean_unsigned_to_nat(2u);
v___x_4155_ = lean_array_get(v___x_4148_, v_args_4147_, v___x_4154_);
v___x_4156_ = 0;
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
lean_inc(v_a_4100_);
lean_inc_ref(v_a_4099_);
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
v___x_4157_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4155_, v___f_4152_, v___x_4156_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v_fst_4159_; lean_object* v_snd_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
v_fst_4159_ = lean_ctor_get(v_a_4158_, 0);
lean_inc(v_fst_4159_);
v_snd_4160_ = lean_ctor_get(v_a_4158_, 1);
lean_inc(v_snd_4160_);
lean_dec(v_a_4158_);
v___x_4161_ = lean_box(v___x_4156_);
v___x_4162_ = lean_box(v___x_4128_);
lean_inc_ref(v_x_4093_);
lean_inc(v_00_u03b2_4153_);
lean_inc(v_00_u03b1_4150_);
v___f_4163_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4163_, 0, v___x_4148_);
lean_closure_set(v___f_4163_, 1, v___x_4149_);
lean_closure_set(v___f_4163_, 2, v___x_4119_);
lean_closure_set(v___f_4163_, 3, v___x_4154_);
lean_closure_set(v___f_4163_, 4, v___x_4161_);
lean_closure_set(v___f_4163_, 5, v___x_4162_);
lean_closure_set(v___f_4163_, 6, v_00_u03b1_4150_);
lean_closure_set(v___f_4163_, 7, v_00_u03b2_4153_);
lean_closure_set(v___f_4163_, 8, v___x_4124_);
lean_closure_set(v___f_4163_, 9, v_k_4096_);
lean_closure_set(v___f_4163_, 10, v___x_4116_);
lean_closure_set(v___f_4163_, 11, v_a_4143_);
lean_closure_set(v___f_4163_, 12, v_x_4093_);
v___x_4164_ = lean_array_get(v___x_4148_, v_args_4147_, v___x_4124_);
lean_dec_ref(v_args_4147_);
v___x_4165_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4164_, v___f_4163_, v___x_4156_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4187_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4187_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4187_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4170_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 1, v_tail_4135_);
lean_ctor_set(v___x_4139_, 0, v_snd_4160_);
v___x_4172_ = v___x_4139_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_snd_4160_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v_tail_4135_);
v___x_4172_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4173_ = l_Lean_mkConst(v___x_4170_, v___x_4172_);
v___x_4174_ = lean_unsigned_to_nat(6u);
v___x_4175_ = lean_mk_empty_array_with_capacity(v___x_4174_);
v___x_4176_ = lean_array_push(v___x_4175_, v_00_u03b1_4150_);
v___x_4177_ = lean_array_push(v___x_4176_, v_00_u03b2_4153_);
v___x_4178_ = lean_array_push(v___x_4177_, v_fst_4159_);
v___x_4179_ = lean_array_push(v___x_4178_, v_x_4093_);
v___x_4180_ = lean_array_push(v___x_4179_, v_a_4166_);
v___x_4181_ = lean_array_push(v___x_4180_, v_F_4094_);
v___x_4182_ = l_Lean_mkAppN(v___x_4173_, v___x_4181_);
lean_dec_ref(v___x_4181_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4182_);
v___x_4184_ = v___x_4168_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
lean_dec(v_snd_4160_);
lean_dec(v_fst_4159_);
lean_dec(v_00_u03b2_4153_);
lean_dec(v_00_u03b1_4150_);
lean_del_object(v___x_4139_);
lean_dec_ref(v_tail_4135_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
return v___x_4165_;
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec(v_00_u03b2_4153_);
lean_dec(v_00_u03b1_4150_);
lean_dec_ref(v_args_4147_);
lean_dec(v_a_4143_);
lean_del_object(v___x_4139_);
lean_dec_ref(v_tail_4135_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v_a_4188_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4157_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4157_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
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
lean_del_object(v___x_4139_);
lean_dec_ref(v_tail_4135_);
lean_dec(v___x_4117_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_val_4095_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v_a_4196_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4142_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4142_);
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
else
{
lean_del_object(v___x_4139_);
lean_dec(v_tail_4137_);
lean_dec_ref(v_tail_4135_);
lean_dec(v___x_4117_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_val_4095_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v___y_4105_ = v_a_4097_;
v___y_4106_ = v_a_4098_;
v___y_4107_ = v_a_4099_;
v___y_4108_ = v_a_4100_;
v___y_4109_ = v_a_4101_;
v___y_4110_ = v_a_4102_;
goto v___jp_4104_;
}
}
}
else
{
lean_dec_ref(v_tail_4135_);
lean_dec(v_tail_4136_);
lean_dec(v___x_4117_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_val_4095_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v___y_4105_ = v_a_4097_;
v___y_4106_ = v_a_4098_;
v___y_4107_ = v_a_4099_;
v___y_4108_ = v_a_4100_;
v___y_4109_ = v_a_4101_;
v___y_4110_ = v_a_4102_;
goto v___jp_4104_;
}
}
else
{
lean_dec(v_tail_4135_);
lean_dec(v___x_4117_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_val_4095_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v___y_4105_ = v_a_4097_;
v___y_4106_ = v_a_4098_;
v___y_4107_ = v_a_4099_;
v___y_4108_ = v_a_4100_;
v___y_4109_ = v_a_4101_;
v___y_4110_ = v_a_4102_;
goto v___jp_4104_;
}
}
else
{
lean_dec(v___x_4134_);
lean_dec(v___x_4117_);
lean_dec_ref(v_k_4096_);
lean_dec_ref(v_val_4095_);
lean_dec_ref(v_F_4094_);
lean_dec_ref(v_x_4093_);
v___y_4105_ = v_a_4097_;
v___y_4106_ = v_a_4098_;
v___y_4107_ = v_a_4099_;
v___y_4108_ = v_a_4100_;
v___y_4109_ = v_a_4101_;
v___y_4110_ = v_a_4102_;
goto v___jp_4104_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4210_, lean_object* v_a_4211_, lean_object* v_k_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, uint8_t v___x_4215_, uint8_t v___x_4216_, uint8_t v___x_4217_, lean_object* v_FNew_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; 
lean_inc(v___y_4224_);
lean_inc_ref(v___y_4223_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc_ref(v_FNew_4218_);
lean_inc_ref(v___x_4210_);
v___x_4226_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4210_, v_FNew_4218_, v_a_4211_, v_k_4212_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = lean_mk_empty_array_with_capacity(v___x_4213_);
v___x_4229_ = lean_array_push(v___x_4228_, v___x_4214_);
v___x_4230_ = lean_array_push(v___x_4229_, v___x_4210_);
v___x_4231_ = lean_array_push(v___x_4230_, v_FNew_4218_);
v___x_4232_ = l_Lean_Meta_mkLambdaFVars(v___x_4231_, v_a_4227_, v___x_4215_, v___x_4216_, v___x_4215_, v___x_4216_, v___x_4217_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v___x_4231_);
return v___x_4232_;
}
else
{
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v_FNew_4218_);
lean_dec_ref(v___x_4214_);
lean_dec_ref(v___x_4210_);
return v___x_4226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4233_, lean_object* v_F_4234_, lean_object* v_val_4235_, lean_object* v_k_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4233_, v_F_4234_, v_val_4235_, v_k_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
v___x_4258_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_ref_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref(v___x_4258_);
v_ref_4259_ = lean_ctor_get(v___y_4255_, 5);
v___x_4260_ = 0;
v___x_4261_ = l_Lean_SourceInfo_fromRef(v_ref_4259_, v___x_4260_);
v___x_4262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4261_);
v___x_4264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4261_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = l_Lean_Syntax_node1(v___x_4261_, v___x_4262_, v___x_4264_);
v___x_4266_ = l_Lean_Elab_Tactic_evalTactic(v___x_4265_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4266_;
}
else
{
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v___x_4258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v___f_4286_; lean_object* v___x_4287_; 
v___f_4286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
lean_inc(v_a_4282_);
lean_inc_ref(v_a_4281_);
v___x_4287_ = l_Lean_Elab_Tactic_run(v_mvarId_4278_, v___f_4286_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4298_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4298_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4298_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
uint8_t v___x_4292_; 
v___x_4292_ = l_List_isEmpty___redArg(v_a_4288_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_del_object(v___x_4290_);
v___x_4293_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4288_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; lean_object* v___x_4296_; 
lean_dec(v_a_4288_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
v___x_4294_ = lean_box(0);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4294_);
v___x_4296_ = v___x_4290_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
v_a_4299_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4287_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4287_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4316_, lean_object* v_x_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_){
_start:
{
lean_object* v_ks_4320_; lean_object* v_vs_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4345_; 
v_ks_4320_ = lean_ctor_get(v_x_4316_, 0);
v_vs_4321_ = lean_ctor_get(v_x_4316_, 1);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_x_4316_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4323_ = v_x_4316_;
v_isShared_4324_ = v_isSharedCheck_4345_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_vs_4321_);
lean_inc(v_ks_4320_);
lean_dec(v_x_4316_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4345_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_array_get_size(v_ks_4320_);
v___x_4326_ = lean_nat_dec_lt(v_x_4317_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
lean_dec(v_x_4317_);
v___x_4327_ = lean_array_push(v_ks_4320_, v_x_4318_);
v___x_4328_ = lean_array_push(v_vs_4321_, v_x_4319_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 1, v___x_4328_);
lean_ctor_set(v___x_4323_, 0, v___x_4327_);
v___x_4330_ = v___x_4323_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
else
{
lean_object* v_k_x27_4332_; uint8_t v___x_4333_; 
v_k_x27_4332_ = lean_array_fget_borrowed(v_ks_4320_, v_x_4317_);
v___x_4333_ = l_Lean_instBEqMVarId_beq(v_x_4318_, v_k_x27_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4335_; 
if (v_isShared_4324_ == 0)
{
v___x_4335_ = v___x_4323_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_ks_4320_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_vs_4321_);
v___x_4335_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_unsigned_to_nat(1u);
v___x_4337_ = lean_nat_add(v_x_4317_, v___x_4336_);
lean_dec(v_x_4317_);
v_x_4316_ = v___x_4335_;
v_x_4317_ = v___x_4337_;
goto _start;
}
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4340_ = lean_array_fset(v_ks_4320_, v_x_4317_, v_x_4318_);
v___x_4341_ = lean_array_fset(v_vs_4321_, v_x_4317_, v_x_4319_);
lean_dec(v_x_4317_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 1, v___x_4341_);
lean_ctor_set(v___x_4323_, 0, v___x_4340_);
v___x_4343_ = v___x_4323_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4346_, lean_object* v_k_4347_, lean_object* v_v_4348_){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = lean_unsigned_to_nat(0u);
v___x_4350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4346_, v___x_4349_, v_k_4347_, v_v_4348_);
return v___x_4350_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4351_; size_t v___x_4352_; size_t v___x_4353_; 
v___x_4351_ = ((size_t)5ULL);
v___x_4352_ = ((size_t)1ULL);
v___x_4353_ = lean_usize_shift_left(v___x_4352_, v___x_4351_);
return v___x_4353_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4354_; size_t v___x_4355_; size_t v___x_4356_; 
v___x_4354_ = ((size_t)1ULL);
v___x_4355_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4356_ = lean_usize_sub(v___x_4355_, v___x_4354_);
return v___x_4356_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4358_, size_t v_x_4359_, size_t v_x_4360_, lean_object* v_x_4361_, lean_object* v_x_4362_){
_start:
{
if (lean_obj_tag(v_x_4358_) == 0)
{
lean_object* v_es_4363_; size_t v___x_4364_; size_t v___x_4365_; size_t v___x_4366_; size_t v___x_4367_; lean_object* v_j_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v_es_4363_ = lean_ctor_get(v_x_4358_, 0);
v___x_4364_ = ((size_t)5ULL);
v___x_4365_ = ((size_t)1ULL);
v___x_4366_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4367_ = lean_usize_land(v_x_4359_, v___x_4366_);
v_j_4368_ = lean_usize_to_nat(v___x_4367_);
v___x_4369_ = lean_array_get_size(v_es_4363_);
v___x_4370_ = lean_nat_dec_lt(v_j_4368_, v___x_4369_);
if (v___x_4370_ == 0)
{
lean_dec(v_j_4368_);
lean_dec(v_x_4362_);
lean_dec(v_x_4361_);
return v_x_4358_;
}
else
{
lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4407_; 
lean_inc_ref(v_es_4363_);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_x_4358_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; 
v_unused_4408_ = lean_ctor_get(v_x_4358_, 0);
lean_dec(v_unused_4408_);
v___x_4372_ = v_x_4358_;
v_isShared_4373_ = v_isSharedCheck_4407_;
goto v_resetjp_4371_;
}
else
{
lean_dec(v_x_4358_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4407_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v_v_4374_; lean_object* v___x_4375_; lean_object* v_xs_x27_4376_; lean_object* v___y_4378_; 
v_v_4374_ = lean_array_fget(v_es_4363_, v_j_4368_);
v___x_4375_ = lean_box(0);
v_xs_x27_4376_ = lean_array_fset(v_es_4363_, v_j_4368_, v___x_4375_);
switch(lean_obj_tag(v_v_4374_))
{
case 0:
{
lean_object* v_key_4383_; lean_object* v_val_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4394_; 
v_key_4383_ = lean_ctor_get(v_v_4374_, 0);
v_val_4384_ = lean_ctor_get(v_v_4374_, 1);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_v_4374_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4386_ = v_v_4374_;
v_isShared_4387_ = v_isSharedCheck_4394_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_val_4384_);
lean_inc(v_key_4383_);
lean_dec(v_v_4374_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4394_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
uint8_t v___x_4388_; 
v___x_4388_ = l_Lean_instBEqMVarId_beq(v_x_4361_, v_key_4383_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
lean_del_object(v___x_4386_);
v___x_4389_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4383_, v_val_4384_, v_x_4361_, v_x_4362_);
v___x_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
v___y_4378_ = v___x_4390_;
goto v___jp_4377_;
}
else
{
lean_object* v___x_4392_; 
lean_dec(v_val_4384_);
lean_dec(v_key_4383_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 1, v_x_4362_);
lean_ctor_set(v___x_4386_, 0, v_x_4361_);
v___x_4392_ = v___x_4386_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_x_4361_);
lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_x_4362_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
v___y_4378_ = v___x_4392_;
goto v___jp_4377_;
}
}
}
}
case 1:
{
lean_object* v_node_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4405_; 
v_node_4395_ = lean_ctor_get(v_v_4374_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_v_4374_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4397_ = v_v_4374_;
v_isShared_4398_ = v_isSharedCheck_4405_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_node_4395_);
lean_dec(v_v_4374_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4405_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
size_t v___x_4399_; size_t v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4399_ = lean_usize_shift_right(v_x_4359_, v___x_4364_);
v___x_4400_ = lean_usize_add(v_x_4360_, v___x_4365_);
v___x_4401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4395_, v___x_4399_, v___x_4400_, v_x_4361_, v_x_4362_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4401_);
v___x_4403_ = v___x_4397_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
v___y_4378_ = v___x_4403_;
goto v___jp_4377_;
}
}
}
default: 
{
lean_object* v___x_4406_; 
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v_x_4361_);
lean_ctor_set(v___x_4406_, 1, v_x_4362_);
v___y_4378_ = v___x_4406_;
goto v___jp_4377_;
}
}
v___jp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_array_fset(v_xs_x27_4376_, v_j_4368_, v___y_4378_);
lean_dec(v_j_4368_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4379_);
v___x_4381_ = v___x_4372_;
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
}
else
{
lean_object* v_ks_4409_; lean_object* v_vs_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4430_; 
v_ks_4409_ = lean_ctor_get(v_x_4358_, 0);
v_vs_4410_ = lean_ctor_get(v_x_4358_, 1);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_x_4358_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4412_ = v_x_4358_;
v_isShared_4413_ = v_isSharedCheck_4430_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_vs_4410_);
lean_inc(v_ks_4409_);
lean_dec(v_x_4358_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4430_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_ks_4409_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_vs_4410_);
v___x_4415_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v_newNode_4416_; uint8_t v___y_4418_; size_t v___x_4424_; uint8_t v___x_4425_; 
v_newNode_4416_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4415_, v_x_4361_, v_x_4362_);
v___x_4424_ = ((size_t)7ULL);
v___x_4425_ = lean_usize_dec_le(v___x_4424_, v_x_4360_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4426_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4416_);
v___x_4427_ = lean_unsigned_to_nat(4u);
v___x_4428_ = lean_nat_dec_lt(v___x_4426_, v___x_4427_);
lean_dec(v___x_4426_);
v___y_4418_ = v___x_4428_;
goto v___jp_4417_;
}
else
{
v___y_4418_ = v___x_4425_;
goto v___jp_4417_;
}
v___jp_4417_:
{
if (v___y_4418_ == 0)
{
lean_object* v_ks_4419_; lean_object* v_vs_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_ks_4419_ = lean_ctor_get(v_newNode_4416_, 0);
lean_inc_ref(v_ks_4419_);
v_vs_4420_ = lean_ctor_get(v_newNode_4416_, 1);
lean_inc_ref(v_vs_4420_);
lean_dec_ref(v_newNode_4416_);
v___x_4421_ = lean_unsigned_to_nat(0u);
v___x_4422_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_4423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4360_, v_ks_4419_, v_vs_4420_, v___x_4421_, v___x_4422_);
lean_dec_ref(v_vs_4420_);
lean_dec_ref(v_ks_4419_);
return v___x_4423_;
}
else
{
return v_newNode_4416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4431_, lean_object* v_keys_4432_, lean_object* v_vals_4433_, lean_object* v_i_4434_, lean_object* v_entries_4435_){
_start:
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = lean_array_get_size(v_keys_4432_);
v___x_4437_ = lean_nat_dec_lt(v_i_4434_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_dec(v_i_4434_);
return v_entries_4435_;
}
else
{
lean_object* v_k_4438_; lean_object* v_v_4439_; uint64_t v___x_4440_; size_t v_h_4441_; size_t v___x_4442_; lean_object* v___x_4443_; size_t v___x_4444_; size_t v___x_4445_; size_t v___x_4446_; size_t v_h_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_k_4438_ = lean_array_fget_borrowed(v_keys_4432_, v_i_4434_);
v_v_4439_ = lean_array_fget_borrowed(v_vals_4433_, v_i_4434_);
v___x_4440_ = l_Lean_instHashableMVarId_hash(v_k_4438_);
v_h_4441_ = lean_uint64_to_usize(v___x_4440_);
v___x_4442_ = ((size_t)5ULL);
v___x_4443_ = lean_unsigned_to_nat(1u);
v___x_4444_ = ((size_t)1ULL);
v___x_4445_ = lean_usize_sub(v_depth_4431_, v___x_4444_);
v___x_4446_ = lean_usize_mul(v___x_4442_, v___x_4445_);
v_h_4447_ = lean_usize_shift_right(v_h_4441_, v___x_4446_);
v___x_4448_ = lean_nat_add(v_i_4434_, v___x_4443_);
lean_dec(v_i_4434_);
lean_inc(v_v_4439_);
lean_inc(v_k_4438_);
v___x_4449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4435_, v_h_4447_, v_depth_4431_, v_k_4438_, v_v_4439_);
v_i_4434_ = v___x_4448_;
v_entries_4435_ = v___x_4449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4451_, lean_object* v_keys_4452_, lean_object* v_vals_4453_, lean_object* v_i_4454_, lean_object* v_entries_4455_){
_start:
{
size_t v_depth_boxed_4456_; lean_object* v_res_4457_; 
v_depth_boxed_4456_ = lean_unbox_usize(v_depth_4451_);
lean_dec(v_depth_4451_);
v_res_4457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4456_, v_keys_4452_, v_vals_4453_, v_i_4454_, v_entries_4455_);
lean_dec_ref(v_vals_4453_);
lean_dec_ref(v_keys_4452_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4458_, lean_object* v_x_4459_, lean_object* v_x_4460_, lean_object* v_x_4461_, lean_object* v_x_4462_){
_start:
{
size_t v_x_4354__boxed_4463_; size_t v_x_4355__boxed_4464_; lean_object* v_res_4465_; 
v_x_4354__boxed_4463_ = lean_unbox_usize(v_x_4459_);
lean_dec(v_x_4459_);
v_x_4355__boxed_4464_ = lean_unbox_usize(v_x_4460_);
lean_dec(v_x_4460_);
v_res_4465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4458_, v_x_4354__boxed_4463_, v_x_4355__boxed_4464_, v_x_4461_, v_x_4462_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4466_, lean_object* v_x_4467_, lean_object* v_x_4468_){
_start:
{
uint64_t v___x_4469_; size_t v___x_4470_; size_t v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = l_Lean_instHashableMVarId_hash(v_x_4467_);
v___x_4470_ = lean_uint64_to_usize(v___x_4469_);
v___x_4471_ = ((size_t)1ULL);
v___x_4472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4466_, v___x_4470_, v___x_4471_, v_x_4467_, v_x_4468_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4473_, lean_object* v_val_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v___x_4477_; lean_object* v_mctx_4478_; lean_object* v_cache_4479_; lean_object* v_zetaDeltaFVarIds_4480_; lean_object* v_postponed_4481_; lean_object* v_diag_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4509_; 
v___x_4477_ = lean_st_ref_take(v___y_4475_);
v_mctx_4478_ = lean_ctor_get(v___x_4477_, 0);
v_cache_4479_ = lean_ctor_get(v___x_4477_, 1);
v_zetaDeltaFVarIds_4480_ = lean_ctor_get(v___x_4477_, 2);
v_postponed_4481_ = lean_ctor_get(v___x_4477_, 3);
v_diag_4482_ = lean_ctor_get(v___x_4477_, 4);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4484_ = v___x_4477_;
v_isShared_4485_ = v_isSharedCheck_4509_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_diag_4482_);
lean_inc(v_postponed_4481_);
lean_inc(v_zetaDeltaFVarIds_4480_);
lean_inc(v_cache_4479_);
lean_inc(v_mctx_4478_);
lean_dec(v___x_4477_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4509_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_depth_4486_; lean_object* v_levelAssignDepth_4487_; lean_object* v_mvarCounter_4488_; lean_object* v_lDepth_4489_; lean_object* v_decls_4490_; lean_object* v_userNames_4491_; lean_object* v_lAssignment_4492_; lean_object* v_eAssignment_4493_; lean_object* v_dAssignment_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4508_; 
v_depth_4486_ = lean_ctor_get(v_mctx_4478_, 0);
v_levelAssignDepth_4487_ = lean_ctor_get(v_mctx_4478_, 1);
v_mvarCounter_4488_ = lean_ctor_get(v_mctx_4478_, 2);
v_lDepth_4489_ = lean_ctor_get(v_mctx_4478_, 3);
v_decls_4490_ = lean_ctor_get(v_mctx_4478_, 4);
v_userNames_4491_ = lean_ctor_get(v_mctx_4478_, 5);
v_lAssignment_4492_ = lean_ctor_get(v_mctx_4478_, 6);
v_eAssignment_4493_ = lean_ctor_get(v_mctx_4478_, 7);
v_dAssignment_4494_ = lean_ctor_get(v_mctx_4478_, 8);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_mctx_4478_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4496_ = v_mctx_4478_;
v_isShared_4497_ = v_isSharedCheck_4508_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_dAssignment_4494_);
lean_inc(v_eAssignment_4493_);
lean_inc(v_lAssignment_4492_);
lean_inc(v_userNames_4491_);
lean_inc(v_decls_4490_);
lean_inc(v_lDepth_4489_);
lean_inc(v_mvarCounter_4488_);
lean_inc(v_levelAssignDepth_4487_);
lean_inc(v_depth_4486_);
lean_dec(v_mctx_4478_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4508_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4498_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4493_, v_mvarId_4473_, v_val_4474_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 7, v___x_4498_);
v___x_4500_ = v___x_4496_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_depth_4486_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_levelAssignDepth_4487_);
lean_ctor_set(v_reuseFailAlloc_4507_, 2, v_mvarCounter_4488_);
lean_ctor_set(v_reuseFailAlloc_4507_, 3, v_lDepth_4489_);
lean_ctor_set(v_reuseFailAlloc_4507_, 4, v_decls_4490_);
lean_ctor_set(v_reuseFailAlloc_4507_, 5, v_userNames_4491_);
lean_ctor_set(v_reuseFailAlloc_4507_, 6, v_lAssignment_4492_);
lean_ctor_set(v_reuseFailAlloc_4507_, 7, v___x_4498_);
lean_ctor_set(v_reuseFailAlloc_4507_, 8, v_dAssignment_4494_);
v___x_4500_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4500_);
v___x_4502_ = v___x_4484_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_cache_4479_);
lean_ctor_set(v_reuseFailAlloc_4506_, 2, v_zetaDeltaFVarIds_4480_);
lean_ctor_set(v_reuseFailAlloc_4506_, 3, v_postponed_4481_);
lean_ctor_set(v_reuseFailAlloc_4506_, 4, v_diag_4482_);
v___x_4502_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4503_ = lean_st_ref_set(v___y_4475_, v___x_4502_);
v___x_4504_ = lean_box(0);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
return v___x_4505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4510_, lean_object* v_val_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4510_, v_val_4511_, v___y_4512_);
lean_dec(v___y_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4519_, lean_object* v_mv_u2082_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v___x_4529_; 
lean_inc(v_mv_u2081_4519_);
v___x_4529_ = l_Lean_MVarId_getDecl(v_mv_u2081_4519_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref(v___x_4529_);
lean_inc(v_mv_u2082_4520_);
v___x_4531_ = l_Lean_MVarId_getDecl(v_mv_u2082_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v_lctx_4533_; lean_object* v_type_4534_; lean_object* v_lctx_4535_; lean_object* v_type_4536_; uint8_t v___x_4537_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref(v___x_4531_);
v_lctx_4533_ = lean_ctor_get(v_a_4530_, 1);
lean_inc_ref(v_lctx_4533_);
v_type_4534_ = lean_ctor_get(v_a_4530_, 2);
lean_inc_ref(v_type_4534_);
lean_dec(v_a_4530_);
v_lctx_4535_ = lean_ctor_get(v_a_4532_, 1);
lean_inc_ref(v_lctx_4535_);
v_type_4536_ = lean_ctor_get(v_a_4532_, 2);
lean_inc_ref(v_type_4536_);
lean_dec(v_a_4532_);
v___x_4537_ = lean_expr_eqv(v_type_4534_, v_type_4536_);
lean_dec_ref(v_type_4536_);
lean_dec_ref(v_type_4534_);
if (v___x_4537_ == 0)
{
lean_dec_ref(v_lctx_4535_);
lean_dec_ref(v_lctx_4533_);
lean_dec(v_mv_u2082_4520_);
lean_dec(v_mv_u2081_4519_);
goto v___jp_4526_;
}
else
{
lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4538_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc_ref(v_lctx_4535_);
lean_inc_ref(v_lctx_4533_);
v___x_4539_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4533_, v_lctx_4535_, v___x_4538_);
if (v___x_4539_ == 0)
{
uint8_t v___x_4540_; 
v___x_4540_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4535_, v_lctx_4533_, v___x_4538_);
if (v___x_4540_ == 0)
{
lean_dec(v_mv_u2082_4520_);
lean_dec(v_mv_u2081_4519_);
goto v___jp_4526_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4552_; 
v___x_4541_ = l_Lean_Expr_mvar___override(v_mv_u2082_4520_);
v___x_4542_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4519_, v___x_4541_, v___y_4522_);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; 
v_unused_4553_ = lean_ctor_get(v___x_4542_, 0);
lean_dec(v_unused_4553_);
v___x_4544_ = v___x_4542_;
v_isShared_4545_ = v_isSharedCheck_4552_;
goto v_resetjp_4543_;
}
else
{
lean_dec(v___x_4542_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4552_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4546_ = lean_box(v___x_4539_);
v___x_4547_ = lean_box(v___x_4537_);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v___x_4548_);
v___x_4550_ = v___x_4544_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4566_; 
lean_dec_ref(v_lctx_4535_);
lean_dec_ref(v_lctx_4533_);
v___x_4554_ = l_Lean_Expr_mvar___override(v_mv_u2081_4519_);
v___x_4555_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4520_, v___x_4554_, v___y_4522_);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v___x_4555_, 0);
lean_dec(v_unused_4567_);
v___x_4557_ = v___x_4555_;
v_isShared_4558_ = v_isSharedCheck_4566_;
goto v_resetjp_4556_;
}
else
{
lean_dec(v___x_4555_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4566_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4559_ = 0;
v___x_4560_ = lean_box(v___x_4537_);
v___x_4561_ = lean_box(v___x_4559_);
v___x_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 0, v___x_4562_);
v___x_4564_ = v___x_4557_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4562_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec(v_a_4530_);
lean_dec(v_mv_u2082_4520_);
lean_dec(v_mv_u2081_4519_);
v_a_4568_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4531_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4531_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec(v_mv_u2082_4520_);
lean_dec(v_mv_u2081_4519_);
v_a_4576_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4529_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4529_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
v___jp_4526_:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4584_, lean_object* v_mv_u2082_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4584_, v_mv_u2082_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4592_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4606_, lean_object* v_removed_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___y_4617_; uint8_t v___x_4640_; 
v___x_4640_ = lean_nat_dec_lt(v_a_4609_, v_upperBound_4606_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; 
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v_a_4609_);
v___x_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4641_, 0, v_b_4610_);
return v___x_4641_;
}
else
{
uint8_t v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4642_ = 0;
v___x_4643_ = lean_box(v___x_4642_);
v___x_4644_ = lean_array_get_borrowed(v___x_4643_, v_removed_4607_, v_a_4609_);
v___x_4645_ = lean_unbox(v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___f_4649_; 
v___x_4646_ = lean_array_fget_borrowed(v_a_4608_, v_a_4609_);
lean_inc(v___x_4646_);
v___x_4647_ = lean_array_push(v_b_4610_, v___x_4646_);
v___x_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
v___f_4649_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4649_, 0, v___x_4648_);
v___y_4617_ = v___f_4649_;
goto v___jp_4616_;
}
else
{
lean_object* v___x_4650_; lean_object* v___f_4651_; 
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v_b_4610_);
v___f_4651_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4651_, 0, v___x_4650_);
v___y_4617_ = v___f_4651_;
goto v___jp_4616_;
}
}
v___jp_4616_:
{
lean_object* v___x_4618_; 
lean_inc(v___y_4614_);
lean_inc_ref(v___y_4613_);
lean_inc(v___y_4612_);
lean_inc_ref(v___y_4611_);
v___x_4618_ = lean_apply_5(v___y_4617_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, lean_box(0));
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4631_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4621_ = v___x_4618_;
v_isShared_4622_ = v_isSharedCheck_4631_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4618_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4631_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
if (lean_obj_tag(v_a_4619_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; 
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v_a_4609_);
v_a_4623_ = lean_ctor_get(v_a_4619_, 0);
lean_inc(v_a_4623_);
lean_dec_ref(v_a_4619_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v_a_4623_);
v___x_4625_ = v___x_4621_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_del_object(v___x_4621_);
v_a_4627_ = lean_ctor_get(v_a_4619_, 0);
lean_inc(v_a_4627_);
lean_dec_ref(v_a_4619_);
v___x_4628_ = lean_unsigned_to_nat(1u);
v___x_4629_ = lean_nat_add(v_a_4609_, v___x_4628_);
lean_dec(v_a_4609_);
v_a_4609_ = v___x_4629_;
v_b_4610_ = v_a_4627_;
goto _start;
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v_a_4609_);
v_a_4632_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4618_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4618_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4652_, lean_object* v_removed_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_b_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4652_, v_removed_4653_, v_a_4654_, v_a_4655_, v_b_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec_ref(v_a_4654_);
lean_dec_ref(v_removed_4653_);
lean_dec(v_upperBound_4652_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4663_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4677_, lean_object* v___x_4678_, lean_object* v___x_4679_, lean_object* v___x_4680_, lean_object* v_a_4681_, uint8_t v___x_4682_, lean_object* v_snd_4683_, lean_object* v_fst_4684_, lean_object* v_next_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = lean_apply_7(v_f_4677_, v___x_4678_, v___x_4679_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, lean_box(0));
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4727_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4727_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4727_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_fst_4696_; lean_object* v_snd_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4726_; 
v_fst_4696_ = lean_ctor_get(v_a_4692_, 0);
v_snd_4697_ = lean_ctor_get(v_a_4692_, 1);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_a_4692_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4699_ = v_a_4692_;
v_isShared_4700_ = v_isSharedCheck_4726_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_snd_4697_);
lean_inc(v_fst_4696_);
lean_dec(v_a_4692_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4726_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_removed_4702_; lean_object* v_numRemoved_4703_; uint8_t v___x_4722_; 
v___x_4722_ = lean_unbox(v_fst_4696_);
lean_dec(v_fst_4696_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4723_ = lean_nat_add(v_snd_4683_, v___x_4680_);
lean_dec(v_snd_4683_);
v___x_4724_ = lean_box(v___x_4682_);
v___x_4725_ = lean_array_set(v_fst_4684_, v_next_4685_, v___x_4724_);
v_removed_4702_ = v___x_4725_;
v_numRemoved_4703_ = v___x_4723_;
goto v___jp_4701_;
}
else
{
v_removed_4702_ = v_fst_4684_;
v_numRemoved_4703_ = v_snd_4683_;
goto v___jp_4701_;
}
v___jp_4701_:
{
uint8_t v___x_4704_; 
v___x_4704_ = lean_unbox(v_snd_4697_);
lean_dec(v_snd_4697_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4709_; 
v___x_4705_ = lean_nat_add(v_numRemoved_4703_, v___x_4680_);
lean_dec(v_numRemoved_4703_);
v___x_4706_ = lean_box(v___x_4682_);
v___x_4707_ = lean_array_set(v_removed_4702_, v_a_4681_, v___x_4706_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v___x_4705_);
lean_ctor_set(v___x_4699_, 0, v___x_4707_);
v___x_4709_ = v___x_4699_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4705_);
v___x_4709_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4710_; lean_object* v___x_4712_; 
v___x_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4710_);
v___x_4712_ = v___x_4694_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
else
{
lean_object* v___x_4716_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v_numRemoved_4703_);
lean_ctor_set(v___x_4699_, 0, v_removed_4702_);
v___x_4716_ = v___x_4699_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_removed_4702_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v_numRemoved_4703_);
v___x_4716_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4717_);
v___x_4719_ = v___x_4694_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v_fst_4684_);
lean_dec(v_snd_4683_);
v_a_4728_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4691_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4691_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4736_, lean_object* v___x_4737_, lean_object* v___x_4738_, lean_object* v___x_4739_, lean_object* v_a_4740_, lean_object* v___x_4741_, lean_object* v_snd_4742_, lean_object* v_fst_4743_, lean_object* v_next_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
uint8_t v___x_4847__boxed_4750_; lean_object* v_res_4751_; 
v___x_4847__boxed_4750_ = lean_unbox(v___x_4741_);
v_res_4751_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4736_, v___x_4737_, v___x_4738_, v___x_4739_, v_a_4740_, v___x_4847__boxed_4750_, v_snd_4742_, v_fst_4743_, v_next_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
lean_dec(v_next_4744_);
lean_dec(v_a_4740_);
lean_dec(v___x_4739_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4752_, lean_object* v_a_4753_, lean_object* v_next_4754_, lean_object* v_f_4755_, lean_object* v_a_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
uint8_t v___x_4763_; 
v___x_4763_ = lean_nat_dec_lt(v_a_4756_, v_upperBound_4752_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_a_4756_);
lean_dec_ref(v_f_4755_);
lean_dec(v_next_4754_);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v_b_4757_);
return v___x_4764_;
}
else
{
lean_object* v_fst_4765_; lean_object* v_snd_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4813_; 
v_fst_4765_ = lean_ctor_get(v_b_4757_, 0);
v_snd_4766_ = lean_ctor_get(v_b_4757_, 1);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_b_4757_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4768_ = v_b_4757_;
v_isShared_4769_ = v_isSharedCheck_4813_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_snd_4766_);
lean_inc(v_fst_4765_);
lean_dec(v_b_4757_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4813_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4770_; lean_object* v___y_4772_; uint8_t v___y_4795_; uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4770_ = lean_unsigned_to_nat(1u);
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
v___x_4807_ = lean_array_get_borrowed(v___x_4806_, v_fst_4765_, v_next_4754_);
v___x_4808_ = lean_unbox(v___x_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4809_ = lean_box(v___x_4805_);
v___x_4810_ = lean_array_get_borrowed(v___x_4809_, v_fst_4765_, v_a_4756_);
v___x_4811_ = lean_unbox(v___x_4810_);
v___y_4795_ = v___x_4811_;
goto v___jp_4794_;
}
else
{
uint8_t v___x_4812_; 
v___x_4812_ = lean_unbox(v___x_4807_);
v___y_4795_ = v___x_4812_;
goto v___jp_4794_;
}
v___jp_4771_:
{
lean_object* v___x_4773_; 
lean_inc(v___y_4761_);
lean_inc_ref(v___y_4760_);
lean_inc(v___y_4759_);
lean_inc_ref(v___y_4758_);
v___x_4773_ = lean_apply_5(v___y_4772_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, lean_box(0));
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4785_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4776_ = v___x_4773_;
v_isShared_4777_ = v_isSharedCheck_4785_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4773_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4785_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
if (lean_obj_tag(v_a_4774_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_a_4756_);
lean_dec_ref(v_f_4755_);
lean_dec(v_next_4754_);
v_a_4778_ = lean_ctor_get(v_a_4774_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v_a_4774_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v_a_4778_);
v___x_4780_ = v___x_4776_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4783_; 
lean_del_object(v___x_4776_);
v_a_4782_ = lean_ctor_get(v_a_4774_, 0);
lean_inc(v_a_4782_);
lean_dec_ref(v_a_4774_);
v___x_4783_ = lean_nat_add(v_a_4756_, v___x_4770_);
lean_dec(v_a_4756_);
v_a_4756_ = v___x_4783_;
v_b_4757_ = v_a_4782_;
goto _start;
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_a_4756_);
lean_dec_ref(v_f_4755_);
lean_dec(v_next_4754_);
v_a_4786_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4773_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4773_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
v___jp_4794_:
{
if (v___y_4795_ == 0)
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___f_4799_; 
lean_del_object(v___x_4768_);
v___x_4796_ = lean_array_fget_borrowed(v_a_4753_, v_next_4754_);
v___x_4797_ = lean_array_fget_borrowed(v_a_4753_, v_a_4756_);
v___x_4798_ = lean_box(v___x_4763_);
lean_inc(v_next_4754_);
lean_inc(v_a_4756_);
lean_inc(v___x_4797_);
lean_inc(v___x_4796_);
lean_inc_ref(v_f_4755_);
v___f_4799_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4799_, 0, v_f_4755_);
lean_closure_set(v___f_4799_, 1, v___x_4796_);
lean_closure_set(v___f_4799_, 2, v___x_4797_);
lean_closure_set(v___f_4799_, 3, v___x_4770_);
lean_closure_set(v___f_4799_, 4, v_a_4756_);
lean_closure_set(v___f_4799_, 5, v___x_4798_);
lean_closure_set(v___f_4799_, 6, v_snd_4766_);
lean_closure_set(v___f_4799_, 7, v_fst_4765_);
lean_closure_set(v___f_4799_, 8, v_next_4754_);
v___y_4772_ = v___f_4799_;
goto v___jp_4771_;
}
else
{
lean_object* v___x_4801_; 
if (v_isShared_4769_ == 0)
{
v___x_4801_ = v___x_4768_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_fst_4765_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_snd_4766_);
v___x_4801_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; lean_object* v___f_4803_; 
v___x_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
v___f_4803_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4803_, 0, v___x_4802_);
v___y_4772_ = v___f_4803_;
goto v___jp_4771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4814_, lean_object* v_a_4815_, lean_object* v_next_4816_, lean_object* v_f_4817_, lean_object* v_a_4818_, lean_object* v_b_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4814_, v_a_4815_, v_next_4816_, v_f_4817_, v_a_4818_, v_b_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec_ref(v_a_4815_);
lean_dec(v_upperBound_4814_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4826_, lean_object* v___x_4827_, lean_object* v_a_4828_, lean_object* v_f_4829_, lean_object* v_a_4830_, lean_object* v_b_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
uint8_t v___x_4837_; 
v___x_4837_ = lean_nat_dec_lt(v_a_4830_, v_upperBound_4826_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v_a_4830_);
lean_dec_ref(v_f_4829_);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v_b_4831_);
return v___x_4838_;
}
else
{
lean_object* v_fst_4839_; lean_object* v_snd_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4861_; 
v_fst_4839_ = lean_ctor_get(v_b_4831_, 0);
v_snd_4840_ = lean_ctor_get(v_b_4831_, 1);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_b_4831_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4842_ = v_b_4831_;
v_isShared_4843_ = v_isSharedCheck_4861_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_snd_4840_);
lean_inc(v_fst_4839_);
lean_dec(v_b_4831_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4861_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4844_ = lean_unsigned_to_nat(1u);
v___x_4845_ = lean_nat_add(v_a_4830_, v___x_4844_);
if (v_isShared_4843_ == 0)
{
v___x_4847_ = v___x_4842_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_fst_4839_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_snd_4840_);
v___x_4847_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
lean_object* v___x_4848_; 
lean_inc(v___y_4835_);
lean_inc_ref(v___y_4834_);
lean_inc(v___y_4833_);
lean_inc_ref(v___y_4832_);
lean_inc(v___x_4845_);
lean_inc_ref(v_f_4829_);
v___x_4848_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4827_, v_a_4828_, v_a_4830_, v_f_4829_, v___x_4845_, v___x_4847_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v_fst_4850_; lean_object* v_snd_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4859_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref(v___x_4848_);
v_fst_4850_ = lean_ctor_get(v_a_4849_, 0);
v_snd_4851_ = lean_ctor_get(v_a_4849_, 1);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_a_4849_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4853_ = v_a_4849_;
v_isShared_4854_ = v_isSharedCheck_4859_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_snd_4851_);
lean_inc(v_fst_4850_);
lean_dec(v_a_4849_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4859_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_fst_4850_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_snd_4851_);
v___x_4856_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
v_a_4830_ = v___x_4845_;
v_b_4831_ = v___x_4856_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4845_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec_ref(v_f_4829_);
return v___x_4848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4862_, lean_object* v___x_4863_, lean_object* v_a_4864_, lean_object* v_f_4865_, lean_object* v_a_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4862_, v___x_4863_, v_a_4864_, v_f_4865_, v_a_4866_, v_b_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
lean_dec_ref(v_a_4864_);
lean_dec(v___x_4863_);
lean_dec(v_upperBound_4862_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4874_, lean_object* v_f_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v___x_4881_; uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v_removed_4884_; lean_object* v_numRemoved_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4881_ = lean_array_get_size(v_a_4874_);
v___x_4882_ = 0;
v___x_4883_ = lean_box(v___x_4882_);
v_removed_4884_ = lean_mk_array(v___x_4881_, v___x_4883_);
v_numRemoved_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4886_, 0, v_removed_4884_);
lean_ctor_set(v___x_4886_, 1, v_numRemoved_4885_);
lean_inc(v___y_4879_);
lean_inc_ref(v___y_4878_);
lean_inc(v___y_4877_);
lean_inc_ref(v___y_4876_);
v___x_4887_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4881_, v___x_4881_, v_a_4874_, v_f_4875_, v_numRemoved_4885_, v___x_4886_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v_fst_4889_; lean_object* v_snd_4890_; lean_object* v_a_x27_4891_; lean_object* v___x_4892_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref(v___x_4887_);
v_fst_4889_ = lean_ctor_get(v_a_4888_, 0);
lean_inc(v_fst_4889_);
v_snd_4890_ = lean_ctor_get(v_a_4888_, 1);
lean_inc(v_snd_4890_);
lean_dec(v_a_4888_);
v_a_x27_4891_ = lean_mk_empty_array_with_capacity(v_snd_4890_);
lean_dec(v_snd_4890_);
v___x_4892_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4881_, v_fst_4889_, v_a_4874_, v_numRemoved_4885_, v_a_x27_4891_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
lean_dec(v_fst_4889_);
return v___x_4892_;
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
v_a_4893_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4887_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4887_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4901_, lean_object* v_f_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4901_, v_f_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
lean_dec_ref(v_a_4901_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v___f_4916_; lean_object* v___x_4917_; 
v___f_4916_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4917_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4910_, v___f_4916_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_);
lean_dec_ref(v_mvars_4918_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4925_, lean_object* v_val_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4925_, v_val_4926_, v___y_4928_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4933_, lean_object* v_val_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4933_, v_val_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec(v___y_4936_);
lean_dec_ref(v___y_4935_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4941_, lean_object* v_a_4942_, lean_object* v_f_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4942_, v_f_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4950_, lean_object* v_a_4951_, lean_object* v_f_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4950_, v_a_4951_, v_f_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
lean_dec_ref(v_a_4951_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4959_, lean_object* v_x_4960_, lean_object* v_x_4961_, lean_object* v_x_4962_){
_start:
{
lean_object* v___x_4963_; 
v___x_4963_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4960_, v_x_4961_, v_x_4962_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4964_, lean_object* v_00_u03b1_4965_, lean_object* v_a_4966_, lean_object* v_next_4967_, lean_object* v_f_4968_, lean_object* v_inst_4969_, lean_object* v_R_4970_, lean_object* v_a_4971_, lean_object* v_b_4972_, lean_object* v_c_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4964_, v_a_4966_, v_next_4967_, v_f_4968_, v_a_4971_, v_b_4972_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4980_, lean_object* v_00_u03b1_4981_, lean_object* v_a_4982_, lean_object* v_next_4983_, lean_object* v_f_4984_, lean_object* v_inst_4985_, lean_object* v_R_4986_, lean_object* v_a_4987_, lean_object* v_b_4988_, lean_object* v_c_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4980_, v_00_u03b1_4981_, v_a_4982_, v_next_4983_, v_f_4984_, v_inst_4985_, v_R_4986_, v_a_4987_, v_b_4988_, v_c_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec_ref(v_a_4982_);
lean_dec(v_upperBound_4980_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4996_, lean_object* v_upperBound_4997_, lean_object* v_removed_4998_, lean_object* v_a_4999_, lean_object* v_inst_5000_, lean_object* v_R_5001_, lean_object* v_a_5002_, lean_object* v_b_5003_, lean_object* v_c_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v___x_5010_; 
v___x_5010_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4997_, v_removed_4998_, v_a_4999_, v_a_5002_, v_b_5003_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_5011_, lean_object* v_upperBound_5012_, lean_object* v_removed_5013_, lean_object* v_a_5014_, lean_object* v_inst_5015_, lean_object* v_R_5016_, lean_object* v_a_5017_, lean_object* v_b_5018_, lean_object* v_c_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_5011_, v_upperBound_5012_, v_removed_5013_, v_a_5014_, v_inst_5015_, v_R_5016_, v_a_5017_, v_b_5018_, v_c_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec_ref(v_a_5014_);
lean_dec_ref(v_removed_5013_);
lean_dec(v_upperBound_5012_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_5026_, lean_object* v___x_5027_, lean_object* v_00_u03b1_5028_, lean_object* v_a_5029_, lean_object* v_f_5030_, lean_object* v_inst_5031_, lean_object* v_R_5032_, lean_object* v_a_5033_, lean_object* v_b_5034_, lean_object* v_c_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
lean_object* v___x_5041_; 
v___x_5041_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_5026_, v___x_5027_, v_a_5029_, v_f_5030_, v_a_5033_, v_b_5034_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_5042_, lean_object* v___x_5043_, lean_object* v_00_u03b1_5044_, lean_object* v_a_5045_, lean_object* v_f_5046_, lean_object* v_inst_5047_, lean_object* v_R_5048_, lean_object* v_a_5049_, lean_object* v_b_5050_, lean_object* v_c_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_5042_, v___x_5043_, v_00_u03b1_5044_, v_a_5045_, v_f_5046_, v_inst_5047_, v_R_5048_, v_a_5049_, v_b_5050_, v_c_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec_ref(v_a_5045_);
lean_dec(v___x_5043_);
lean_dec(v_upperBound_5042_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5058_, lean_object* v_x_5059_, size_t v_x_5060_, size_t v_x_5061_, lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_5059_, v_x_5060_, v_x_5061_, v_x_5062_, v_x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5065_, lean_object* v_x_5066_, lean_object* v_x_5067_, lean_object* v_x_5068_, lean_object* v_x_5069_, lean_object* v_x_5070_){
_start:
{
size_t v_x_5319__boxed_5071_; size_t v_x_5320__boxed_5072_; lean_object* v_res_5073_; 
v_x_5319__boxed_5071_ = lean_unbox_usize(v_x_5067_);
lean_dec(v_x_5067_);
v_x_5320__boxed_5072_ = lean_unbox_usize(v_x_5068_);
lean_dec(v_x_5068_);
v_res_5073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_5065_, v_x_5066_, v_x_5319__boxed_5071_, v_x_5320__boxed_5072_, v_x_5069_, v_x_5070_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_5074_, lean_object* v_n_5075_, lean_object* v_k_5076_, lean_object* v_v_5077_){
_start:
{
lean_object* v___x_5078_; 
v___x_5078_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_5075_, v_k_5076_, v_v_5077_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_5079_, size_t v_depth_5080_, lean_object* v_keys_5081_, lean_object* v_vals_5082_, lean_object* v_heq_5083_, lean_object* v_i_5084_, lean_object* v_entries_5085_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_5080_, v_keys_5081_, v_vals_5082_, v_i_5084_, v_entries_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_5087_, lean_object* v_depth_5088_, lean_object* v_keys_5089_, lean_object* v_vals_5090_, lean_object* v_heq_5091_, lean_object* v_i_5092_, lean_object* v_entries_5093_){
_start:
{
size_t v_depth_boxed_5094_; lean_object* v_res_5095_; 
v_depth_boxed_5094_ = lean_unbox_usize(v_depth_5088_);
lean_dec(v_depth_5088_);
v_res_5095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_5087_, v_depth_boxed_5094_, v_keys_5089_, v_vals_5090_, v_heq_5091_, v_i_5092_, v_entries_5093_);
lean_dec_ref(v_vals_5090_);
lean_dec_ref(v_keys_5089_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_5096_, lean_object* v_x_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_5097_, v_x_5098_, v_x_5099_, v_x_5100_);
return v___x_5101_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5104_ = l_Lean_stringToMessageData(v___x_5103_);
return v___x_5104_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5107_ = l_Lean_stringToMessageData(v___x_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5108_, lean_object* v_as_5109_, size_t v_sz_5110_, size_t v_i_5111_, lean_object* v_b_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_a_5119_; uint8_t v___x_5123_; 
v___x_5123_ = lean_usize_dec_lt(v_i_5111_, v_sz_5110_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v_b_5112_);
return v___x_5124_;
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5126_; 
v_a_5125_ = lean_array_uget_borrowed(v_as_5109_, v_i_5111_);
lean_inc(v_a_5125_);
v___x_5126_ = l_Lean_MVarId_getType(v_a_5125_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5127_);
lean_dec_ref(v___x_5126_);
if (lean_obj_tag(v_a_5127_) == 10)
{
lean_object* v_expr_5145_; 
v_expr_5145_ = lean_ctor_get(v_a_5127_, 1);
if (lean_obj_tag(v_expr_5145_) == 5)
{
lean_object* v_arg_5146_; lean_object* v___x_5147_; 
lean_inc_ref(v_expr_5145_);
lean_dec_ref(v_a_5127_);
v_arg_5146_ = lean_ctor_get(v_expr_5145_, 1);
lean_inc_ref(v_arg_5146_);
lean_dec_ref(v_expr_5145_);
lean_inc_ref(v_arg_5146_);
v___x_5147_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5108_, v_arg_5146_);
if (lean_obj_tag(v___x_5147_) == 1)
{
lean_object* v_val_5148_; lean_object* v_fst_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; 
lean_dec_ref(v_arg_5146_);
v_val_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_val_5148_);
lean_dec_ref(v___x_5147_);
v_fst_5149_ = lean_ctor_get(v_val_5148_, 0);
lean_inc(v_fst_5149_);
lean_dec(v_val_5148_);
v___x_5150_ = lean_array_get_size(v_b_5112_);
v___x_5151_ = lean_nat_dec_lt(v_fst_5149_, v___x_5150_);
if (v___x_5151_ == 0)
{
lean_dec(v_fst_5149_);
v_a_5119_ = v_b_5112_;
goto v___jp_5118_;
}
else
{
lean_object* v_v_5152_; lean_object* v___x_5153_; lean_object* v_xs_x27_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v_v_5152_ = lean_array_fget(v_b_5112_, v_fst_5149_);
v___x_5153_ = lean_box(0);
v_xs_x27_5154_ = lean_array_fset(v_b_5112_, v_fst_5149_, v___x_5153_);
lean_inc(v_a_5125_);
v___x_5155_ = lean_array_push(v_v_5152_, v_a_5125_);
v___x_5156_ = lean_array_fset(v_xs_x27_5154_, v_fst_5149_, v___x_5155_);
lean_dec(v_fst_5149_);
v_a_5119_ = v___x_5156_;
goto v___jp_5118_;
}
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_dec(v___x_5147_);
v___x_5157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5158_ = l_Lean_indentExpr(v_arg_5146_);
v___x_5159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5157_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5159_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_dec_ref(v___x_5160_);
v_a_5119_ = v_b_5112_;
goto v___jp_5118_;
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
lean_dec_ref(v_b_5112_);
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5160_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5160_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
else
{
v___y_5129_ = v___y_5113_;
v___y_5130_ = v___y_5114_;
v___y_5131_ = v___y_5115_;
v___y_5132_ = v___y_5116_;
goto v___jp_5128_;
}
}
else
{
v___y_5129_ = v___y_5113_;
v___y_5130_ = v___y_5114_;
v___y_5131_ = v___y_5115_;
v___y_5132_ = v___y_5116_;
goto v___jp_5128_;
}
v___jp_5128_:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5134_ = l_Lean_indentExpr(v_a_5127_);
v___x_5135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5133_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
v___x_5136_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5135_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_dec_ref(v___x_5136_);
v_a_5119_ = v_b_5112_;
goto v___jp_5118_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec_ref(v_b_5112_);
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5136_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5136_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec_ref(v_b_5112_);
v_a_5169_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5126_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5126_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
v___jp_5118_:
{
size_t v___x_5120_; size_t v___x_5121_; 
v___x_5120_ = ((size_t)1ULL);
v___x_5121_ = lean_usize_add(v_i_5111_, v___x_5120_);
v_i_5111_ = v___x_5121_;
v_b_5112_ = v_a_5119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5177_, lean_object* v_as_5178_, lean_object* v_sz_5179_, lean_object* v_i_5180_, lean_object* v_b_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
size_t v_sz_boxed_5187_; size_t v_i_boxed_5188_; lean_object* v_res_5189_; 
v_sz_boxed_5187_ = lean_unbox_usize(v_sz_5179_);
lean_dec(v_sz_5179_);
v_i_boxed_5188_ = lean_unbox_usize(v_i_5180_);
lean_dec(v_i_5180_);
v_res_5189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5177_, v_as_5178_, v_sz_boxed_5187_, v_i_boxed_5188_, v_b_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec_ref(v_as_5178_);
lean_dec_ref(v_argsPacker_5177_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5190_, lean_object* v_numFuncs_5191_, lean_object* v_goals_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v___x_5198_; lean_object* v_r_5199_; size_t v_sz_5200_; size_t v___x_5201_; lean_object* v___x_5202_; 
v___x_5198_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5199_ = lean_mk_array(v_numFuncs_5191_, v___x_5198_);
v_sz_5200_ = lean_array_size(v_goals_5192_);
v___x_5201_ = ((size_t)0ULL);
v___x_5202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5190_, v_goals_5192_, v_sz_5200_, v___x_5201_, v_r_5199_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5203_, lean_object* v_numFuncs_5204_, lean_object* v_goals_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5203_, v_numFuncs_5204_, v_goals_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_a_5209_);
lean_dec_ref(v_a_5208_);
lean_dec(v_a_5207_);
lean_dec_ref(v_a_5206_);
lean_dec_ref(v_goals_5205_);
lean_dec_ref(v_argsPacker_5203_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; lean_object* v_infoState_5216_; uint8_t v_enabled_5217_; 
v___x_5215_ = lean_st_ref_get(v___y_5213_);
v_infoState_5216_ = lean_ctor_get(v___x_5215_, 7);
lean_inc_ref(v_infoState_5216_);
lean_dec(v___x_5215_);
v_enabled_5217_ = lean_ctor_get_uint8(v_infoState_5216_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5216_);
if (v_enabled_5217_ == 0)
{
lean_object* v___x_5218_; lean_object* v___x_5219_; 
lean_dec_ref(v_t_5212_);
v___x_5218_ = lean_box(0);
v___x_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
return v___x_5219_;
}
else
{
lean_object* v___x_5220_; lean_object* v_infoState_5221_; lean_object* v_env_5222_; lean_object* v_nextMacroScope_5223_; lean_object* v_ngen_5224_; lean_object* v_auxDeclNGen_5225_; lean_object* v_traceState_5226_; lean_object* v_cache_5227_; lean_object* v_messages_5228_; lean_object* v_snapshotTasks_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5251_; 
v___x_5220_ = lean_st_ref_take(v___y_5213_);
v_infoState_5221_ = lean_ctor_get(v___x_5220_, 7);
v_env_5222_ = lean_ctor_get(v___x_5220_, 0);
v_nextMacroScope_5223_ = lean_ctor_get(v___x_5220_, 1);
v_ngen_5224_ = lean_ctor_get(v___x_5220_, 2);
v_auxDeclNGen_5225_ = lean_ctor_get(v___x_5220_, 3);
v_traceState_5226_ = lean_ctor_get(v___x_5220_, 4);
v_cache_5227_ = lean_ctor_get(v___x_5220_, 5);
v_messages_5228_ = lean_ctor_get(v___x_5220_, 6);
v_snapshotTasks_5229_ = lean_ctor_get(v___x_5220_, 8);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5231_ = v___x_5220_;
v_isShared_5232_ = v_isSharedCheck_5251_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_snapshotTasks_5229_);
lean_inc(v_infoState_5221_);
lean_inc(v_messages_5228_);
lean_inc(v_cache_5227_);
lean_inc(v_traceState_5226_);
lean_inc(v_auxDeclNGen_5225_);
lean_inc(v_ngen_5224_);
lean_inc(v_nextMacroScope_5223_);
lean_inc(v_env_5222_);
lean_dec(v___x_5220_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5251_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
uint8_t v_enabled_5233_; lean_object* v_assignment_5234_; lean_object* v_lazyAssignment_5235_; lean_object* v_trees_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5250_; 
v_enabled_5233_ = lean_ctor_get_uint8(v_infoState_5221_, sizeof(void*)*3);
v_assignment_5234_ = lean_ctor_get(v_infoState_5221_, 0);
v_lazyAssignment_5235_ = lean_ctor_get(v_infoState_5221_, 1);
v_trees_5236_ = lean_ctor_get(v_infoState_5221_, 2);
v_isSharedCheck_5250_ = !lean_is_exclusive(v_infoState_5221_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5238_ = v_infoState_5221_;
v_isShared_5239_ = v_isSharedCheck_5250_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_trees_5236_);
lean_inc(v_lazyAssignment_5235_);
lean_inc(v_assignment_5234_);
lean_dec(v_infoState_5221_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5250_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5240_; lean_object* v___x_5242_; 
v___x_5240_ = l_Lean_PersistentArray_push___redArg(v_trees_5236_, v_t_5212_);
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 2, v___x_5240_);
v___x_5242_ = v___x_5238_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_assignment_5234_);
lean_ctor_set(v_reuseFailAlloc_5249_, 1, v_lazyAssignment_5235_);
lean_ctor_set(v_reuseFailAlloc_5249_, 2, v___x_5240_);
lean_ctor_set_uint8(v_reuseFailAlloc_5249_, sizeof(void*)*3, v_enabled_5233_);
v___x_5242_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
lean_object* v___x_5244_; 
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 7, v___x_5242_);
v___x_5244_ = v___x_5231_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_env_5222_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v_nextMacroScope_5223_);
lean_ctor_set(v_reuseFailAlloc_5248_, 2, v_ngen_5224_);
lean_ctor_set(v_reuseFailAlloc_5248_, 3, v_auxDeclNGen_5225_);
lean_ctor_set(v_reuseFailAlloc_5248_, 4, v_traceState_5226_);
lean_ctor_set(v_reuseFailAlloc_5248_, 5, v_cache_5227_);
lean_ctor_set(v_reuseFailAlloc_5248_, 6, v_messages_5228_);
lean_ctor_set(v_reuseFailAlloc_5248_, 7, v___x_5242_);
lean_ctor_set(v_reuseFailAlloc_5248_, 8, v_snapshotTasks_5229_);
v___x_5244_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5245_ = lean_st_ref_set(v___y_5213_, v___x_5244_);
v___x_5246_ = lean_box(0);
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5246_);
return v___x_5247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5252_, v___y_5253_);
lean_dec(v___y_5253_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_){
_start:
{
lean_object* v___x_5264_; 
v___x_5264_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5256_, v___y_5262_);
return v___x_5264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5274_, lean_object* v___y_5275_){
_start:
{
uint8_t v___x_5277_; 
v___x_5277_ = l_Lean_Expr_hasMVar(v_e_5274_);
if (v___x_5277_ == 0)
{
lean_object* v___x_5278_; 
v___x_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5278_, 0, v_e_5274_);
return v___x_5278_;
}
else
{
lean_object* v___x_5279_; lean_object* v_mctx_5280_; lean_object* v___x_5281_; lean_object* v_fst_5282_; lean_object* v_snd_5283_; lean_object* v___x_5284_; lean_object* v_cache_5285_; lean_object* v_zetaDeltaFVarIds_5286_; lean_object* v_postponed_5287_; lean_object* v_diag_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5297_; 
v___x_5279_ = lean_st_ref_get(v___y_5275_);
v_mctx_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc_ref(v_mctx_5280_);
lean_dec(v___x_5279_);
v___x_5281_ = l_Lean_instantiateMVarsCore(v_mctx_5280_, v_e_5274_);
v_fst_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_fst_5282_);
v_snd_5283_ = lean_ctor_get(v___x_5281_, 1);
lean_inc(v_snd_5283_);
lean_dec_ref(v___x_5281_);
v___x_5284_ = lean_st_ref_take(v___y_5275_);
v_cache_5285_ = lean_ctor_get(v___x_5284_, 1);
v_zetaDeltaFVarIds_5286_ = lean_ctor_get(v___x_5284_, 2);
v_postponed_5287_ = lean_ctor_get(v___x_5284_, 3);
v_diag_5288_ = lean_ctor_get(v___x_5284_, 4);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; 
v_unused_5298_ = lean_ctor_get(v___x_5284_, 0);
lean_dec(v_unused_5298_);
v___x_5290_ = v___x_5284_;
v_isShared_5291_ = v_isSharedCheck_5297_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_diag_5288_);
lean_inc(v_postponed_5287_);
lean_inc(v_zetaDeltaFVarIds_5286_);
lean_inc(v_cache_5285_);
lean_dec(v___x_5284_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5297_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v_snd_5283_);
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_snd_5283_);
lean_ctor_set(v_reuseFailAlloc_5296_, 1, v_cache_5285_);
lean_ctor_set(v_reuseFailAlloc_5296_, 2, v_zetaDeltaFVarIds_5286_);
lean_ctor_set(v_reuseFailAlloc_5296_, 3, v_postponed_5287_);
lean_ctor_set(v_reuseFailAlloc_5296_, 4, v_diag_5288_);
v___x_5293_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = lean_st_ref_set(v___y_5275_, v___x_5293_);
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v_fst_5282_);
return v___x_5295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5299_, v___y_5300_);
lean_dec(v___y_5300_);
return v_res_5302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5303_, v___y_5305_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
lean_dec(v___y_5314_);
lean_dec_ref(v___y_5313_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5317_, size_t v_i_5318_, size_t v_stop_5319_, lean_object* v_b_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
uint8_t v___x_5328_; 
v___x_5328_ = lean_usize_dec_eq(v_i_5318_, v_stop_5319_);
if (v___x_5328_ == 0)
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
v___x_5329_ = lean_array_uget_borrowed(v_as_5317_, v_i_5318_);
lean_inc(v___x_5329_);
v___x_5330_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5329_);
v___x_5331_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5330_, v___y_5326_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; size_t v___x_5333_; size_t v___x_5334_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
lean_inc(v_a_5332_);
lean_dec_ref(v___x_5331_);
v___x_5333_ = ((size_t)1ULL);
v___x_5334_ = lean_usize_add(v_i_5318_, v___x_5333_);
v_i_5318_ = v___x_5334_;
v_b_5320_ = v_a_5332_;
goto _start;
}
else
{
return v___x_5331_;
}
}
else
{
lean_object* v___x_5336_; 
v___x_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5336_, 0, v_b_5320_);
return v___x_5336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5337_, lean_object* v_i_5338_, lean_object* v_stop_5339_, lean_object* v_b_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
size_t v_i_boxed_5348_; size_t v_stop_boxed_5349_; lean_object* v_res_5350_; 
v_i_boxed_5348_ = lean_unbox_usize(v_i_5338_);
lean_dec(v_i_5338_);
v_stop_boxed_5349_ = lean_unbox_usize(v_stop_5339_);
lean_dec(v_stop_5339_);
v_res_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5337_, v_i_boxed_5348_, v_stop_boxed_5349_, v_b_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec_ref(v_as_5337_);
return v_res_5350_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = lean_unsigned_to_nat(32u);
v___x_5352_ = lean_mk_empty_array_with_capacity(v___x_5351_);
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5352_);
return v___x_5353_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5354_ = ((size_t)5ULL);
v___x_5355_ = lean_unsigned_to_nat(0u);
v___x_5356_ = lean_unsigned_to_nat(32u);
v___x_5357_ = lean_mk_empty_array_with_capacity(v___x_5356_);
v___x_5358_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5359_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5359_, 0, v___x_5358_);
lean_ctor_set(v___x_5359_, 1, v___x_5357_);
lean_ctor_set(v___x_5359_, 2, v___x_5355_);
lean_ctor_set(v___x_5359_, 3, v___x_5355_);
lean_ctor_set_usize(v___x_5359_, 4, v___x_5354_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5360_){
_start:
{
lean_object* v___x_5362_; lean_object* v_infoState_5363_; lean_object* v_trees_5364_; lean_object* v___x_5365_; lean_object* v_infoState_5366_; lean_object* v_env_5367_; lean_object* v_nextMacroScope_5368_; lean_object* v_ngen_5369_; lean_object* v_auxDeclNGen_5370_; lean_object* v_traceState_5371_; lean_object* v_cache_5372_; lean_object* v_messages_5373_; lean_object* v_snapshotTasks_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5395_; 
v___x_5362_ = lean_st_ref_get(v___y_5360_);
v_infoState_5363_ = lean_ctor_get(v___x_5362_, 7);
lean_inc_ref(v_infoState_5363_);
lean_dec(v___x_5362_);
v_trees_5364_ = lean_ctor_get(v_infoState_5363_, 2);
lean_inc_ref(v_trees_5364_);
lean_dec_ref(v_infoState_5363_);
v___x_5365_ = lean_st_ref_take(v___y_5360_);
v_infoState_5366_ = lean_ctor_get(v___x_5365_, 7);
v_env_5367_ = lean_ctor_get(v___x_5365_, 0);
v_nextMacroScope_5368_ = lean_ctor_get(v___x_5365_, 1);
v_ngen_5369_ = lean_ctor_get(v___x_5365_, 2);
v_auxDeclNGen_5370_ = lean_ctor_get(v___x_5365_, 3);
v_traceState_5371_ = lean_ctor_get(v___x_5365_, 4);
v_cache_5372_ = lean_ctor_get(v___x_5365_, 5);
v_messages_5373_ = lean_ctor_get(v___x_5365_, 6);
v_snapshotTasks_5374_ = lean_ctor_get(v___x_5365_, 8);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5376_ = v___x_5365_;
v_isShared_5377_ = v_isSharedCheck_5395_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_snapshotTasks_5374_);
lean_inc(v_infoState_5366_);
lean_inc(v_messages_5373_);
lean_inc(v_cache_5372_);
lean_inc(v_traceState_5371_);
lean_inc(v_auxDeclNGen_5370_);
lean_inc(v_ngen_5369_);
lean_inc(v_nextMacroScope_5368_);
lean_inc(v_env_5367_);
lean_dec(v___x_5365_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5395_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
uint8_t v_enabled_5378_; lean_object* v_assignment_5379_; lean_object* v_lazyAssignment_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5393_; 
v_enabled_5378_ = lean_ctor_get_uint8(v_infoState_5366_, sizeof(void*)*3);
v_assignment_5379_ = lean_ctor_get(v_infoState_5366_, 0);
v_lazyAssignment_5380_ = lean_ctor_get(v_infoState_5366_, 1);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_infoState_5366_);
if (v_isSharedCheck_5393_ == 0)
{
lean_object* v_unused_5394_; 
v_unused_5394_ = lean_ctor_get(v_infoState_5366_, 2);
lean_dec(v_unused_5394_);
v___x_5382_ = v_infoState_5366_;
v_isShared_5383_ = v_isSharedCheck_5393_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_lazyAssignment_5380_);
lean_inc(v_assignment_5379_);
lean_dec(v_infoState_5366_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5393_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5384_; lean_object* v___x_5386_; 
v___x_5384_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 2, v___x_5384_);
v___x_5386_ = v___x_5382_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_assignment_5379_);
lean_ctor_set(v_reuseFailAlloc_5392_, 1, v_lazyAssignment_5380_);
lean_ctor_set(v_reuseFailAlloc_5392_, 2, v___x_5384_);
lean_ctor_set_uint8(v_reuseFailAlloc_5392_, sizeof(void*)*3, v_enabled_5378_);
v___x_5386_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
lean_object* v___x_5388_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 7, v___x_5386_);
v___x_5388_ = v___x_5376_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_env_5367_);
lean_ctor_set(v_reuseFailAlloc_5391_, 1, v_nextMacroScope_5368_);
lean_ctor_set(v_reuseFailAlloc_5391_, 2, v_ngen_5369_);
lean_ctor_set(v_reuseFailAlloc_5391_, 3, v_auxDeclNGen_5370_);
lean_ctor_set(v_reuseFailAlloc_5391_, 4, v_traceState_5371_);
lean_ctor_set(v_reuseFailAlloc_5391_, 5, v_cache_5372_);
lean_ctor_set(v_reuseFailAlloc_5391_, 6, v_messages_5373_);
lean_ctor_set(v_reuseFailAlloc_5391_, 7, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5391_, 8, v_snapshotTasks_5374_);
v___x_5388_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = lean_st_ref_set(v___y_5360_, v___x_5388_);
v___x_5390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5390_, 0, v_trees_5364_);
return v___x_5390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5396_);
lean_dec(v___y_5396_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5399_, lean_object* v_mkInfoTree_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v_a_5408_, lean_object* v_a_x3f_5409_){
_start:
{
lean_object* v___x_5411_; lean_object* v_infoState_5412_; lean_object* v_trees_5413_; lean_object* v___x_5414_; 
v___x_5411_ = lean_st_ref_get(v___y_5399_);
v_infoState_5412_ = lean_ctor_get(v___x_5411_, 7);
lean_inc_ref(v_infoState_5412_);
lean_dec(v___x_5411_);
v_trees_5413_ = lean_ctor_get(v_infoState_5412_, 2);
lean_inc_ref(v_trees_5413_);
lean_dec_ref(v_infoState_5412_);
lean_inc(v___y_5399_);
v___x_5414_ = lean_apply_10(v_mkInfoTree_5400_, v_trees_5413_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5399_, lean_box(0));
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5453_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5417_ = v___x_5414_;
v_isShared_5418_ = v_isSharedCheck_5453_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5414_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5453_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5419_; lean_object* v_infoState_5420_; lean_object* v_env_5421_; lean_object* v_nextMacroScope_5422_; lean_object* v_ngen_5423_; lean_object* v_auxDeclNGen_5424_; lean_object* v_traceState_5425_; lean_object* v_cache_5426_; lean_object* v_messages_5427_; lean_object* v_snapshotTasks_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5452_; 
v___x_5419_ = lean_st_ref_take(v___y_5399_);
v_infoState_5420_ = lean_ctor_get(v___x_5419_, 7);
v_env_5421_ = lean_ctor_get(v___x_5419_, 0);
v_nextMacroScope_5422_ = lean_ctor_get(v___x_5419_, 1);
v_ngen_5423_ = lean_ctor_get(v___x_5419_, 2);
v_auxDeclNGen_5424_ = lean_ctor_get(v___x_5419_, 3);
v_traceState_5425_ = lean_ctor_get(v___x_5419_, 4);
v_cache_5426_ = lean_ctor_get(v___x_5419_, 5);
v_messages_5427_ = lean_ctor_get(v___x_5419_, 6);
v_snapshotTasks_5428_ = lean_ctor_get(v___x_5419_, 8);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5430_ = v___x_5419_;
v_isShared_5431_ = v_isSharedCheck_5452_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_snapshotTasks_5428_);
lean_inc(v_infoState_5420_);
lean_inc(v_messages_5427_);
lean_inc(v_cache_5426_);
lean_inc(v_traceState_5425_);
lean_inc(v_auxDeclNGen_5424_);
lean_inc(v_ngen_5423_);
lean_inc(v_nextMacroScope_5422_);
lean_inc(v_env_5421_);
lean_dec(v___x_5419_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5452_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
uint8_t v_enabled_5432_; lean_object* v_assignment_5433_; lean_object* v_lazyAssignment_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5450_; 
v_enabled_5432_ = lean_ctor_get_uint8(v_infoState_5420_, sizeof(void*)*3);
v_assignment_5433_ = lean_ctor_get(v_infoState_5420_, 0);
v_lazyAssignment_5434_ = lean_ctor_get(v_infoState_5420_, 1);
v_isSharedCheck_5450_ = !lean_is_exclusive(v_infoState_5420_);
if (v_isSharedCheck_5450_ == 0)
{
lean_object* v_unused_5451_; 
v_unused_5451_ = lean_ctor_get(v_infoState_5420_, 2);
lean_dec(v_unused_5451_);
v___x_5436_ = v_infoState_5420_;
v_isShared_5437_ = v_isSharedCheck_5450_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_lazyAssignment_5434_);
lean_inc(v_assignment_5433_);
lean_dec(v_infoState_5420_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5450_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; lean_object* v___x_5440_; 
v___x_5438_ = l_Lean_PersistentArray_push___redArg(v_a_5408_, v_a_5415_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 2, v___x_5438_);
v___x_5440_ = v___x_5436_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_assignment_5433_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_lazyAssignment_5434_);
lean_ctor_set(v_reuseFailAlloc_5449_, 2, v___x_5438_);
lean_ctor_set_uint8(v_reuseFailAlloc_5449_, sizeof(void*)*3, v_enabled_5432_);
v___x_5440_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5442_; 
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 7, v___x_5440_);
v___x_5442_ = v___x_5430_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_env_5421_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v_nextMacroScope_5422_);
lean_ctor_set(v_reuseFailAlloc_5448_, 2, v_ngen_5423_);
lean_ctor_set(v_reuseFailAlloc_5448_, 3, v_auxDeclNGen_5424_);
lean_ctor_set(v_reuseFailAlloc_5448_, 4, v_traceState_5425_);
lean_ctor_set(v_reuseFailAlloc_5448_, 5, v_cache_5426_);
lean_ctor_set(v_reuseFailAlloc_5448_, 6, v_messages_5427_);
lean_ctor_set(v_reuseFailAlloc_5448_, 7, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5448_, 8, v_snapshotTasks_5428_);
v___x_5442_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5446_; 
v___x_5443_ = lean_st_ref_set(v___y_5399_, v___x_5442_);
lean_dec(v___y_5399_);
v___x_5444_ = lean_box(0);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 0, v___x_5444_);
v___x_5446_ = v___x_5417_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v___x_5444_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
lean_dec_ref(v_a_5408_);
lean_dec(v___y_5399_);
v_a_5454_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5414_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5414_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5462_, lean_object* v_mkInfoTree_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v_a_5471_, lean_object* v_a_x3f_5472_, lean_object* v___y_5473_){
_start:
{
lean_object* v_res_5474_; 
v_res_5474_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5462_, v_mkInfoTree_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v_a_5471_, v_a_x3f_5472_);
lean_dec(v_a_x3f_5472_);
return v_res_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5475_, lean_object* v_mkInfoTree_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_){
_start:
{
lean_object* v___x_5486_; lean_object* v_infoState_5487_; uint8_t v_enabled_5488_; 
v___x_5486_ = lean_st_ref_get(v___y_5484_);
v_infoState_5487_ = lean_ctor_get(v___x_5486_, 7);
lean_inc_ref(v_infoState_5487_);
lean_dec(v___x_5486_);
v_enabled_5488_ = lean_ctor_get_uint8(v_infoState_5487_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5487_);
if (v_enabled_5488_ == 0)
{
lean_object* v___x_5489_; 
lean_dec_ref(v_mkInfoTree_5476_);
v___x_5489_ = lean_apply_9(v_x_5475_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, lean_box(0));
return v___x_5489_;
}
else
{
lean_object* v___x_5490_; lean_object* v_a_5491_; lean_object* v_r_5492_; 
v___x_5490_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5484_);
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref(v___x_5490_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
lean_inc(v___y_5480_);
lean_inc_ref(v___y_5479_);
lean_inc(v___y_5478_);
lean_inc_ref(v___y_5477_);
v_r_5492_ = lean_apply_9(v_x_5475_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, lean_box(0));
if (lean_obj_tag(v_r_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5517_; 
v_a_5493_ = lean_ctor_get(v_r_5492_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_r_5492_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5495_ = v_r_5492_;
v_isShared_5496_ = v_isSharedCheck_5517_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v_r_5492_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5517_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
lean_inc(v_a_5493_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set_tag(v___x_5495_, 1);
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
lean_object* v___x_5499_; 
v___x_5499_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5484_, v_mkInfoTree_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v_a_5491_, v___x_5498_);
lean_dec_ref(v___x_5498_);
if (lean_obj_tag(v___x_5499_) == 0)
{
lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5499_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; 
v_unused_5507_ = lean_ctor_get(v___x_5499_, 0);
lean_dec(v_unused_5507_);
v___x_5501_ = v___x_5499_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_dec(v___x_5499_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 0, v_a_5493_);
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5493_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
else
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5515_; 
lean_dec(v_a_5493_);
v_a_5508_ = lean_ctor_get(v___x_5499_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5499_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5510_ = v___x_5499_;
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5499_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5511_ == 0)
{
v___x_5513_ = v___x_5510_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
v_a_5518_ = lean_ctor_get(v_r_5492_, 0);
lean_inc(v_a_5518_);
lean_dec_ref(v_r_5492_);
v___x_5519_ = lean_box(0);
v___x_5520_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5484_, v_mkInfoTree_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v_a_5491_, v___x_5519_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5527_; 
v_isSharedCheck_5527_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5527_ == 0)
{
lean_object* v_unused_5528_; 
v_unused_5528_ = lean_ctor_get(v___x_5520_, 0);
lean_dec(v_unused_5528_);
v___x_5522_ = v___x_5520_;
v_isShared_5523_ = v_isSharedCheck_5527_;
goto v_resetjp_5521_;
}
else
{
lean_dec(v___x_5520_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5527_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5525_; 
if (v_isShared_5523_ == 0)
{
lean_ctor_set_tag(v___x_5522_, 1);
lean_ctor_set(v___x_5522_, 0, v_a_5518_);
v___x_5525_ = v___x_5522_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_a_5518_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
else
{
lean_object* v_a_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5536_; 
lean_dec(v_a_5518_);
v_a_5529_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5536_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5536_ == 0)
{
v___x_5531_ = v___x_5520_;
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_a_5529_);
lean_dec(v___x_5520_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5534_; 
if (v_isShared_5532_ == 0)
{
v___x_5534_ = v___x_5531_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
return v___x_5534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5537_, lean_object* v_mkInfoTree_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
lean_object* v_res_5548_; 
v_res_5548_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5537_, v_mkInfoTree_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
return v_res_5548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5549_, lean_object* v_trees_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v___x_5560_; 
v___x_5560_ = lean_apply_9(v_a_5549_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, lean_box(0));
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5569_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5563_ = v___x_5560_;
v_isShared_5564_ = v_isSharedCheck_5569_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5560_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5569_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5565_, 0, v_a_5561_);
lean_ctor_set(v___x_5565_, 1, v_trees_5550_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5565_);
v___x_5567_ = v___x_5563_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5565_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
else
{
lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5577_; 
lean_dec_ref(v_trees_5550_);
v_a_5570_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5572_ = v___x_5560_;
v_isShared_5573_ = v_isSharedCheck_5577_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_dec(v___x_5560_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5577_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5575_; 
if (v_isShared_5573_ == 0)
{
v___x_5575_ = v___x_5572_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5570_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5578_, lean_object* v_trees_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5578_, v_trees_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5590_, lean_object* v_ref_5591_, lean_object* v_tactic_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_){
_start:
{
lean_object* v___x_5602_; 
v___x_5602_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5590_, v___y_5594_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_object* v___x_5603_; 
lean_dec_ref(v___x_5602_);
lean_inc(v___y_5600_);
lean_inc_ref(v___y_5599_);
lean_inc(v___y_5598_);
lean_inc_ref(v___y_5597_);
lean_inc(v___y_5596_);
lean_inc_ref(v___y_5595_);
lean_inc(v___y_5594_);
lean_inc_ref(v___y_5593_);
v___x_5603_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v___x_5604_; 
lean_dec_ref(v___x_5603_);
v___x_5604_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5591_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
if (lean_obj_tag(v___x_5604_) == 0)
{
lean_object* v_a_5605_; lean_object* v___f_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
v_a_5605_ = lean_ctor_get(v___x_5604_, 0);
lean_inc(v_a_5605_);
lean_dec_ref(v___x_5604_);
v___f_5606_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5606_, 0, v_a_5605_);
v___x_5607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5607_, 0, v_tactic_5592_);
v___x_5608_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5607_, v___f_5606_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
return v___x_5608_;
}
else
{
lean_object* v_a_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5616_; 
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v_tactic_5592_);
v_a_5609_ = lean_ctor_get(v___x_5604_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5604_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5611_ = v___x_5604_;
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_a_5609_);
lean_dec(v___x_5604_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5614_; 
if (v_isShared_5612_ == 0)
{
v___x_5614_ = v___x_5611_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_a_5609_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
else
{
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v_tactic_5592_);
lean_dec(v_ref_5591_);
return v___x_5603_;
}
}
else
{
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v_tactic_5592_);
lean_dec(v_ref_5591_);
return v___x_5602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5617_, lean_object* v_ref_5618_, lean_object* v_tactic_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5617_, v_ref_5618_, v_tactic_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
return v_res_5629_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_box(1);
v___x_5631_ = l_Lean_MessageData_ofFormat(v___x_5630_);
return v___x_5631_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5635_; lean_object* v___x_5636_; 
v___x_5635_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5636_ = l_Lean_MessageData_ofFormat(v___x_5635_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5637_, lean_object* v_x_5638_){
_start:
{
if (lean_obj_tag(v_x_5638_) == 0)
{
return v_x_5637_;
}
else
{
lean_object* v_head_5639_; lean_object* v_tail_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5662_; 
v_head_5639_ = lean_ctor_get(v_x_5638_, 0);
v_tail_5640_ = lean_ctor_get(v_x_5638_, 1);
v_isSharedCheck_5662_ = !lean_is_exclusive(v_x_5638_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5642_ = v_x_5638_;
v_isShared_5643_ = v_isSharedCheck_5662_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_tail_5640_);
lean_inc(v_head_5639_);
lean_dec(v_x_5638_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5662_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v_before_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5660_; 
v_before_5644_ = lean_ctor_get(v_head_5639_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v_head_5639_);
if (v_isSharedCheck_5660_ == 0)
{
lean_object* v_unused_5661_; 
v_unused_5661_ = lean_ctor_get(v_head_5639_, 1);
lean_dec(v_unused_5661_);
v___x_5646_ = v_head_5639_;
v_isShared_5647_ = v_isSharedCheck_5660_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_before_5644_);
lean_dec(v_head_5639_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5660_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5648_; lean_object* v___x_5650_; 
v___x_5648_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5647_ == 0)
{
lean_ctor_set_tag(v___x_5646_, 7);
lean_ctor_set(v___x_5646_, 1, v___x_5648_);
lean_ctor_set(v___x_5646_, 0, v_x_5637_);
v___x_5650_ = v___x_5646_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_x_5637_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5648_);
v___x_5650_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
lean_object* v___x_5651_; lean_object* v___x_5653_; 
v___x_5651_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5643_ == 0)
{
lean_ctor_set_tag(v___x_5642_, 7);
lean_ctor_set(v___x_5642_, 1, v___x_5651_);
lean_ctor_set(v___x_5642_, 0, v___x_5650_);
v___x_5653_ = v___x_5642_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v___x_5651_);
v___x_5653_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v___x_5654_ = l_Lean_MessageData_ofSyntax(v_before_5644_);
v___x_5655_ = l_Lean_indentD(v___x_5654_);
v___x_5656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5653_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v_x_5637_ = v___x_5656_;
v_x_5638_ = v_tail_5640_;
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
lean_object* v___x_5666_; lean_object* v___x_5667_; 
v___x_5666_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5667_ = l_Lean_MessageData_ofFormat(v___x_5666_);
return v___x_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5668_, lean_object* v_macroStack_5669_, lean_object* v___y_5670_){
_start:
{
lean_object* v_options_5672_; lean_object* v___x_5673_; uint8_t v___x_5674_; 
v_options_5672_ = lean_ctor_get(v___y_5670_, 2);
v___x_5673_ = l_Lean_Elab_pp_macroStack;
v___x_5674_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_options_5672_, v___x_5673_);
if (v___x_5674_ == 0)
{
lean_object* v___x_5675_; 
lean_dec(v_macroStack_5669_);
v___x_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5675_, 0, v_msgData_5668_);
return v___x_5675_;
}
else
{
if (lean_obj_tag(v_macroStack_5669_) == 0)
{
lean_object* v___x_5676_; 
v___x_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5676_, 0, v_msgData_5668_);
return v___x_5676_;
}
else
{
lean_object* v_head_5677_; lean_object* v_after_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5693_; 
v_head_5677_ = lean_ctor_get(v_macroStack_5669_, 0);
lean_inc(v_head_5677_);
v_after_5678_ = lean_ctor_get(v_head_5677_, 1);
v_isSharedCheck_5693_ = !lean_is_exclusive(v_head_5677_);
if (v_isSharedCheck_5693_ == 0)
{
lean_object* v_unused_5694_; 
v_unused_5694_ = lean_ctor_get(v_head_5677_, 0);
lean_dec(v_unused_5694_);
v___x_5680_ = v_head_5677_;
v_isShared_5681_ = v_isSharedCheck_5693_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_after_5678_);
lean_dec(v_head_5677_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5693_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v___x_5682_; lean_object* v___x_5684_; 
v___x_5682_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5681_ == 0)
{
lean_ctor_set_tag(v___x_5680_, 7);
lean_ctor_set(v___x_5680_, 1, v___x_5682_);
lean_ctor_set(v___x_5680_, 0, v_msgData_5668_);
v___x_5684_ = v___x_5680_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_msgData_5668_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v___x_5682_);
v___x_5684_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v_msgData_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_5685_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = l_Lean_MessageData_ofSyntax(v_after_5678_);
v___x_5688_ = l_Lean_indentD(v___x_5687_);
v_msgData_5689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5689_, 0, v___x_5686_);
lean_ctor_set(v_msgData_5689_, 1, v___x_5688_);
v___x_5690_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5689_, v_macroStack_5669_);
v___x_5691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
return v___x_5691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5695_, lean_object* v_macroStack_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5695_, v_macroStack_5696_, v___y_5697_);
lean_dec_ref(v___y_5697_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v_ref_5708_; lean_object* v___x_5709_; lean_object* v_a_5710_; lean_object* v_macroStack_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v_a_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5722_; 
v_ref_5708_ = lean_ctor_get(v___y_5705_, 5);
v___x_5709_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5700_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
v_a_5710_ = lean_ctor_get(v___x_5709_, 0);
lean_inc(v_a_5710_);
lean_dec_ref(v___x_5709_);
v_macroStack_5711_ = lean_ctor_get(v___y_5701_, 1);
lean_inc(v_macroStack_5711_);
lean_dec_ref(v___y_5701_);
lean_inc(v_macroStack_5711_);
v___x_5712_ = l_Lean_Elab_getBetterRef(v_ref_5708_, v_macroStack_5711_);
v___x_5713_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5710_, v_macroStack_5711_, v___y_5705_);
v_a_5714_ = lean_ctor_get(v___x_5713_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5713_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5716_ = v___x_5713_;
v_isShared_5717_ = v_isSharedCheck_5722_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_a_5714_);
lean_dec(v___x_5713_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5722_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v___x_5718_; lean_object* v___x_5720_; 
v___x_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5712_);
lean_ctor_set(v___x_5718_, 1, v_a_5714_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set_tag(v___x_5716_, 1);
lean_ctor_set(v___x_5716_, 0, v___x_5718_);
v___x_5720_ = v___x_5716_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5718_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec(v___y_5725_);
return v_res_5731_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5733_; lean_object* v___x_5734_; 
v___x_5733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5734_ = l_Lean_stringToMessageData(v___x_5733_);
return v___x_5734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5735_, size_t v_sz_5736_, size_t v_i_5737_, lean_object* v_b_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_){
_start:
{
lean_object* v_a_5747_; uint8_t v___x_5751_; 
v___x_5751_ = lean_usize_dec_lt(v_i_5737_, v_sz_5736_);
if (v___x_5751_ == 0)
{
lean_object* v___x_5752_; 
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
v___x_5752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5752_, 0, v_b_5738_);
return v___x_5752_;
}
else
{
lean_object* v_a_5753_; lean_object* v___x_5754_; 
v_a_5753_ = lean_array_uget_borrowed(v_as_5735_, v_i_5737_);
lean_inc(v_a_5753_);
v___x_5754_ = l_Lean_MVarId_getType(v_a_5753_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v_a_5755_; lean_object* v___x_5756_; 
v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
lean_inc(v_a_5755_);
lean_dec_ref(v___x_5754_);
lean_inc(v_a_5753_);
v___x_5756_ = l_Lean_MVarId_getType(v_a_5753_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
lean_inc(v_a_5757_);
lean_dec_ref(v___x_5756_);
v___x_5758_ = lean_box(0);
v___x_5759_ = l_Lean_getRecAppSyntax_x3f(v_a_5757_);
lean_dec(v_a_5757_);
if (lean_obj_tag(v___x_5759_) == 1)
{
lean_object* v_val_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v_val_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_val_5760_);
lean_dec_ref(v___x_5759_);
v___x_5761_ = l_Lean_Expr_mdataExpr_x21(v_a_5755_);
lean_dec(v_a_5755_);
lean_inc(v_a_5753_);
v___x_5762_ = l_Lean_MVarId_setType___redArg(v_a_5753_, v___x_5761_, v___y_5742_);
if (lean_obj_tag(v___x_5762_) == 0)
{
lean_object* v_fileName_5763_; lean_object* v_fileMap_5764_; lean_object* v_options_5765_; lean_object* v_currRecDepth_5766_; lean_object* v_maxRecDepth_5767_; lean_object* v_ref_5768_; lean_object* v_currNamespace_5769_; lean_object* v_openDecls_5770_; lean_object* v_initHeartbeats_5771_; lean_object* v_maxHeartbeats_5772_; lean_object* v_quotContext_5773_; lean_object* v_currMacroScope_5774_; uint8_t v_diag_5775_; lean_object* v_cancelTk_x3f_5776_; uint8_t v_suppressElabErrors_5777_; lean_object* v_inheritedTraceOptions_5778_; lean_object* v_ref_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
lean_dec_ref(v___x_5762_);
v_fileName_5763_ = lean_ctor_get(v___y_5743_, 0);
v_fileMap_5764_ = lean_ctor_get(v___y_5743_, 1);
v_options_5765_ = lean_ctor_get(v___y_5743_, 2);
v_currRecDepth_5766_ = lean_ctor_get(v___y_5743_, 3);
v_maxRecDepth_5767_ = lean_ctor_get(v___y_5743_, 4);
v_ref_5768_ = lean_ctor_get(v___y_5743_, 5);
v_currNamespace_5769_ = lean_ctor_get(v___y_5743_, 6);
v_openDecls_5770_ = lean_ctor_get(v___y_5743_, 7);
v_initHeartbeats_5771_ = lean_ctor_get(v___y_5743_, 8);
v_maxHeartbeats_5772_ = lean_ctor_get(v___y_5743_, 9);
v_quotContext_5773_ = lean_ctor_get(v___y_5743_, 10);
v_currMacroScope_5774_ = lean_ctor_get(v___y_5743_, 11);
v_diag_5775_ = lean_ctor_get_uint8(v___y_5743_, sizeof(void*)*14);
v_cancelTk_x3f_5776_ = lean_ctor_get(v___y_5743_, 12);
v_suppressElabErrors_5777_ = lean_ctor_get_uint8(v___y_5743_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5778_ = lean_ctor_get(v___y_5743_, 13);
v_ref_5779_ = l_Lean_replaceRef(v_val_5760_, v_ref_5768_);
lean_dec(v_val_5760_);
lean_inc_ref(v_inheritedTraceOptions_5778_);
lean_inc(v_cancelTk_x3f_5776_);
lean_inc(v_currMacroScope_5774_);
lean_inc(v_quotContext_5773_);
lean_inc(v_maxHeartbeats_5772_);
lean_inc(v_initHeartbeats_5771_);
lean_inc(v_openDecls_5770_);
lean_inc(v_currNamespace_5769_);
lean_inc(v_maxRecDepth_5767_);
lean_inc(v_currRecDepth_5766_);
lean_inc_ref(v_options_5765_);
lean_inc_ref(v_fileMap_5764_);
lean_inc_ref(v_fileName_5763_);
v___x_5780_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5780_, 0, v_fileName_5763_);
lean_ctor_set(v___x_5780_, 1, v_fileMap_5764_);
lean_ctor_set(v___x_5780_, 2, v_options_5765_);
lean_ctor_set(v___x_5780_, 3, v_currRecDepth_5766_);
lean_ctor_set(v___x_5780_, 4, v_maxRecDepth_5767_);
lean_ctor_set(v___x_5780_, 5, v_ref_5779_);
lean_ctor_set(v___x_5780_, 6, v_currNamespace_5769_);
lean_ctor_set(v___x_5780_, 7, v_openDecls_5770_);
lean_ctor_set(v___x_5780_, 8, v_initHeartbeats_5771_);
lean_ctor_set(v___x_5780_, 9, v_maxHeartbeats_5772_);
lean_ctor_set(v___x_5780_, 10, v_quotContext_5773_);
lean_ctor_set(v___x_5780_, 11, v_currMacroScope_5774_);
lean_ctor_set(v___x_5780_, 12, v_cancelTk_x3f_5776_);
lean_ctor_set(v___x_5780_, 13, v_inheritedTraceOptions_5778_);
lean_ctor_set_uint8(v___x_5780_, sizeof(void*)*14, v_diag_5775_);
lean_ctor_set_uint8(v___x_5780_, sizeof(void*)*14 + 1, v_suppressElabErrors_5777_);
lean_inc(v___y_5744_);
lean_inc(v___y_5742_);
lean_inc_ref(v___y_5741_);
lean_inc(v___y_5740_);
lean_inc_ref(v___y_5739_);
lean_inc(v_a_5753_);
v___x_5781_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5753_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___x_5780_, v___y_5744_);
if (lean_obj_tag(v___x_5781_) == 0)
{
lean_dec_ref(v___x_5781_);
v_a_5747_ = v___x_5758_;
goto v___jp_5746_;
}
else
{
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
return v___x_5781_;
}
}
else
{
lean_dec(v_val_5760_);
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
return v___x_5762_;
}
}
else
{
lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; 
lean_dec(v___x_5759_);
v___x_5782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5783_ = l_Lean_indentExpr(v_a_5755_);
v___x_5784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5784_, 0, v___x_5782_);
lean_ctor_set(v___x_5784_, 1, v___x_5783_);
lean_inc_ref(v___y_5739_);
v___x_5785_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5784_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
if (lean_obj_tag(v___x_5785_) == 0)
{
lean_dec_ref(v___x_5785_);
v_a_5747_ = v___x_5758_;
goto v___jp_5746_;
}
else
{
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
return v___x_5785_;
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec(v_a_5755_);
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
v_a_5786_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5756_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5756_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
else
{
lean_object* v_a_5794_; lean_object* v___x_5796_; uint8_t v_isShared_5797_; uint8_t v_isSharedCheck_5801_; 
lean_dec(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
v_a_5794_ = lean_ctor_get(v___x_5754_, 0);
v_isSharedCheck_5801_ = !lean_is_exclusive(v___x_5754_);
if (v_isSharedCheck_5801_ == 0)
{
v___x_5796_ = v___x_5754_;
v_isShared_5797_ = v_isSharedCheck_5801_;
goto v_resetjp_5795_;
}
else
{
lean_inc(v_a_5794_);
lean_dec(v___x_5754_);
v___x_5796_ = lean_box(0);
v_isShared_5797_ = v_isSharedCheck_5801_;
goto v_resetjp_5795_;
}
v_resetjp_5795_:
{
lean_object* v___x_5799_; 
if (v_isShared_5797_ == 0)
{
v___x_5799_ = v___x_5796_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_a_5794_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
return v___x_5799_;
}
}
}
}
v___jp_5746_:
{
size_t v___x_5748_; size_t v___x_5749_; 
v___x_5748_ = ((size_t)1ULL);
v___x_5749_ = lean_usize_add(v_i_5737_, v___x_5748_);
v_i_5737_ = v___x_5749_;
v_b_5738_ = v_a_5747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5802_, lean_object* v_sz_5803_, lean_object* v_i_5804_, lean_object* v_b_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_){
_start:
{
size_t v_sz_boxed_5813_; size_t v_i_boxed_5814_; lean_object* v_res_5815_; 
v_sz_boxed_5813_ = lean_unbox_usize(v_sz_5803_);
lean_dec(v_sz_5803_);
v_i_boxed_5814_ = lean_unbox_usize(v_i_5804_);
lean_dec(v_i_5804_);
v_res_5815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5802_, v_sz_boxed_5813_, v_i_boxed_5814_, v_b_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec_ref(v_as_5802_);
return v_res_5815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5816_, size_t v_i_5817_, size_t v_stop_5818_, lean_object* v_b_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_){
_start:
{
uint8_t v___x_5825_; 
v___x_5825_ = lean_usize_dec_eq(v_i_5817_, v_stop_5818_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = lean_array_uget_borrowed(v_as_5816_, v_i_5817_);
lean_inc(v___x_5826_);
v___x_5827_ = l_Lean_MVarId_getType(v___x_5826_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
if (lean_obj_tag(v___x_5827_) == 0)
{
lean_object* v_a_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v_a_5828_ = lean_ctor_get(v___x_5827_, 0);
lean_inc(v_a_5828_);
lean_dec_ref(v___x_5827_);
v___x_5829_ = l_Lean_Expr_mdataExpr_x21(v_a_5828_);
lean_dec(v_a_5828_);
lean_inc(v___x_5826_);
v___x_5830_ = l_Lean_MVarId_setType___redArg(v___x_5826_, v___x_5829_, v___y_5821_);
if (lean_obj_tag(v___x_5830_) == 0)
{
lean_object* v_a_5831_; size_t v___x_5832_; size_t v___x_5833_; 
v_a_5831_ = lean_ctor_get(v___x_5830_, 0);
lean_inc(v_a_5831_);
lean_dec_ref(v___x_5830_);
v___x_5832_ = ((size_t)1ULL);
v___x_5833_ = lean_usize_add(v_i_5817_, v___x_5832_);
v_i_5817_ = v___x_5833_;
v_b_5819_ = v_a_5831_;
goto _start;
}
else
{
return v___x_5830_;
}
}
else
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5842_; 
v_a_5835_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5837_ = v___x_5827_;
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5827_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5838_ == 0)
{
v___x_5840_ = v___x_5837_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
}
else
{
lean_object* v___x_5843_; 
v___x_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5843_, 0, v_b_5819_);
return v___x_5843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5844_, lean_object* v_i_5845_, lean_object* v_stop_5846_, lean_object* v_b_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_){
_start:
{
size_t v_i_boxed_5853_; size_t v_stop_boxed_5854_; lean_object* v_res_5855_; 
v_i_boxed_5853_ = lean_unbox_usize(v_i_5845_);
lean_dec(v_i_5845_);
v_stop_boxed_5854_ = lean_unbox_usize(v_stop_5846_);
lean_dec(v_stop_5846_);
v_res_5855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5844_, v_i_boxed_5853_, v_stop_boxed_5854_, v_b_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec_ref(v_as_5844_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5856_, lean_object* v___x_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_){
_start:
{
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_object* v___x_5865_; size_t v_sz_5866_; size_t v___x_5867_; lean_object* v___x_5868_; 
v___x_5865_ = lean_box(0);
v_sz_5866_ = lean_array_size(v___x_5857_);
v___x_5867_ = ((size_t)0ULL);
v___x_5868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5857_, v_sz_5866_, v___x_5867_, v___x_5865_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_);
lean_dec_ref(v___y_5862_);
lean_dec_ref(v___x_5857_);
if (lean_obj_tag(v___x_5868_) == 0)
{
lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5875_ == 0)
{
lean_object* v_unused_5876_; 
v_unused_5876_ = lean_ctor_get(v___x_5868_, 0);
lean_dec(v_unused_5876_);
v___x_5870_ = v___x_5868_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_dec(v___x_5868_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 0, v___x_5865_);
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v___x_5865_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
else
{
return v___x_5868_;
}
}
else
{
lean_object* v_val_5877_; lean_object* v___x_5879_; uint8_t v_isShared_5880_; uint8_t v_isSharedCheck_5962_; 
v_val_5877_ = lean_ctor_get(v___x_5856_, 0);
v_isSharedCheck_5962_ = !lean_is_exclusive(v___x_5856_);
if (v_isSharedCheck_5962_ == 0)
{
v___x_5879_ = v___x_5856_;
v_isShared_5880_ = v_isSharedCheck_5962_;
goto v_resetjp_5878_;
}
else
{
lean_inc(v_val_5877_);
lean_dec(v___x_5856_);
v___x_5879_ = lean_box(0);
v_isShared_5880_ = v_isSharedCheck_5962_;
goto v_resetjp_5878_;
}
v_resetjp_5878_:
{
lean_object* v_ref_5881_; lean_object* v_tactic_5882_; lean_object* v_fileName_5883_; lean_object* v_fileMap_5884_; lean_object* v_options_5885_; lean_object* v_currRecDepth_5886_; lean_object* v_maxRecDepth_5887_; lean_object* v_ref_5888_; lean_object* v_currNamespace_5889_; lean_object* v_openDecls_5890_; lean_object* v_initHeartbeats_5891_; lean_object* v_maxHeartbeats_5892_; lean_object* v_quotContext_5893_; lean_object* v_currMacroScope_5894_; uint8_t v_diag_5895_; lean_object* v_cancelTk_x3f_5896_; uint8_t v_suppressElabErrors_5897_; lean_object* v_inheritedTraceOptions_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5961_; 
v_ref_5881_ = lean_ctor_get(v_val_5877_, 0);
lean_inc(v_ref_5881_);
v_tactic_5882_ = lean_ctor_get(v_val_5877_, 1);
lean_inc(v_tactic_5882_);
lean_dec(v_val_5877_);
v_fileName_5883_ = lean_ctor_get(v___y_5862_, 0);
v_fileMap_5884_ = lean_ctor_get(v___y_5862_, 1);
v_options_5885_ = lean_ctor_get(v___y_5862_, 2);
v_currRecDepth_5886_ = lean_ctor_get(v___y_5862_, 3);
v_maxRecDepth_5887_ = lean_ctor_get(v___y_5862_, 4);
v_ref_5888_ = lean_ctor_get(v___y_5862_, 5);
v_currNamespace_5889_ = lean_ctor_get(v___y_5862_, 6);
v_openDecls_5890_ = lean_ctor_get(v___y_5862_, 7);
v_initHeartbeats_5891_ = lean_ctor_get(v___y_5862_, 8);
v_maxHeartbeats_5892_ = lean_ctor_get(v___y_5862_, 9);
v_quotContext_5893_ = lean_ctor_get(v___y_5862_, 10);
v_currMacroScope_5894_ = lean_ctor_get(v___y_5862_, 11);
v_diag_5895_ = lean_ctor_get_uint8(v___y_5862_, sizeof(void*)*14);
v_cancelTk_x3f_5896_ = lean_ctor_get(v___y_5862_, 12);
v_suppressElabErrors_5897_ = lean_ctor_get_uint8(v___y_5862_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5898_ = lean_ctor_get(v___y_5862_, 13);
v_isSharedCheck_5961_ = !lean_is_exclusive(v___y_5862_);
if (v_isSharedCheck_5961_ == 0)
{
v___x_5900_ = v___y_5862_;
v_isShared_5901_ = v_isSharedCheck_5961_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_inheritedTraceOptions_5898_);
lean_inc(v_cancelTk_x3f_5896_);
lean_inc(v_currMacroScope_5894_);
lean_inc(v_quotContext_5893_);
lean_inc(v_maxHeartbeats_5892_);
lean_inc(v_initHeartbeats_5891_);
lean_inc(v_openDecls_5890_);
lean_inc(v_currNamespace_5889_);
lean_inc(v_ref_5888_);
lean_inc(v_maxRecDepth_5887_);
lean_inc(v_currRecDepth_5886_);
lean_inc(v_options_5885_);
lean_inc(v_fileMap_5884_);
lean_inc(v_fileName_5883_);
lean_dec(v___y_5862_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5961_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v_ref_5904_; lean_object* v___x_5906_; 
v___x_5902_ = lean_unsigned_to_nat(0u);
v___x_5903_ = lean_array_get_size(v___x_5857_);
v_ref_5904_ = l_Lean_replaceRef(v_ref_5881_, v_ref_5888_);
lean_dec(v_ref_5888_);
if (v_isShared_5901_ == 0)
{
lean_ctor_set(v___x_5900_, 5, v_ref_5904_);
v___x_5906_ = v___x_5900_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v_fileName_5883_);
lean_ctor_set(v_reuseFailAlloc_5960_, 1, v_fileMap_5884_);
lean_ctor_set(v_reuseFailAlloc_5960_, 2, v_options_5885_);
lean_ctor_set(v_reuseFailAlloc_5960_, 3, v_currRecDepth_5886_);
lean_ctor_set(v_reuseFailAlloc_5960_, 4, v_maxRecDepth_5887_);
lean_ctor_set(v_reuseFailAlloc_5960_, 5, v_ref_5904_);
lean_ctor_set(v_reuseFailAlloc_5960_, 6, v_currNamespace_5889_);
lean_ctor_set(v_reuseFailAlloc_5960_, 7, v_openDecls_5890_);
lean_ctor_set(v_reuseFailAlloc_5960_, 8, v_initHeartbeats_5891_);
lean_ctor_set(v_reuseFailAlloc_5960_, 9, v_maxHeartbeats_5892_);
lean_ctor_set(v_reuseFailAlloc_5960_, 10, v_quotContext_5893_);
lean_ctor_set(v_reuseFailAlloc_5960_, 11, v_currMacroScope_5894_);
lean_ctor_set(v_reuseFailAlloc_5960_, 12, v_cancelTk_x3f_5896_);
lean_ctor_set(v_reuseFailAlloc_5960_, 13, v_inheritedTraceOptions_5898_);
lean_ctor_set_uint8(v_reuseFailAlloc_5960_, sizeof(void*)*14, v_diag_5895_);
lean_ctor_set_uint8(v_reuseFailAlloc_5960_, sizeof(void*)*14 + 1, v_suppressElabErrors_5897_);
v___x_5906_ = v_reuseFailAlloc_5960_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___y_5933_; lean_object* v___y_5950_; uint8_t v___x_5951_; 
v___x_5951_ = lean_nat_dec_lt(v___x_5902_, v___x_5903_);
if (v___x_5951_ == 0)
{
goto v___jp_5934_;
}
else
{
lean_object* v___x_5952_; uint8_t v___x_5953_; 
v___x_5952_ = lean_box(0);
v___x_5953_ = lean_nat_dec_le(v___x_5903_, v___x_5903_);
if (v___x_5953_ == 0)
{
if (v___x_5951_ == 0)
{
goto v___jp_5934_;
}
else
{
size_t v___x_5954_; size_t v___x_5955_; lean_object* v___x_5956_; 
v___x_5954_ = ((size_t)0ULL);
v___x_5955_ = lean_usize_of_nat(v___x_5903_);
v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5857_, v___x_5954_, v___x_5955_, v___x_5952_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
v___y_5950_ = v___x_5956_;
goto v___jp_5949_;
}
}
else
{
size_t v___x_5957_; size_t v___x_5958_; lean_object* v___x_5959_; 
v___x_5957_ = ((size_t)0ULL);
v___x_5958_ = lean_usize_of_nat(v___x_5903_);
v___x_5959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5857_, v___x_5957_, v___x_5958_, v___x_5952_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
v___y_5950_ = v___x_5959_;
goto v___jp_5949_;
}
}
v___jp_5907_:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___f_5911_; lean_object* v___x_5912_; 
v___x_5908_ = lean_box(0);
v___x_5909_ = lean_array_get(v___x_5908_, v___x_5857_, v___x_5902_);
v___x_5910_ = lean_array_to_list(v___x_5857_);
v___f_5911_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5911_, 0, v___x_5910_);
lean_closure_set(v___f_5911_, 1, v_ref_5881_);
lean_closure_set(v___f_5911_, 2, v_tactic_5882_);
lean_inc(v___y_5863_);
lean_inc_ref(v___x_5906_);
lean_inc(v___y_5861_);
lean_inc_ref(v___y_5860_);
v___x_5912_ = l_Lean_Elab_Tactic_run(v___x_5909_, v___f_5911_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
if (lean_obj_tag(v___x_5912_) == 0)
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5923_; 
v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5915_ = v___x_5912_;
v_isShared_5916_ = v_isSharedCheck_5923_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5912_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5923_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
uint8_t v___x_5917_; 
v___x_5917_ = l_List_isEmpty___redArg(v_a_5913_);
if (v___x_5917_ == 0)
{
lean_object* v___x_5918_; 
lean_del_object(v___x_5915_);
v___x_5918_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5913_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
return v___x_5918_;
}
else
{
lean_object* v___x_5919_; lean_object* v___x_5921_; 
lean_dec(v_a_5913_);
lean_dec_ref(v___x_5906_);
lean_dec(v___y_5863_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
v___x_5919_ = lean_box(0);
if (v_isShared_5916_ == 0)
{
lean_ctor_set(v___x_5915_, 0, v___x_5919_);
v___x_5921_ = v___x_5915_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec_ref(v___x_5906_);
lean_dec(v___y_5863_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
v_a_5924_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5912_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5912_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
v___jp_5932_:
{
if (lean_obj_tag(v___y_5933_) == 0)
{
lean_dec_ref(v___y_5933_);
goto v___jp_5907_;
}
else
{
lean_dec_ref(v___x_5906_);
lean_dec(v_tactic_5882_);
lean_dec(v_ref_5881_);
lean_dec(v___y_5863_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec_ref(v___x_5857_);
return v___y_5933_;
}
}
v___jp_5934_:
{
uint8_t v___x_5935_; 
v___x_5935_ = lean_nat_dec_eq(v___x_5903_, v___x_5902_);
if (v___x_5935_ == 0)
{
uint8_t v___x_5936_; 
lean_del_object(v___x_5879_);
v___x_5936_ = lean_nat_dec_lt(v___x_5902_, v___x_5903_);
if (v___x_5936_ == 0)
{
goto v___jp_5907_;
}
else
{
lean_object* v___x_5937_; uint8_t v___x_5938_; 
v___x_5937_ = lean_box(0);
v___x_5938_ = lean_nat_dec_le(v___x_5903_, v___x_5903_);
if (v___x_5938_ == 0)
{
if (v___x_5936_ == 0)
{
goto v___jp_5907_;
}
else
{
size_t v___x_5939_; size_t v___x_5940_; lean_object* v___x_5941_; 
v___x_5939_ = ((size_t)0ULL);
v___x_5940_ = lean_usize_of_nat(v___x_5903_);
v___x_5941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5857_, v___x_5939_, v___x_5940_, v___x_5937_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
v___y_5933_ = v___x_5941_;
goto v___jp_5932_;
}
}
else
{
size_t v___x_5942_; size_t v___x_5943_; lean_object* v___x_5944_; 
v___x_5942_ = ((size_t)0ULL);
v___x_5943_ = lean_usize_of_nat(v___x_5903_);
v___x_5944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5857_, v___x_5942_, v___x_5943_, v___x_5937_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___x_5906_, v___y_5863_);
v___y_5933_ = v___x_5944_;
goto v___jp_5932_;
}
}
}
else
{
lean_object* v___x_5945_; lean_object* v___x_5947_; 
lean_dec_ref(v___x_5906_);
lean_dec(v_tactic_5882_);
lean_dec(v_ref_5881_);
lean_dec(v___y_5863_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec_ref(v___x_5857_);
v___x_5945_ = lean_box(0);
if (v_isShared_5880_ == 0)
{
lean_ctor_set_tag(v___x_5879_, 0);
lean_ctor_set(v___x_5879_, 0, v___x_5945_);
v___x_5947_ = v___x_5879_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v___x_5945_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
v___jp_5949_:
{
if (lean_obj_tag(v___y_5950_) == 0)
{
lean_dec_ref(v___y_5950_);
goto v___jp_5934_;
}
else
{
lean_dec_ref(v___x_5906_);
lean_dec(v_tactic_5882_);
lean_dec(v_ref_5881_);
lean_del_object(v___x_5879_);
lean_dec(v___y_5863_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec_ref(v___x_5857_);
return v___y_5950_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5963_, lean_object* v___x_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_){
_start:
{
lean_object* v_res_5972_; 
v_res_5972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5963_, v___x_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_);
return v_res_5972_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5973_){
_start:
{
uint8_t v___x_5974_; 
v___x_5974_ = 0;
return v___x_5974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5975_){
_start:
{
uint8_t v_res_5976_; lean_object* v_r_5977_; 
v_res_5976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5975_);
lean_dec(v_x_5975_);
v_r_5977_ = lean_box(v_res_5976_);
return v_r_5977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5984_, size_t v_sz_5985_, size_t v_i_5986_, lean_object* v_b_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_){
_start:
{
uint8_t v___x_5993_; 
v___x_5993_ = lean_usize_dec_lt(v_i_5986_, v_sz_5985_);
if (v___x_5993_ == 0)
{
lean_object* v___x_5994_; 
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
v___x_5994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5994_, 0, v_b_5987_);
return v___x_5994_;
}
else
{
lean_object* v_snd_5995_; lean_object* v_fst_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6067_; 
v_snd_5995_ = lean_ctor_get(v_b_5987_, 1);
v_fst_5996_ = lean_ctor_get(v_b_5987_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v_b_5987_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_5998_ = v_b_5987_;
v_isShared_5999_ = v_isSharedCheck_6067_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_snd_5995_);
lean_inc(v_fst_5996_);
lean_dec(v_b_5987_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6067_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v_array_6000_; lean_object* v_start_6001_; lean_object* v_stop_6002_; uint8_t v___x_6003_; 
v_array_6000_ = lean_ctor_get(v_snd_5995_, 0);
v_start_6001_ = lean_ctor_get(v_snd_5995_, 1);
v_stop_6002_ = lean_ctor_get(v_snd_5995_, 2);
v___x_6003_ = lean_nat_dec_lt(v_start_6001_, v_stop_6002_);
if (v___x_6003_ == 0)
{
lean_object* v___x_6005_; 
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
if (v_isShared_5999_ == 0)
{
v___x_6005_ = v___x_5998_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_fst_5996_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v_snd_5995_);
v___x_6005_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
return v___x_6006_;
}
}
else
{
lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6063_; 
lean_inc(v_stop_6002_);
lean_inc(v_start_6001_);
lean_inc_ref(v_array_6000_);
v_isSharedCheck_6063_ = !lean_is_exclusive(v_snd_5995_);
if (v_isSharedCheck_6063_ == 0)
{
lean_object* v_unused_6064_; lean_object* v_unused_6065_; lean_object* v_unused_6066_; 
v_unused_6064_ = lean_ctor_get(v_snd_5995_, 2);
lean_dec(v_unused_6064_);
v_unused_6065_ = lean_ctor_get(v_snd_5995_, 1);
lean_dec(v_unused_6065_);
v_unused_6066_ = lean_ctor_get(v_snd_5995_, 0);
lean_dec(v_unused_6066_);
v___x_6009_ = v_snd_5995_;
v_isShared_6010_ = v_isSharedCheck_6063_;
goto v_resetjp_6008_;
}
else
{
lean_dec(v_snd_5995_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6063_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v_array_6011_; lean_object* v_start_6012_; lean_object* v_stop_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6018_; 
v_array_6011_ = lean_ctor_get(v_fst_5996_, 0);
v_start_6012_ = lean_ctor_get(v_fst_5996_, 1);
v_stop_6013_ = lean_ctor_get(v_fst_5996_, 2);
v___x_6014_ = lean_array_fget(v_array_6000_, v_start_6001_);
v___x_6015_ = lean_unsigned_to_nat(1u);
v___x_6016_ = lean_nat_add(v_start_6001_, v___x_6015_);
lean_dec(v_start_6001_);
if (v_isShared_6010_ == 0)
{
lean_ctor_set(v___x_6009_, 1, v___x_6016_);
v___x_6018_ = v___x_6009_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6062_; 
v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_array_6000_);
lean_ctor_set(v_reuseFailAlloc_6062_, 1, v___x_6016_);
lean_ctor_set(v_reuseFailAlloc_6062_, 2, v_stop_6002_);
v___x_6018_ = v_reuseFailAlloc_6062_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
uint8_t v___x_6019_; 
v___x_6019_ = lean_nat_dec_lt(v_start_6012_, v_stop_6013_);
if (v___x_6019_ == 0)
{
lean_object* v___x_6021_; 
lean_dec(v___x_6014_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 1, v___x_6018_);
v___x_6021_ = v___x_5998_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_fst_5996_);
lean_ctor_set(v_reuseFailAlloc_6023_, 1, v___x_6018_);
v___x_6021_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
lean_object* v___x_6022_; 
v___x_6022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
return v___x_6022_;
}
}
else
{
lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6058_; 
lean_inc(v_stop_6013_);
lean_inc(v_start_6012_);
lean_inc_ref(v_array_6011_);
v_isSharedCheck_6058_ = !lean_is_exclusive(v_fst_5996_);
if (v_isSharedCheck_6058_ == 0)
{
lean_object* v_unused_6059_; lean_object* v_unused_6060_; lean_object* v_unused_6061_; 
v_unused_6059_ = lean_ctor_get(v_fst_5996_, 2);
lean_dec(v_unused_6059_);
v_unused_6060_ = lean_ctor_get(v_fst_5996_, 1);
lean_dec(v_unused_6060_);
v_unused_6061_ = lean_ctor_get(v_fst_5996_, 0);
lean_dec(v_unused_6061_);
v___x_6025_ = v_fst_5996_;
v_isShared_6026_ = v_isSharedCheck_6058_;
goto v_resetjp_6024_;
}
else
{
lean_dec(v_fst_5996_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6058_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___f_6027_; lean_object* v_a_6028_; lean_object* v___x_6029_; lean_object* v___y_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; uint8_t v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___f_6027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_6028_ = lean_array_uget_borrowed(v_as_5984_, v_i_5986_);
v___x_6029_ = lean_array_fget_borrowed(v_array_6011_, v_start_6012_);
lean_inc(v___x_6029_);
v___y_6030_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_6030_, 0, v___x_6014_);
lean_closure_set(v___y_6030_, 1, v___x_6029_);
lean_inc(v_a_6028_);
v___x_6031_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_6031_, 0, lean_box(0));
lean_closure_set(v___x_6031_, 1, v_a_6028_);
lean_closure_set(v___x_6031_, 2, v___y_6030_);
v___x_6032_ = lean_box(0);
v___x_6033_ = lean_box(0);
v___x_6034_ = lean_box(1);
v___x_6035_ = 0;
v___x_6036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_6037_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_6037_, 0, v___x_6032_);
lean_ctor_set(v___x_6037_, 1, v___x_6033_);
lean_ctor_set(v___x_6037_, 2, v___x_6032_);
lean_ctor_set(v___x_6037_, 3, v___f_6027_);
lean_ctor_set(v___x_6037_, 4, v___x_6034_);
lean_ctor_set(v___x_6037_, 5, v___x_6034_);
lean_ctor_set(v___x_6037_, 6, v___x_6032_);
lean_ctor_set(v___x_6037_, 7, v___x_6036_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8, v___x_6019_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 1, v___x_6019_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 2, v___x_6019_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 3, v___x_6019_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 4, v___x_6035_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 5, v___x_6035_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 6, v___x_6035_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 7, v___x_6019_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 8, v___x_6035_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*8 + 9, v___x_6019_);
v___x_6038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
lean_inc(v___y_5991_);
lean_inc_ref(v___y_5990_);
lean_inc(v___y_5989_);
lean_inc_ref(v___y_5988_);
v___x_6039_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_6031_, v___x_6037_, v___x_6038_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
if (lean_obj_tag(v___x_6039_) == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6042_; 
lean_dec_ref(v___x_6039_);
v___x_6040_ = lean_nat_add(v_start_6012_, v___x_6015_);
lean_dec(v_start_6012_);
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 1, v___x_6040_);
v___x_6042_ = v___x_6025_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_array_6011_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6049_, 2, v_stop_6013_);
v___x_6042_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
lean_object* v___x_6044_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 1, v___x_6018_);
lean_ctor_set(v___x_5998_, 0, v___x_6042_);
v___x_6044_ = v___x_5998_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6042_);
lean_ctor_set(v_reuseFailAlloc_6048_, 1, v___x_6018_);
v___x_6044_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
size_t v___x_6045_; size_t v___x_6046_; 
v___x_6045_ = ((size_t)1ULL);
v___x_6046_ = lean_usize_add(v_i_5986_, v___x_6045_);
v_i_5986_ = v___x_6046_;
v_b_5987_ = v___x_6044_;
goto _start;
}
}
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_del_object(v___x_6025_);
lean_dec_ref(v___x_6018_);
lean_dec(v_stop_6013_);
lean_dec(v_start_6012_);
lean_dec_ref(v_array_6011_);
lean_del_object(v___x_5998_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
v_a_6050_ = lean_ctor_get(v___x_6039_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6039_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_6039_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_6039_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_6068_, lean_object* v_sz_6069_, lean_object* v_i_6070_, lean_object* v_b_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
size_t v_sz_boxed_6077_; size_t v_i_boxed_6078_; lean_object* v_res_6079_; 
v_sz_boxed_6077_ = lean_unbox_usize(v_sz_6069_);
lean_dec(v_sz_6069_);
v_i_boxed_6078_ = lean_unbox_usize(v_i_6070_);
lean_dec(v_i_6070_);
v_res_6079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_6068_, v_sz_boxed_6077_, v_i_boxed_6078_, v_b_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_);
lean_dec_ref(v_as_6068_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_6080_, lean_object* v_decrTactics_6081_, lean_object* v_argsPacker_6082_, lean_object* v_funNames_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_){
_start:
{
lean_object* v___x_6089_; 
lean_inc_ref(v_value_6080_);
v___x_6089_ = l_Lean_Meta_getMVarsNoDelayed(v_value_6080_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
if (lean_obj_tag(v___x_6089_) == 0)
{
lean_object* v_a_6090_; lean_object* v___x_6091_; 
v_a_6090_ = lean_ctor_get(v___x_6089_, 0);
lean_inc(v_a_6090_);
lean_dec_ref(v___x_6089_);
lean_inc(v___y_6087_);
lean_inc_ref(v___y_6086_);
lean_inc(v___y_6085_);
lean_inc_ref(v___y_6084_);
v___x_6091_ = l_Lean_Elab_WF_assignSubsumed(v_a_6090_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
lean_dec(v_a_6090_);
if (lean_obj_tag(v___x_6091_) == 0)
{
lean_object* v_a_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; 
v_a_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc(v_a_6092_);
lean_dec_ref(v___x_6091_);
v___x_6093_ = lean_array_get_size(v_decrTactics_6081_);
v___x_6094_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_6082_, v___x_6093_, v_a_6092_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
lean_dec(v_a_6092_);
if (lean_obj_tag(v___x_6094_) == 0)
{
lean_object* v_a_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; size_t v_sz_6101_; size_t v___x_6102_; lean_object* v___x_6103_; 
v_a_6095_ = lean_ctor_get(v___x_6094_, 0);
lean_inc(v_a_6095_);
lean_dec_ref(v___x_6094_);
v___x_6096_ = lean_unsigned_to_nat(0u);
v___x_6097_ = lean_array_get_size(v_a_6095_);
v___x_6098_ = l_Array_toSubarray___redArg(v_a_6095_, v___x_6096_, v___x_6097_);
v___x_6099_ = l_Array_toSubarray___redArg(v_decrTactics_6081_, v___x_6096_, v___x_6093_);
v___x_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6098_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v_sz_6101_ = lean_array_size(v_funNames_6083_);
v___x_6102_ = ((size_t)0ULL);
lean_inc(v___y_6085_);
v___x_6103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_6083_, v_sz_6101_, v___x_6102_, v___x_6100_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v___x_6104_; 
lean_dec_ref(v___x_6103_);
v___x_6104_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_6080_, v___y_6085_);
lean_dec(v___y_6085_);
return v___x_6104_;
}
else
{
lean_object* v_a_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6112_; 
lean_dec(v___y_6085_);
lean_dec_ref(v_value_6080_);
v_a_6105_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6112_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6112_ == 0)
{
v___x_6107_ = v___x_6103_;
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_a_6105_);
lean_dec(v___x_6103_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v___x_6110_; 
if (v_isShared_6108_ == 0)
{
v___x_6110_ = v___x_6107_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_a_6105_);
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
else
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6120_; 
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
lean_dec_ref(v_decrTactics_6081_);
lean_dec_ref(v_value_6080_);
v_a_6113_ = lean_ctor_get(v___x_6094_, 0);
v_isSharedCheck_6120_ = !lean_is_exclusive(v___x_6094_);
if (v_isSharedCheck_6120_ == 0)
{
v___x_6115_ = v___x_6094_;
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6094_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6118_; 
if (v_isShared_6116_ == 0)
{
v___x_6118_ = v___x_6115_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_a_6113_);
v___x_6118_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
return v___x_6118_;
}
}
}
}
else
{
lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6128_; 
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
lean_dec_ref(v_decrTactics_6081_);
lean_dec_ref(v_value_6080_);
v_a_6121_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6128_ == 0)
{
v___x_6123_ = v___x_6091_;
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6091_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6126_; 
if (v_isShared_6124_ == 0)
{
v___x_6126_ = v___x_6123_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
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
else
{
lean_object* v_a_6129_; lean_object* v___x_6131_; uint8_t v_isShared_6132_; uint8_t v_isSharedCheck_6136_; 
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
lean_dec_ref(v_decrTactics_6081_);
lean_dec_ref(v_value_6080_);
v_a_6129_ = lean_ctor_get(v___x_6089_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6089_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6131_ = v___x_6089_;
v_isShared_6132_ = v_isSharedCheck_6136_;
goto v_resetjp_6130_;
}
else
{
lean_inc(v_a_6129_);
lean_dec(v___x_6089_);
v___x_6131_ = lean_box(0);
v_isShared_6132_ = v_isSharedCheck_6136_;
goto v_resetjp_6130_;
}
v_resetjp_6130_:
{
lean_object* v___x_6134_; 
if (v_isShared_6132_ == 0)
{
v___x_6134_ = v___x_6131_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6129_);
v___x_6134_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
return v___x_6134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6137_, lean_object* v_decrTactics_6138_, lean_object* v_argsPacker_6139_, lean_object* v_funNames_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_){
_start:
{
lean_object* v_res_6146_; 
v_res_6146_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6137_, v_decrTactics_6138_, v_argsPacker_6139_, v_funNames_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_);
lean_dec_ref(v_funNames_6140_);
lean_dec_ref(v_argsPacker_6139_);
return v_res_6146_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6147_, uint8_t v_isExporting_6148_, lean_object* v___x_6149_, lean_object* v___y_6150_, lean_object* v___x_6151_, lean_object* v_a_x3f_6152_){
_start:
{
lean_object* v___x_6154_; lean_object* v_env_6155_; lean_object* v_nextMacroScope_6156_; lean_object* v_ngen_6157_; lean_object* v_auxDeclNGen_6158_; lean_object* v_traceState_6159_; lean_object* v_messages_6160_; lean_object* v_infoState_6161_; lean_object* v_snapshotTasks_6162_; lean_object* v___x_6164_; uint8_t v_isShared_6165_; uint8_t v_isSharedCheck_6187_; 
v___x_6154_ = lean_st_ref_take(v___y_6147_);
v_env_6155_ = lean_ctor_get(v___x_6154_, 0);
v_nextMacroScope_6156_ = lean_ctor_get(v___x_6154_, 1);
v_ngen_6157_ = lean_ctor_get(v___x_6154_, 2);
v_auxDeclNGen_6158_ = lean_ctor_get(v___x_6154_, 3);
v_traceState_6159_ = lean_ctor_get(v___x_6154_, 4);
v_messages_6160_ = lean_ctor_get(v___x_6154_, 6);
v_infoState_6161_ = lean_ctor_get(v___x_6154_, 7);
v_snapshotTasks_6162_ = lean_ctor_get(v___x_6154_, 8);
v_isSharedCheck_6187_ = !lean_is_exclusive(v___x_6154_);
if (v_isSharedCheck_6187_ == 0)
{
lean_object* v_unused_6188_; 
v_unused_6188_ = lean_ctor_get(v___x_6154_, 5);
lean_dec(v_unused_6188_);
v___x_6164_ = v___x_6154_;
v_isShared_6165_ = v_isSharedCheck_6187_;
goto v_resetjp_6163_;
}
else
{
lean_inc(v_snapshotTasks_6162_);
lean_inc(v_infoState_6161_);
lean_inc(v_messages_6160_);
lean_inc(v_traceState_6159_);
lean_inc(v_auxDeclNGen_6158_);
lean_inc(v_ngen_6157_);
lean_inc(v_nextMacroScope_6156_);
lean_inc(v_env_6155_);
lean_dec(v___x_6154_);
v___x_6164_ = lean_box(0);
v_isShared_6165_ = v_isSharedCheck_6187_;
goto v_resetjp_6163_;
}
v_resetjp_6163_:
{
lean_object* v___x_6166_; lean_object* v___x_6168_; 
v___x_6166_ = l_Lean_Environment_setExporting(v_env_6155_, v_isExporting_6148_);
if (v_isShared_6165_ == 0)
{
lean_ctor_set(v___x_6164_, 5, v___x_6149_);
lean_ctor_set(v___x_6164_, 0, v___x_6166_);
v___x_6168_ = v___x_6164_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v___x_6166_);
lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_nextMacroScope_6156_);
lean_ctor_set(v_reuseFailAlloc_6186_, 2, v_ngen_6157_);
lean_ctor_set(v_reuseFailAlloc_6186_, 3, v_auxDeclNGen_6158_);
lean_ctor_set(v_reuseFailAlloc_6186_, 4, v_traceState_6159_);
lean_ctor_set(v_reuseFailAlloc_6186_, 5, v___x_6149_);
lean_ctor_set(v_reuseFailAlloc_6186_, 6, v_messages_6160_);
lean_ctor_set(v_reuseFailAlloc_6186_, 7, v_infoState_6161_);
lean_ctor_set(v_reuseFailAlloc_6186_, 8, v_snapshotTasks_6162_);
v___x_6168_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v_mctx_6171_; lean_object* v_zetaDeltaFVarIds_6172_; lean_object* v_postponed_6173_; lean_object* v_diag_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6184_; 
v___x_6169_ = lean_st_ref_set(v___y_6147_, v___x_6168_);
v___x_6170_ = lean_st_ref_take(v___y_6150_);
v_mctx_6171_ = lean_ctor_get(v___x_6170_, 0);
v_zetaDeltaFVarIds_6172_ = lean_ctor_get(v___x_6170_, 2);
v_postponed_6173_ = lean_ctor_get(v___x_6170_, 3);
v_diag_6174_ = lean_ctor_get(v___x_6170_, 4);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6170_);
if (v_isSharedCheck_6184_ == 0)
{
lean_object* v_unused_6185_; 
v_unused_6185_ = lean_ctor_get(v___x_6170_, 1);
lean_dec(v_unused_6185_);
v___x_6176_ = v___x_6170_;
v_isShared_6177_ = v_isSharedCheck_6184_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_diag_6174_);
lean_inc(v_postponed_6173_);
lean_inc(v_zetaDeltaFVarIds_6172_);
lean_inc(v_mctx_6171_);
lean_dec(v___x_6170_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6184_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6179_; 
if (v_isShared_6177_ == 0)
{
lean_ctor_set(v___x_6176_, 1, v___x_6151_);
v___x_6179_ = v___x_6176_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_mctx_6171_);
lean_ctor_set(v_reuseFailAlloc_6183_, 1, v___x_6151_);
lean_ctor_set(v_reuseFailAlloc_6183_, 2, v_zetaDeltaFVarIds_6172_);
lean_ctor_set(v_reuseFailAlloc_6183_, 3, v_postponed_6173_);
lean_ctor_set(v_reuseFailAlloc_6183_, 4, v_diag_6174_);
v___x_6179_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6180_ = lean_st_ref_set(v___y_6150_, v___x_6179_);
v___x_6181_ = lean_box(0);
v___x_6182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
return v___x_6182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6189_, lean_object* v_isExporting_6190_, lean_object* v___x_6191_, lean_object* v___y_6192_, lean_object* v___x_6193_, lean_object* v_a_x3f_6194_, lean_object* v___y_6195_){
_start:
{
uint8_t v_isExporting_boxed_6196_; lean_object* v_res_6197_; 
v_isExporting_boxed_6196_ = lean_unbox(v_isExporting_6190_);
v_res_6197_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6189_, v_isExporting_boxed_6196_, v___x_6191_, v___y_6192_, v___x_6193_, v_a_x3f_6194_);
lean_dec(v_a_x3f_6194_);
lean_dec(v___y_6192_);
lean_dec(v___y_6189_);
return v_res_6197_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6198_; 
v___x_6198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6198_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6199_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
return v___x_6200_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
return v___x_6202_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6203_; lean_object* v___x_6204_; 
v___x_6203_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6204_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6203_);
lean_ctor_set(v___x_6204_, 1, v___x_6203_);
lean_ctor_set(v___x_6204_, 2, v___x_6203_);
lean_ctor_set(v___x_6204_, 3, v___x_6203_);
lean_ctor_set(v___x_6204_, 4, v___x_6203_);
lean_ctor_set(v___x_6204_, 5, v___x_6203_);
return v___x_6204_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6205_, uint8_t v_isExporting_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_){
_start:
{
lean_object* v___x_6212_; lean_object* v_env_6213_; uint8_t v_isExporting_6214_; lean_object* v___x_6215_; lean_object* v_env_6216_; lean_object* v_nextMacroScope_6217_; lean_object* v_ngen_6218_; lean_object* v_auxDeclNGen_6219_; lean_object* v_traceState_6220_; lean_object* v_messages_6221_; lean_object* v_infoState_6222_; lean_object* v_snapshotTasks_6223_; lean_object* v___x_6225_; uint8_t v_isShared_6226_; uint8_t v_isSharedCheck_6277_; 
v___x_6212_ = lean_st_ref_get(v___y_6210_);
v_env_6213_ = lean_ctor_get(v___x_6212_, 0);
lean_inc_ref(v_env_6213_);
lean_dec(v___x_6212_);
v_isExporting_6214_ = lean_ctor_get_uint8(v_env_6213_, sizeof(void*)*8);
lean_dec_ref(v_env_6213_);
v___x_6215_ = lean_st_ref_take(v___y_6210_);
v_env_6216_ = lean_ctor_get(v___x_6215_, 0);
v_nextMacroScope_6217_ = lean_ctor_get(v___x_6215_, 1);
v_ngen_6218_ = lean_ctor_get(v___x_6215_, 2);
v_auxDeclNGen_6219_ = lean_ctor_get(v___x_6215_, 3);
v_traceState_6220_ = lean_ctor_get(v___x_6215_, 4);
v_messages_6221_ = lean_ctor_get(v___x_6215_, 6);
v_infoState_6222_ = lean_ctor_get(v___x_6215_, 7);
v_snapshotTasks_6223_ = lean_ctor_get(v___x_6215_, 8);
v_isSharedCheck_6277_ = !lean_is_exclusive(v___x_6215_);
if (v_isSharedCheck_6277_ == 0)
{
lean_object* v_unused_6278_; 
v_unused_6278_ = lean_ctor_get(v___x_6215_, 5);
lean_dec(v_unused_6278_);
v___x_6225_ = v___x_6215_;
v_isShared_6226_ = v_isSharedCheck_6277_;
goto v_resetjp_6224_;
}
else
{
lean_inc(v_snapshotTasks_6223_);
lean_inc(v_infoState_6222_);
lean_inc(v_messages_6221_);
lean_inc(v_traceState_6220_);
lean_inc(v_auxDeclNGen_6219_);
lean_inc(v_ngen_6218_);
lean_inc(v_nextMacroScope_6217_);
lean_inc(v_env_6216_);
lean_dec(v___x_6215_);
v___x_6225_ = lean_box(0);
v_isShared_6226_ = v_isSharedCheck_6277_;
goto v_resetjp_6224_;
}
v_resetjp_6224_:
{
lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6230_; 
v___x_6227_ = l_Lean_Environment_setExporting(v_env_6216_, v_isExporting_6206_);
v___x_6228_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6226_ == 0)
{
lean_ctor_set(v___x_6225_, 5, v___x_6228_);
lean_ctor_set(v___x_6225_, 0, v___x_6227_);
v___x_6230_ = v___x_6225_;
goto v_reusejp_6229_;
}
else
{
lean_object* v_reuseFailAlloc_6276_; 
v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6276_, 0, v___x_6227_);
lean_ctor_set(v_reuseFailAlloc_6276_, 1, v_nextMacroScope_6217_);
lean_ctor_set(v_reuseFailAlloc_6276_, 2, v_ngen_6218_);
lean_ctor_set(v_reuseFailAlloc_6276_, 3, v_auxDeclNGen_6219_);
lean_ctor_set(v_reuseFailAlloc_6276_, 4, v_traceState_6220_);
lean_ctor_set(v_reuseFailAlloc_6276_, 5, v___x_6228_);
lean_ctor_set(v_reuseFailAlloc_6276_, 6, v_messages_6221_);
lean_ctor_set(v_reuseFailAlloc_6276_, 7, v_infoState_6222_);
lean_ctor_set(v_reuseFailAlloc_6276_, 8, v_snapshotTasks_6223_);
v___x_6230_ = v_reuseFailAlloc_6276_;
goto v_reusejp_6229_;
}
v_reusejp_6229_:
{
lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v_mctx_6233_; lean_object* v_zetaDeltaFVarIds_6234_; lean_object* v_postponed_6235_; lean_object* v_diag_6236_; lean_object* v___x_6238_; uint8_t v_isShared_6239_; uint8_t v_isSharedCheck_6274_; 
v___x_6231_ = lean_st_ref_set(v___y_6210_, v___x_6230_);
v___x_6232_ = lean_st_ref_take(v___y_6208_);
v_mctx_6233_ = lean_ctor_get(v___x_6232_, 0);
v_zetaDeltaFVarIds_6234_ = lean_ctor_get(v___x_6232_, 2);
v_postponed_6235_ = lean_ctor_get(v___x_6232_, 3);
v_diag_6236_ = lean_ctor_get(v___x_6232_, 4);
v_isSharedCheck_6274_ = !lean_is_exclusive(v___x_6232_);
if (v_isSharedCheck_6274_ == 0)
{
lean_object* v_unused_6275_; 
v_unused_6275_ = lean_ctor_get(v___x_6232_, 1);
lean_dec(v_unused_6275_);
v___x_6238_ = v___x_6232_;
v_isShared_6239_ = v_isSharedCheck_6274_;
goto v_resetjp_6237_;
}
else
{
lean_inc(v_diag_6236_);
lean_inc(v_postponed_6235_);
lean_inc(v_zetaDeltaFVarIds_6234_);
lean_inc(v_mctx_6233_);
lean_dec(v___x_6232_);
v___x_6238_ = lean_box(0);
v_isShared_6239_ = v_isSharedCheck_6274_;
goto v_resetjp_6237_;
}
v_resetjp_6237_:
{
lean_object* v___x_6240_; lean_object* v___x_6242_; 
v___x_6240_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6239_ == 0)
{
lean_ctor_set(v___x_6238_, 1, v___x_6240_);
v___x_6242_ = v___x_6238_;
goto v_reusejp_6241_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_mctx_6233_);
lean_ctor_set(v_reuseFailAlloc_6273_, 1, v___x_6240_);
lean_ctor_set(v_reuseFailAlloc_6273_, 2, v_zetaDeltaFVarIds_6234_);
lean_ctor_set(v_reuseFailAlloc_6273_, 3, v_postponed_6235_);
lean_ctor_set(v_reuseFailAlloc_6273_, 4, v_diag_6236_);
v___x_6242_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6241_;
}
v_reusejp_6241_:
{
lean_object* v___x_6243_; lean_object* v_r_6244_; 
v___x_6243_ = lean_st_ref_set(v___y_6208_, v___x_6242_);
lean_inc(v___y_6210_);
lean_inc(v___y_6208_);
v_r_6244_ = lean_apply_5(v_x_6205_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, lean_box(0));
if (lean_obj_tag(v_r_6244_) == 0)
{
lean_object* v_a_6245_; lean_object* v___x_6247_; uint8_t v_isShared_6248_; uint8_t v_isSharedCheck_6261_; 
v_a_6245_ = lean_ctor_get(v_r_6244_, 0);
v_isSharedCheck_6261_ = !lean_is_exclusive(v_r_6244_);
if (v_isSharedCheck_6261_ == 0)
{
v___x_6247_ = v_r_6244_;
v_isShared_6248_ = v_isSharedCheck_6261_;
goto v_resetjp_6246_;
}
else
{
lean_inc(v_a_6245_);
lean_dec(v_r_6244_);
v___x_6247_ = lean_box(0);
v_isShared_6248_ = v_isSharedCheck_6261_;
goto v_resetjp_6246_;
}
v_resetjp_6246_:
{
lean_object* v___x_6250_; 
lean_inc(v_a_6245_);
if (v_isShared_6248_ == 0)
{
lean_ctor_set_tag(v___x_6247_, 1);
v___x_6250_ = v___x_6247_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6260_; 
v_reuseFailAlloc_6260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6245_);
v___x_6250_ = v_reuseFailAlloc_6260_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
lean_object* v___x_6251_; lean_object* v___x_6253_; uint8_t v_isShared_6254_; uint8_t v_isSharedCheck_6258_; 
v___x_6251_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6210_, v_isExporting_6214_, v___x_6228_, v___y_6208_, v___x_6240_, v___x_6250_);
lean_dec_ref(v___x_6250_);
lean_dec(v___y_6208_);
lean_dec(v___y_6210_);
v_isSharedCheck_6258_ = !lean_is_exclusive(v___x_6251_);
if (v_isSharedCheck_6258_ == 0)
{
lean_object* v_unused_6259_; 
v_unused_6259_ = lean_ctor_get(v___x_6251_, 0);
lean_dec(v_unused_6259_);
v___x_6253_ = v___x_6251_;
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
else
{
lean_dec(v___x_6251_);
v___x_6253_ = lean_box(0);
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
v_resetjp_6252_:
{
lean_object* v___x_6256_; 
if (v_isShared_6254_ == 0)
{
lean_ctor_set(v___x_6253_, 0, v_a_6245_);
v___x_6256_ = v___x_6253_;
goto v_reusejp_6255_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_a_6245_);
v___x_6256_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6255_;
}
v_reusejp_6255_:
{
return v___x_6256_;
}
}
}
}
}
else
{
lean_object* v_a_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6271_; 
v_a_6262_ = lean_ctor_get(v_r_6244_, 0);
lean_inc(v_a_6262_);
lean_dec_ref(v_r_6244_);
v___x_6263_ = lean_box(0);
v___x_6264_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6210_, v_isExporting_6214_, v___x_6228_, v___y_6208_, v___x_6240_, v___x_6263_);
lean_dec(v___y_6208_);
lean_dec(v___y_6210_);
v_isSharedCheck_6271_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6271_ == 0)
{
lean_object* v_unused_6272_; 
v_unused_6272_ = lean_ctor_get(v___x_6264_, 0);
lean_dec(v_unused_6272_);
v___x_6266_ = v___x_6264_;
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
else
{
lean_dec(v___x_6264_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6269_; 
if (v_isShared_6267_ == 0)
{
lean_ctor_set_tag(v___x_6266_, 1);
lean_ctor_set(v___x_6266_, 0, v_a_6262_);
v___x_6269_ = v___x_6266_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_a_6262_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6279_, lean_object* v_isExporting_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
uint8_t v_isExporting_boxed_6286_; lean_object* v_res_6287_; 
v_isExporting_boxed_6286_ = lean_unbox(v_isExporting_6280_);
v_res_6287_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6279_, v_isExporting_boxed_6286_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
return v_res_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6288_, uint8_t v_when_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
if (v_when_6289_ == 0)
{
lean_object* v___x_6295_; 
v___x_6295_ = lean_apply_5(v_x_6288_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, lean_box(0));
return v___x_6295_;
}
else
{
uint8_t v___x_6296_; lean_object* v___x_6297_; 
v___x_6296_ = 0;
v___x_6297_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6288_, v___x_6296_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
return v___x_6297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6298_, lean_object* v_when_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
uint8_t v_when_boxed_6305_; lean_object* v_res_6306_; 
v_when_boxed_6305_ = lean_unbox(v_when_6299_);
v_res_6306_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6298_, v_when_boxed_6305_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
return v_res_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6307_, lean_object* v_argsPacker_6308_, lean_object* v_decrTactics_6309_, lean_object* v_value_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_){
_start:
{
lean_object* v___f_6316_; uint8_t v___x_6317_; lean_object* v___x_6318_; 
v___f_6316_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6316_, 0, v_value_6310_);
lean_closure_set(v___f_6316_, 1, v_decrTactics_6309_);
lean_closure_set(v___f_6316_, 2, v_argsPacker_6308_);
lean_closure_set(v___f_6316_, 3, v_funNames_6307_);
v___x_6317_ = 1;
v___x_6318_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6316_, v___x_6317_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_);
return v___x_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6319_, lean_object* v_argsPacker_6320_, lean_object* v_decrTactics_6321_, lean_object* v_value_6322_, lean_object* v_a_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_){
_start:
{
lean_object* v_res_6328_; 
v_res_6328_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6319_, v_argsPacker_6320_, v_decrTactics_6321_, v_value_6322_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_);
return v_res_6328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6329_, lean_object* v_msg_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_){
_start:
{
lean_object* v___x_6338_; 
v___x_6338_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
return v___x_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6339_, lean_object* v_msg_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v_res_6348_; 
v_res_6348_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6339_, v_msg_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
lean_dec(v___y_6346_);
lean_dec_ref(v___y_6345_);
lean_dec(v___y_6344_);
lean_dec_ref(v___y_6343_);
lean_dec(v___y_6342_);
return v_res_6348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_){
_start:
{
lean_object* v___x_6358_; 
v___x_6358_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6356_);
return v___x_6358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_){
_start:
{
lean_object* v_res_6368_; 
v_res_6368_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6359_, v___y_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_);
lean_dec(v___y_6366_);
lean_dec_ref(v___y_6365_);
lean_dec(v___y_6364_);
lean_dec_ref(v___y_6363_);
lean_dec(v___y_6362_);
lean_dec_ref(v___y_6361_);
lean_dec(v___y_6360_);
lean_dec_ref(v___y_6359_);
return v_res_6368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6369_, lean_object* v_x_6370_, lean_object* v_mkInfoTree_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6370_, v_mkInfoTree_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_);
return v___x_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6382_, lean_object* v_x_6383_, lean_object* v_mkInfoTree_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_){
_start:
{
lean_object* v_res_6394_; 
v_res_6394_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6382_, v_x_6383_, v_mkInfoTree_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
return v_res_6394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6395_, size_t v_i_6396_, size_t v_stop_6397_, lean_object* v_b_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_){
_start:
{
lean_object* v___x_6406_; 
v___x_6406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6395_, v_i_6396_, v_stop_6397_, v_b_6398_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_);
return v___x_6406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6407_, lean_object* v_i_6408_, lean_object* v_stop_6409_, lean_object* v_b_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_){
_start:
{
size_t v_i_boxed_6418_; size_t v_stop_boxed_6419_; lean_object* v_res_6420_; 
v_i_boxed_6418_ = lean_unbox_usize(v_i_6408_);
lean_dec(v_i_6408_);
v_stop_boxed_6419_ = lean_unbox_usize(v_stop_6409_);
lean_dec(v_stop_6409_);
v_res_6420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6407_, v_i_boxed_6418_, v_stop_boxed_6419_, v_b_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec_ref(v___y_6413_);
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
lean_dec_ref(v_as_6407_);
return v_res_6420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6421_, lean_object* v_x_6422_, uint8_t v_isExporting_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_){
_start:
{
lean_object* v___x_6429_; 
v___x_6429_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6422_, v_isExporting_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6430_, lean_object* v_x_6431_, lean_object* v_isExporting_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
uint8_t v_isExporting_boxed_6438_; lean_object* v_res_6439_; 
v_isExporting_boxed_6438_ = lean_unbox(v_isExporting_6432_);
v_res_6439_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6430_, v_x_6431_, v_isExporting_boxed_6438_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_);
return v_res_6439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6440_, lean_object* v_x_6441_, uint8_t v_when_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v___x_6448_; 
v___x_6448_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6441_, v_when_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_);
return v___x_6448_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6449_, lean_object* v_x_6450_, lean_object* v_when_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_){
_start:
{
uint8_t v_when_boxed_6457_; lean_object* v_res_6458_; 
v_when_boxed_6457_ = lean_unbox(v_when_6451_);
v_res_6458_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6449_, v_x_6450_, v_when_boxed_6457_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_);
return v_res_6458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6459_, lean_object* v_macroStack_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_){
_start:
{
lean_object* v___x_6468_; 
v___x_6468_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6459_, v_macroStack_6460_, v___y_6465_);
return v___x_6468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6469_, lean_object* v_macroStack_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_){
_start:
{
lean_object* v_res_6478_; 
v_res_6478_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6469_, v_macroStack_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_);
lean_dec(v___y_6476_);
lean_dec_ref(v___y_6475_);
lean_dec(v___y_6474_);
lean_dec_ref(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec_ref(v___y_6471_);
return v_res_6478_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; 
v___x_6485_ = lean_box(0);
v___x_6486_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6487_ = l_Lean_mkConst(v___x_6486_, v___x_6485_);
return v___x_6487_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6492_ = lean_box(0);
v___x_6493_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6494_ = l_Lean_mkConst(v___x_6493_, v___x_6492_);
return v___x_6494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6495_, lean_object* v_a_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_){
_start:
{
lean_object* v___x_6501_; 
v___x_6501_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6495_, v_a_6497_);
if (lean_obj_tag(v___x_6501_) == 0)
{
lean_object* v_a_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6569_; 
v_a_6502_ = lean_ctor_get(v___x_6501_, 0);
v_isSharedCheck_6569_ = !lean_is_exclusive(v___x_6501_);
if (v_isSharedCheck_6569_ == 0)
{
v___x_6504_ = v___x_6501_;
v_isShared_6505_ = v_isSharedCheck_6569_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_a_6502_);
lean_dec(v___x_6501_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6569_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v___x_6511_; uint8_t v___x_6512_; 
v___x_6511_ = l_Lean_Expr_cleanupAnnotations(v_a_6502_);
v___x_6512_ = l_Lean_Expr_isApp(v___x_6511_);
if (v___x_6512_ == 0)
{
lean_dec_ref(v___x_6511_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
goto v___jp_6506_;
}
else
{
lean_object* v_arg_6513_; lean_object* v___x_6514_; uint8_t v___x_6515_; 
v_arg_6513_ = lean_ctor_get(v___x_6511_, 1);
lean_inc_ref(v_arg_6513_);
v___x_6514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6511_);
v___x_6515_ = l_Lean_Expr_isApp(v___x_6514_);
if (v___x_6515_ == 0)
{
lean_dec_ref(v___x_6514_);
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
goto v___jp_6506_;
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
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
goto v___jp_6506_;
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
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
goto v___jp_6506_;
}
else
{
lean_object* v___x_6522_; lean_object* v___x_6523_; uint8_t v___x_6524_; 
v___x_6522_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6520_);
v___x_6523_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6524_ = l_Lean_Expr_isConstOf(v___x_6522_, v___x_6523_);
lean_dec_ref(v___x_6522_);
if (v___x_6524_ == 0)
{
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
goto v___jp_6506_;
}
else
{
lean_object* v___x_6525_; lean_object* v___x_6526_; 
lean_del_object(v___x_6504_);
v___x_6525_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
lean_inc(v_a_6499_);
lean_inc_ref(v_a_6498_);
lean_inc(v_a_6497_);
lean_inc_ref(v_a_6496_);
v___x_6526_ = l_Lean_Meta_isExprDefEq(v_arg_6519_, v___x_6525_, v_a_6496_, v_a_6497_, v_a_6498_, v_a_6499_);
if (lean_obj_tag(v___x_6526_) == 0)
{
lean_object* v_a_6527_; lean_object* v___x_6529_; uint8_t v_isShared_6530_; uint8_t v_isSharedCheck_6560_; 
v_a_6527_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6529_ = v___x_6526_;
v_isShared_6530_ = v_isSharedCheck_6560_;
goto v_resetjp_6528_;
}
else
{
lean_inc(v_a_6527_);
lean_dec(v___x_6526_);
v___x_6529_ = lean_box(0);
v_isShared_6530_ = v_isSharedCheck_6560_;
goto v_resetjp_6528_;
}
v_resetjp_6528_:
{
uint8_t v___x_6531_; 
v___x_6531_ = lean_unbox(v_a_6527_);
lean_dec(v_a_6527_);
if (v___x_6531_ == 0)
{
lean_object* v___x_6532_; lean_object* v___x_6534_; 
lean_dec_ref(v_arg_6516_);
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
v___x_6532_ = lean_box(0);
if (v_isShared_6530_ == 0)
{
lean_ctor_set(v___x_6529_, 0, v___x_6532_);
v___x_6534_ = v___x_6529_;
goto v_reusejp_6533_;
}
else
{
lean_object* v_reuseFailAlloc_6535_; 
v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6532_);
v___x_6534_ = v_reuseFailAlloc_6535_;
goto v_reusejp_6533_;
}
v_reusejp_6533_:
{
return v___x_6534_;
}
}
else
{
lean_object* v___x_6536_; lean_object* v___x_6537_; 
lean_del_object(v___x_6529_);
v___x_6536_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6537_ = l_Lean_Meta_isExprDefEq(v_arg_6513_, v___x_6536_, v_a_6496_, v_a_6497_, v_a_6498_, v_a_6499_);
if (lean_obj_tag(v___x_6537_) == 0)
{
lean_object* v_a_6538_; lean_object* v___x_6540_; uint8_t v_isShared_6541_; uint8_t v_isSharedCheck_6551_; 
v_a_6538_ = lean_ctor_get(v___x_6537_, 0);
v_isSharedCheck_6551_ = !lean_is_exclusive(v___x_6537_);
if (v_isSharedCheck_6551_ == 0)
{
v___x_6540_ = v___x_6537_;
v_isShared_6541_ = v_isSharedCheck_6551_;
goto v_resetjp_6539_;
}
else
{
lean_inc(v_a_6538_);
lean_dec(v___x_6537_);
v___x_6540_ = lean_box(0);
v_isShared_6541_ = v_isSharedCheck_6551_;
goto v_resetjp_6539_;
}
v_resetjp_6539_:
{
uint8_t v___x_6542_; 
v___x_6542_ = lean_unbox(v_a_6538_);
lean_dec(v_a_6538_);
if (v___x_6542_ == 0)
{
lean_object* v___x_6543_; lean_object* v___x_6545_; 
lean_dec_ref(v_arg_6516_);
v___x_6543_ = lean_box(0);
if (v_isShared_6541_ == 0)
{
lean_ctor_set(v___x_6540_, 0, v___x_6543_);
v___x_6545_ = v___x_6540_;
goto v_reusejp_6544_;
}
else
{
lean_object* v_reuseFailAlloc_6546_; 
v_reuseFailAlloc_6546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6546_, 0, v___x_6543_);
v___x_6545_ = v_reuseFailAlloc_6546_;
goto v_reusejp_6544_;
}
v_reusejp_6544_:
{
return v___x_6545_;
}
}
else
{
lean_object* v___x_6547_; lean_object* v___x_6549_; 
v___x_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6547_, 0, v_arg_6516_);
if (v_isShared_6541_ == 0)
{
lean_ctor_set(v___x_6540_, 0, v___x_6547_);
v___x_6549_ = v___x_6540_;
goto v_reusejp_6548_;
}
else
{
lean_object* v_reuseFailAlloc_6550_; 
v_reuseFailAlloc_6550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6550_, 0, v___x_6547_);
v___x_6549_ = v_reuseFailAlloc_6550_;
goto v_reusejp_6548_;
}
v_reusejp_6548_:
{
return v___x_6549_;
}
}
}
}
else
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6559_; 
lean_dec_ref(v_arg_6516_);
v_a_6552_ = lean_ctor_get(v___x_6537_, 0);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6537_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6554_ = v___x_6537_;
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6537_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6557_; 
if (v_isShared_6555_ == 0)
{
v___x_6557_ = v___x_6554_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6552_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
return v___x_6557_;
}
}
}
}
}
}
else
{
lean_object* v_a_6561_; lean_object* v___x_6563_; uint8_t v_isShared_6564_; uint8_t v_isSharedCheck_6568_; 
lean_dec_ref(v_arg_6516_);
lean_dec_ref(v_arg_6513_);
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
v_a_6561_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6568_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6568_ == 0)
{
v___x_6563_ = v___x_6526_;
v_isShared_6564_ = v_isSharedCheck_6568_;
goto v_resetjp_6562_;
}
else
{
lean_inc(v_a_6561_);
lean_dec(v___x_6526_);
v___x_6563_ = lean_box(0);
v_isShared_6564_ = v_isSharedCheck_6568_;
goto v_resetjp_6562_;
}
v_resetjp_6562_:
{
lean_object* v___x_6566_; 
if (v_isShared_6564_ == 0)
{
v___x_6566_ = v___x_6563_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6567_; 
v_reuseFailAlloc_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_a_6561_);
v___x_6566_ = v_reuseFailAlloc_6567_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
return v___x_6566_;
}
}
}
}
}
}
}
}
v___jp_6506_:
{
lean_object* v___x_6507_; lean_object* v___x_6509_; 
v___x_6507_ = lean_box(0);
if (v_isShared_6505_ == 0)
{
lean_ctor_set(v___x_6504_, 0, v___x_6507_);
v___x_6509_ = v___x_6504_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v___x_6507_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
return v___x_6509_;
}
}
}
}
else
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
lean_dec(v_a_6499_);
lean_dec_ref(v_a_6498_);
lean_dec(v_a_6497_);
lean_dec_ref(v_a_6496_);
v_a_6570_ = lean_ctor_get(v___x_6501_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6501_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6501_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6501_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6570_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
return v___x_6575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v_res_6584_; 
v_res_6584_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6585_, lean_object* v_maxFVars_x3f_6586_, lean_object* v_k_6587_, uint8_t v_cleanupAnnotations_6588_, uint8_t v_whnfType_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_){
_start:
{
lean_object* v___f_6597_; lean_object* v___x_6598_; 
v___f_6597_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6597_, 0, v_k_6587_);
lean_closure_set(v___f_6597_, 1, v___y_6590_);
lean_closure_set(v___f_6597_, 2, v___y_6591_);
v___x_6598_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6585_, v_maxFVars_x3f_6586_, v___f_6597_, v_cleanupAnnotations_6588_, v_whnfType_6589_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_);
if (lean_obj_tag(v___x_6598_) == 0)
{
return v___x_6598_;
}
else
{
lean_object* v_a_6599_; lean_object* v___x_6601_; uint8_t v_isShared_6602_; uint8_t v_isSharedCheck_6606_; 
v_a_6599_ = lean_ctor_get(v___x_6598_, 0);
v_isSharedCheck_6606_ = !lean_is_exclusive(v___x_6598_);
if (v_isSharedCheck_6606_ == 0)
{
v___x_6601_ = v___x_6598_;
v_isShared_6602_ = v_isSharedCheck_6606_;
goto v_resetjp_6600_;
}
else
{
lean_inc(v_a_6599_);
lean_dec(v___x_6598_);
v___x_6601_ = lean_box(0);
v_isShared_6602_ = v_isSharedCheck_6606_;
goto v_resetjp_6600_;
}
v_resetjp_6600_:
{
lean_object* v___x_6604_; 
if (v_isShared_6602_ == 0)
{
v___x_6604_ = v___x_6601_;
goto v_reusejp_6603_;
}
else
{
lean_object* v_reuseFailAlloc_6605_; 
v_reuseFailAlloc_6605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6605_, 0, v_a_6599_);
v___x_6604_ = v_reuseFailAlloc_6605_;
goto v_reusejp_6603_;
}
v_reusejp_6603_:
{
return v___x_6604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6607_, lean_object* v_maxFVars_x3f_6608_, lean_object* v_k_6609_, lean_object* v_cleanupAnnotations_6610_, lean_object* v_whnfType_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6619_; uint8_t v_whnfType_boxed_6620_; lean_object* v_res_6621_; 
v_cleanupAnnotations_boxed_6619_ = lean_unbox(v_cleanupAnnotations_6610_);
v_whnfType_boxed_6620_ = lean_unbox(v_whnfType_6611_);
v_res_6621_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6607_, v_maxFVars_x3f_6608_, v_k_6609_, v_cleanupAnnotations_boxed_6619_, v_whnfType_boxed_6620_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
return v_res_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6622_, lean_object* v_type_6623_, lean_object* v_maxFVars_x3f_6624_, lean_object* v_k_6625_, uint8_t v_cleanupAnnotations_6626_, uint8_t v_whnfType_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_){
_start:
{
lean_object* v___x_6635_; 
v___x_6635_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6623_, v_maxFVars_x3f_6624_, v_k_6625_, v_cleanupAnnotations_6626_, v_whnfType_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_, v___y_6632_, v___y_6633_);
return v___x_6635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6636_, lean_object* v_type_6637_, lean_object* v_maxFVars_x3f_6638_, lean_object* v_k_6639_, lean_object* v_cleanupAnnotations_6640_, lean_object* v_whnfType_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_, lean_object* v___y_6647_, lean_object* v___y_6648_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6649_; uint8_t v_whnfType_boxed_6650_; lean_object* v_res_6651_; 
v_cleanupAnnotations_boxed_6649_ = lean_unbox(v_cleanupAnnotations_6640_);
v_whnfType_boxed_6650_ = lean_unbox(v_whnfType_6641_);
v_res_6651_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6636_, v_type_6637_, v_maxFVars_x3f_6638_, v_k_6639_, v_cleanupAnnotations_boxed_6649_, v_whnfType_boxed_6650_, v___y_6642_, v___y_6643_, v___y_6644_, v___y_6645_, v___y_6646_, v___y_6647_);
return v_res_6651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6652_, lean_object* v_x_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_){
_start:
{
lean_object* v_keyedConfig_6661_; uint8_t v_trackZetaDelta_6662_; lean_object* v_zetaDeltaSet_6663_; lean_object* v_localInstances_6664_; lean_object* v_defEqCtx_x3f_6665_; lean_object* v_synthPendingDepth_6666_; lean_object* v_canUnfold_x3f_6667_; uint8_t v_univApprox_6668_; uint8_t v_inTypeClassResolution_6669_; uint8_t v_cacheInferType_6670_; lean_object* v___x_6672_; uint8_t v_isShared_6673_; uint8_t v_isSharedCheck_6686_; 
v_keyedConfig_6661_ = lean_ctor_get(v___y_6656_, 0);
v_trackZetaDelta_6662_ = lean_ctor_get_uint8(v___y_6656_, sizeof(void*)*7);
v_zetaDeltaSet_6663_ = lean_ctor_get(v___y_6656_, 1);
v_localInstances_6664_ = lean_ctor_get(v___y_6656_, 3);
v_defEqCtx_x3f_6665_ = lean_ctor_get(v___y_6656_, 4);
v_synthPendingDepth_6666_ = lean_ctor_get(v___y_6656_, 5);
v_canUnfold_x3f_6667_ = lean_ctor_get(v___y_6656_, 6);
v_univApprox_6668_ = lean_ctor_get_uint8(v___y_6656_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6669_ = lean_ctor_get_uint8(v___y_6656_, sizeof(void*)*7 + 2);
v_cacheInferType_6670_ = lean_ctor_get_uint8(v___y_6656_, sizeof(void*)*7 + 3);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___y_6656_);
if (v_isSharedCheck_6686_ == 0)
{
lean_object* v_unused_6687_; 
v_unused_6687_ = lean_ctor_get(v___y_6656_, 2);
lean_dec(v_unused_6687_);
v___x_6672_ = v___y_6656_;
v_isShared_6673_ = v_isSharedCheck_6686_;
goto v_resetjp_6671_;
}
else
{
lean_inc(v_canUnfold_x3f_6667_);
lean_inc(v_synthPendingDepth_6666_);
lean_inc(v_defEqCtx_x3f_6665_);
lean_inc(v_localInstances_6664_);
lean_inc(v_zetaDeltaSet_6663_);
lean_inc(v_keyedConfig_6661_);
lean_dec(v___y_6656_);
v___x_6672_ = lean_box(0);
v_isShared_6673_ = v_isSharedCheck_6686_;
goto v_resetjp_6671_;
}
v_resetjp_6671_:
{
lean_object* v___x_6675_; 
if (v_isShared_6673_ == 0)
{
lean_ctor_set(v___x_6672_, 2, v_lctx_6652_);
v___x_6675_ = v___x_6672_;
goto v_reusejp_6674_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_keyedConfig_6661_);
lean_ctor_set(v_reuseFailAlloc_6685_, 1, v_zetaDeltaSet_6663_);
lean_ctor_set(v_reuseFailAlloc_6685_, 2, v_lctx_6652_);
lean_ctor_set(v_reuseFailAlloc_6685_, 3, v_localInstances_6664_);
lean_ctor_set(v_reuseFailAlloc_6685_, 4, v_defEqCtx_x3f_6665_);
lean_ctor_set(v_reuseFailAlloc_6685_, 5, v_synthPendingDepth_6666_);
lean_ctor_set(v_reuseFailAlloc_6685_, 6, v_canUnfold_x3f_6667_);
lean_ctor_set_uint8(v_reuseFailAlloc_6685_, sizeof(void*)*7, v_trackZetaDelta_6662_);
lean_ctor_set_uint8(v_reuseFailAlloc_6685_, sizeof(void*)*7 + 1, v_univApprox_6668_);
lean_ctor_set_uint8(v_reuseFailAlloc_6685_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6669_);
lean_ctor_set_uint8(v_reuseFailAlloc_6685_, sizeof(void*)*7 + 3, v_cacheInferType_6670_);
v___x_6675_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6674_;
}
v_reusejp_6674_:
{
lean_object* v___x_6676_; 
v___x_6676_ = lean_apply_7(v_x_6653_, v___y_6654_, v___y_6655_, v___x_6675_, v___y_6657_, v___y_6658_, v___y_6659_, lean_box(0));
if (lean_obj_tag(v___x_6676_) == 0)
{
lean_object* v_a_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6684_; 
v_a_6677_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6684_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6684_ == 0)
{
v___x_6679_ = v___x_6676_;
v_isShared_6680_ = v_isSharedCheck_6684_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_a_6677_);
lean_dec(v___x_6676_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6684_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___x_6682_; 
if (v_isShared_6680_ == 0)
{
v___x_6682_ = v___x_6679_;
goto v_reusejp_6681_;
}
else
{
lean_object* v_reuseFailAlloc_6683_; 
v_reuseFailAlloc_6683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6683_, 0, v_a_6677_);
v___x_6682_ = v_reuseFailAlloc_6683_;
goto v_reusejp_6681_;
}
v_reusejp_6681_:
{
return v___x_6682_;
}
}
}
else
{
return v___x_6676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6688_, lean_object* v_x_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_, lean_object* v___y_6694_, lean_object* v___y_6695_, lean_object* v___y_6696_){
_start:
{
lean_object* v_res_6697_; 
v_res_6697_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6688_, v_x_6689_, v___y_6690_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_);
return v_res_6697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6698_, lean_object* v_lctx_6699_, lean_object* v_x_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_){
_start:
{
lean_object* v___x_6708_; 
v___x_6708_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6699_, v_x_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_, v___y_6706_);
return v___x_6708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6709_, lean_object* v_lctx_6710_, lean_object* v_x_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_){
_start:
{
lean_object* v_res_6719_; 
v_res_6719_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6709_, v_lctx_6710_, v_x_6711_, v___y_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_);
return v_res_6719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6736_, lean_object* v___x_6737_, lean_object* v_wfRel_6738_, lean_object* v_x_6739_, lean_object* v_type_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_){
_start:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; 
v___x_6748_ = lean_unsigned_to_nat(0u);
v___x_6749_ = lean_array_get_borrowed(v___x_6736_, v_x_6739_, v___x_6748_);
v___x_6750_ = l_Lean_Expr_fvarId_x21(v___x_6749_);
lean_inc_ref(v___y_6743_);
v___x_6751_ = l_Lean_FVarId_getUserName___redArg(v___x_6750_, v___y_6743_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6751_) == 0)
{
lean_object* v_a_6752_; lean_object* v___x_6753_; 
v_a_6752_ = lean_ctor_get(v___x_6751_, 0);
lean_inc(v_a_6752_);
lean_dec_ref(v___x_6751_);
lean_inc(v___y_6746_);
lean_inc_ref(v___y_6745_);
lean_inc(v___y_6744_);
lean_inc_ref(v___y_6743_);
lean_inc(v___x_6749_);
v___x_6753_ = lean_infer_type(v___x_6749_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6753_) == 0)
{
lean_object* v_a_6754_; lean_object* v___x_6755_; 
v_a_6754_ = lean_ctor_get(v___x_6753_, 0);
lean_inc(v_a_6754_);
lean_dec_ref(v___x_6753_);
lean_inc(v___y_6746_);
lean_inc_ref(v___y_6745_);
lean_inc(v___y_6744_);
lean_inc_ref(v___y_6743_);
lean_inc(v_a_6754_);
v___x_6755_ = l_Lean_Meta_getLevel(v_a_6754_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6755_) == 0)
{
lean_object* v_a_6756_; lean_object* v___x_6757_; 
v_a_6756_ = lean_ctor_get(v___x_6755_, 0);
lean_inc(v_a_6756_);
lean_dec_ref(v___x_6755_);
lean_inc(v___y_6746_);
lean_inc_ref(v___y_6745_);
lean_inc(v___y_6744_);
lean_inc_ref(v___y_6743_);
lean_inc_ref(v_type_6740_);
v___x_6757_ = l_Lean_Meta_getLevel(v_type_6740_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6757_) == 0)
{
lean_object* v_a_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; uint8_t v___x_6761_; uint8_t v___x_6762_; uint8_t v___x_6763_; lean_object* v___x_6764_; 
v_a_6758_ = lean_ctor_get(v___x_6757_, 0);
lean_inc(v_a_6758_);
lean_dec_ref(v___x_6757_);
v___x_6759_ = lean_mk_empty_array_with_capacity(v___x_6737_);
lean_inc(v___x_6749_);
lean_inc_ref(v___x_6759_);
v___x_6760_ = lean_array_push(v___x_6759_, v___x_6749_);
v___x_6761_ = 0;
v___x_6762_ = 1;
v___x_6763_ = 1;
v___x_6764_ = l_Lean_Meta_mkLambdaFVars(v___x_6760_, v_type_6740_, v___x_6761_, v___x_6762_, v___x_6761_, v___x_6762_, v___x_6763_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
lean_dec_ref(v___x_6760_);
if (lean_obj_tag(v___x_6764_) == 0)
{
lean_object* v_a_6765_; lean_object* v___x_6766_; 
v_a_6765_ = lean_ctor_get(v___x_6764_, 0);
lean_inc(v_a_6765_);
lean_dec_ref(v___x_6764_);
lean_inc(v___y_6746_);
lean_inc_ref(v___y_6745_);
lean_inc(v___y_6744_);
lean_inc_ref(v___y_6743_);
lean_inc_ref(v_wfRel_6738_);
v___x_6766_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6738_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6766_) == 0)
{
lean_object* v_a_6767_; lean_object* v___x_6769_; uint8_t v_isShared_6770_; uint8_t v_isSharedCheck_6811_; 
v_a_6767_ = lean_ctor_get(v___x_6766_, 0);
v_isSharedCheck_6811_ = !lean_is_exclusive(v___x_6766_);
if (v_isSharedCheck_6811_ == 0)
{
v___x_6769_ = v___x_6766_;
v_isShared_6770_ = v_isSharedCheck_6811_;
goto v_resetjp_6768_;
}
else
{
lean_inc(v_a_6767_);
lean_dec(v___x_6766_);
v___x_6769_ = lean_box(0);
v_isShared_6770_ = v_isSharedCheck_6811_;
goto v_resetjp_6768_;
}
v_resetjp_6768_:
{
if (lean_obj_tag(v_a_6767_) == 1)
{
lean_object* v_val_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6780_; 
lean_dec_ref(v___x_6759_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_val_6771_ = lean_ctor_get(v_a_6767_, 0);
lean_inc(v_val_6771_);
lean_dec_ref(v_a_6767_);
v___x_6772_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6773_ = lean_box(0);
v___x_6774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6774_, 0, v_a_6758_);
lean_ctor_set(v___x_6774_, 1, v___x_6773_);
v___x_6775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6775_, 0, v_a_6756_);
lean_ctor_set(v___x_6775_, 1, v___x_6774_);
v___x_6776_ = l_Lean_mkConst(v___x_6772_, v___x_6775_);
v___x_6777_ = l_Lean_mkApp3(v___x_6776_, v_a_6754_, v_a_6765_, v_val_6771_);
v___x_6778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6778_, 0, v___x_6777_);
lean_ctor_set(v___x_6778_, 1, v_a_6752_);
if (v_isShared_6770_ == 0)
{
lean_ctor_set(v___x_6769_, 0, v___x_6778_);
v___x_6780_ = v___x_6769_;
goto v_reusejp_6779_;
}
else
{
lean_object* v_reuseFailAlloc_6781_; 
v_reuseFailAlloc_6781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6781_, 0, v___x_6778_);
v___x_6780_ = v_reuseFailAlloc_6781_;
goto v_reusejp_6779_;
}
v_reusejp_6779_:
{
return v___x_6780_;
}
}
else
{
lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___x_6787_; 
lean_del_object(v___x_6769_);
lean_dec(v_a_6767_);
v___x_6782_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6738_);
v___x_6783_ = l_Lean_mkProj(v___x_6782_, v___x_6748_, v_wfRel_6738_);
v___x_6784_ = l_Lean_mkProj(v___x_6782_, v___x_6737_, v_wfRel_6738_);
v___x_6785_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6786_ = lean_array_push(v___x_6759_, v___x_6784_);
v___x_6787_ = l_Lean_Meta_mkAppM(v___x_6785_, v___x_6786_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
if (lean_obj_tag(v___x_6787_) == 0)
{
lean_object* v_a_6788_; lean_object* v___x_6790_; uint8_t v_isShared_6791_; uint8_t v_isSharedCheck_6802_; 
v_a_6788_ = lean_ctor_get(v___x_6787_, 0);
v_isSharedCheck_6802_ = !lean_is_exclusive(v___x_6787_);
if (v_isSharedCheck_6802_ == 0)
{
v___x_6790_ = v___x_6787_;
v_isShared_6791_ = v_isSharedCheck_6802_;
goto v_resetjp_6789_;
}
else
{
lean_inc(v_a_6788_);
lean_dec(v___x_6787_);
v___x_6790_ = lean_box(0);
v_isShared_6791_ = v_isSharedCheck_6802_;
goto v_resetjp_6789_;
}
v_resetjp_6789_:
{
lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___x_6800_; 
v___x_6792_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6793_ = lean_box(0);
v___x_6794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6794_, 0, v_a_6758_);
lean_ctor_set(v___x_6794_, 1, v___x_6793_);
v___x_6795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6795_, 0, v_a_6756_);
lean_ctor_set(v___x_6795_, 1, v___x_6794_);
v___x_6796_ = l_Lean_mkConst(v___x_6792_, v___x_6795_);
v___x_6797_ = l_Lean_mkApp4(v___x_6796_, v_a_6754_, v_a_6765_, v___x_6783_, v_a_6788_);
v___x_6798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6798_, 0, v___x_6797_);
lean_ctor_set(v___x_6798_, 1, v_a_6752_);
if (v_isShared_6791_ == 0)
{
lean_ctor_set(v___x_6790_, 0, v___x_6798_);
v___x_6800_ = v___x_6790_;
goto v_reusejp_6799_;
}
else
{
lean_object* v_reuseFailAlloc_6801_; 
v_reuseFailAlloc_6801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6801_, 0, v___x_6798_);
v___x_6800_ = v_reuseFailAlloc_6801_;
goto v_reusejp_6799_;
}
v_reusejp_6799_:
{
return v___x_6800_;
}
}
}
else
{
lean_object* v_a_6803_; lean_object* v___x_6805_; uint8_t v_isShared_6806_; uint8_t v_isSharedCheck_6810_; 
lean_dec_ref(v___x_6783_);
lean_dec(v_a_6765_);
lean_dec(v_a_6758_);
lean_dec(v_a_6756_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
v_a_6803_ = lean_ctor_get(v___x_6787_, 0);
v_isSharedCheck_6810_ = !lean_is_exclusive(v___x_6787_);
if (v_isSharedCheck_6810_ == 0)
{
v___x_6805_ = v___x_6787_;
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
else
{
lean_inc(v_a_6803_);
lean_dec(v___x_6787_);
v___x_6805_ = lean_box(0);
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
v_resetjp_6804_:
{
lean_object* v___x_6808_; 
if (v_isShared_6806_ == 0)
{
v___x_6808_ = v___x_6805_;
goto v_reusejp_6807_;
}
else
{
lean_object* v_reuseFailAlloc_6809_; 
v_reuseFailAlloc_6809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6809_, 0, v_a_6803_);
v___x_6808_ = v_reuseFailAlloc_6809_;
goto v_reusejp_6807_;
}
v_reusejp_6807_:
{
return v___x_6808_;
}
}
}
}
}
}
else
{
lean_object* v_a_6812_; lean_object* v___x_6814_; uint8_t v_isShared_6815_; uint8_t v_isSharedCheck_6819_; 
lean_dec(v_a_6765_);
lean_dec_ref(v___x_6759_);
lean_dec(v_a_6758_);
lean_dec(v_a_6756_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6812_ = lean_ctor_get(v___x_6766_, 0);
v_isSharedCheck_6819_ = !lean_is_exclusive(v___x_6766_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6814_ = v___x_6766_;
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
else
{
lean_inc(v_a_6812_);
lean_dec(v___x_6766_);
v___x_6814_ = lean_box(0);
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
v_resetjp_6813_:
{
lean_object* v___x_6817_; 
if (v_isShared_6815_ == 0)
{
v___x_6817_ = v___x_6814_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_a_6812_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
}
else
{
lean_object* v_a_6820_; lean_object* v___x_6822_; uint8_t v_isShared_6823_; uint8_t v_isSharedCheck_6827_; 
lean_dec_ref(v___x_6759_);
lean_dec(v_a_6758_);
lean_dec(v_a_6756_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6820_ = lean_ctor_get(v___x_6764_, 0);
v_isSharedCheck_6827_ = !lean_is_exclusive(v___x_6764_);
if (v_isSharedCheck_6827_ == 0)
{
v___x_6822_ = v___x_6764_;
v_isShared_6823_ = v_isSharedCheck_6827_;
goto v_resetjp_6821_;
}
else
{
lean_inc(v_a_6820_);
lean_dec(v___x_6764_);
v___x_6822_ = lean_box(0);
v_isShared_6823_ = v_isSharedCheck_6827_;
goto v_resetjp_6821_;
}
v_resetjp_6821_:
{
lean_object* v___x_6825_; 
if (v_isShared_6823_ == 0)
{
v___x_6825_ = v___x_6822_;
goto v_reusejp_6824_;
}
else
{
lean_object* v_reuseFailAlloc_6826_; 
v_reuseFailAlloc_6826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_a_6820_);
v___x_6825_ = v_reuseFailAlloc_6826_;
goto v_reusejp_6824_;
}
v_reusejp_6824_:
{
return v___x_6825_;
}
}
}
}
else
{
lean_object* v_a_6828_; lean_object* v___x_6830_; uint8_t v_isShared_6831_; uint8_t v_isSharedCheck_6835_; 
lean_dec(v_a_6756_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_type_6740_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6828_ = lean_ctor_get(v___x_6757_, 0);
v_isSharedCheck_6835_ = !lean_is_exclusive(v___x_6757_);
if (v_isSharedCheck_6835_ == 0)
{
v___x_6830_ = v___x_6757_;
v_isShared_6831_ = v_isSharedCheck_6835_;
goto v_resetjp_6829_;
}
else
{
lean_inc(v_a_6828_);
lean_dec(v___x_6757_);
v___x_6830_ = lean_box(0);
v_isShared_6831_ = v_isSharedCheck_6835_;
goto v_resetjp_6829_;
}
v_resetjp_6829_:
{
lean_object* v___x_6833_; 
if (v_isShared_6831_ == 0)
{
v___x_6833_ = v___x_6830_;
goto v_reusejp_6832_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v_a_6828_);
v___x_6833_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6832_;
}
v_reusejp_6832_:
{
return v___x_6833_;
}
}
}
}
else
{
lean_object* v_a_6836_; lean_object* v___x_6838_; uint8_t v_isShared_6839_; uint8_t v_isSharedCheck_6843_; 
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_type_6740_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6836_ = lean_ctor_get(v___x_6755_, 0);
v_isSharedCheck_6843_ = !lean_is_exclusive(v___x_6755_);
if (v_isSharedCheck_6843_ == 0)
{
v___x_6838_ = v___x_6755_;
v_isShared_6839_ = v_isSharedCheck_6843_;
goto v_resetjp_6837_;
}
else
{
lean_inc(v_a_6836_);
lean_dec(v___x_6755_);
v___x_6838_ = lean_box(0);
v_isShared_6839_ = v_isSharedCheck_6843_;
goto v_resetjp_6837_;
}
v_resetjp_6837_:
{
lean_object* v___x_6841_; 
if (v_isShared_6839_ == 0)
{
v___x_6841_ = v___x_6838_;
goto v_reusejp_6840_;
}
else
{
lean_object* v_reuseFailAlloc_6842_; 
v_reuseFailAlloc_6842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6842_, 0, v_a_6836_);
v___x_6841_ = v_reuseFailAlloc_6842_;
goto v_reusejp_6840_;
}
v_reusejp_6840_:
{
return v___x_6841_;
}
}
}
}
else
{
lean_object* v_a_6844_; lean_object* v___x_6846_; uint8_t v_isShared_6847_; uint8_t v_isSharedCheck_6851_; 
lean_dec(v_a_6752_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_type_6740_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6844_ = lean_ctor_get(v___x_6753_, 0);
v_isSharedCheck_6851_ = !lean_is_exclusive(v___x_6753_);
if (v_isSharedCheck_6851_ == 0)
{
v___x_6846_ = v___x_6753_;
v_isShared_6847_ = v_isSharedCheck_6851_;
goto v_resetjp_6845_;
}
else
{
lean_inc(v_a_6844_);
lean_dec(v___x_6753_);
v___x_6846_ = lean_box(0);
v_isShared_6847_ = v_isSharedCheck_6851_;
goto v_resetjp_6845_;
}
v_resetjp_6845_:
{
lean_object* v___x_6849_; 
if (v_isShared_6847_ == 0)
{
v___x_6849_ = v___x_6846_;
goto v_reusejp_6848_;
}
else
{
lean_object* v_reuseFailAlloc_6850_; 
v_reuseFailAlloc_6850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6850_, 0, v_a_6844_);
v___x_6849_ = v_reuseFailAlloc_6850_;
goto v_reusejp_6848_;
}
v_reusejp_6848_:
{
return v___x_6849_;
}
}
}
}
else
{
lean_object* v_a_6852_; lean_object* v___x_6854_; uint8_t v_isShared_6855_; uint8_t v_isSharedCheck_6859_; 
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
lean_dec_ref(v_type_6740_);
lean_dec_ref(v_wfRel_6738_);
lean_dec(v___x_6737_);
v_a_6852_ = lean_ctor_get(v___x_6751_, 0);
v_isSharedCheck_6859_ = !lean_is_exclusive(v___x_6751_);
if (v_isSharedCheck_6859_ == 0)
{
v___x_6854_ = v___x_6751_;
v_isShared_6855_ = v_isSharedCheck_6859_;
goto v_resetjp_6853_;
}
else
{
lean_inc(v_a_6852_);
lean_dec(v___x_6751_);
v___x_6854_ = lean_box(0);
v_isShared_6855_ = v_isSharedCheck_6859_;
goto v_resetjp_6853_;
}
v_resetjp_6853_:
{
lean_object* v___x_6857_; 
if (v_isShared_6855_ == 0)
{
v___x_6857_ = v___x_6854_;
goto v_reusejp_6856_;
}
else
{
lean_object* v_reuseFailAlloc_6858_; 
v_reuseFailAlloc_6858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6858_, 0, v_a_6852_);
v___x_6857_ = v_reuseFailAlloc_6858_;
goto v_reusejp_6856_;
}
v_reusejp_6856_:
{
return v___x_6857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6860_, lean_object* v___x_6861_, lean_object* v_wfRel_6862_, lean_object* v_x_6863_, lean_object* v_type_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_, lean_object* v___y_6870_, lean_object* v___y_6871_){
_start:
{
lean_object* v_res_6872_; 
v_res_6872_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6860_, v___x_6861_, v_wfRel_6862_, v_x_6863_, v_type_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_);
lean_dec(v___y_6866_);
lean_dec_ref(v___y_6865_);
lean_dec_ref(v_x_6863_);
return v_res_6872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6873_, lean_object* v_declName_6874_, lean_object* v_x_6875_, lean_object* v_F_6876_, lean_object* v_val_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_){
_start:
{
lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; 
v___x_6885_ = lean_array_get_size(v_prefixArgs_6873_);
v___x_6886_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6886_, 0, v_declName_6874_);
lean_closure_set(v___x_6886_, 1, v___x_6885_);
v___x_6887_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6875_, v_F_6876_, v_val_6877_, v___x_6886_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_);
return v___x_6887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6888_, lean_object* v_declName_6889_, lean_object* v_x_6890_, lean_object* v_F_6891_, lean_object* v_val_6892_, lean_object* v___y_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_){
_start:
{
lean_object* v_res_6900_; 
v_res_6900_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6888_, v_declName_6889_, v_x_6890_, v_F_6891_, v_val_6892_, v___y_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
lean_dec_ref(v_prefixArgs_6888_);
return v_res_6900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6901_, lean_object* v___x_6902_, lean_object* v___x_6903_, lean_object* v___f_6904_, lean_object* v_funNames_6905_, lean_object* v_argsPacker_6906_, lean_object* v_decrTactics_6907_, uint8_t v___x_6908_, lean_object* v_fst_6909_, lean_object* v_prefixArgs_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_){
_start:
{
lean_object* v___x_6918_; 
lean_inc(v___y_6916_);
lean_inc_ref(v___y_6915_);
lean_inc(v___y_6914_);
lean_inc_ref(v___y_6913_);
lean_inc_ref(v___x_6902_);
lean_inc_ref(v___x_6901_);
v___x_6918_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6901_, v___x_6902_, v___x_6903_, v___f_6904_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_);
if (lean_obj_tag(v___x_6918_) == 0)
{
lean_object* v_a_6919_; lean_object* v___x_6920_; 
v_a_6919_ = lean_ctor_get(v___x_6918_, 0);
lean_inc(v_a_6919_);
lean_dec_ref(v___x_6918_);
lean_inc(v___y_6916_);
lean_inc_ref(v___y_6915_);
lean_inc(v___y_6914_);
lean_inc_ref(v___y_6913_);
v___x_6920_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6905_, v_argsPacker_6906_, v_decrTactics_6907_, v_a_6919_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v_a_6921_; lean_object* v___x_6922_; lean_object* v___x_6923_; lean_object* v___x_6924_; lean_object* v___x_6925_; uint8_t v___x_6926_; uint8_t v___x_6927_; lean_object* v___x_6928_; 
v_a_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_a_6921_);
lean_dec_ref(v___x_6920_);
v___x_6922_ = lean_unsigned_to_nat(2u);
v___x_6923_ = lean_mk_empty_array_with_capacity(v___x_6922_);
v___x_6924_ = lean_array_push(v___x_6923_, v___x_6901_);
v___x_6925_ = lean_array_push(v___x_6924_, v___x_6902_);
v___x_6926_ = 1;
v___x_6927_ = 1;
v___x_6928_ = l_Lean_Meta_mkLambdaFVars(v___x_6925_, v_a_6921_, v___x_6908_, v___x_6926_, v___x_6908_, v___x_6926_, v___x_6927_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_);
lean_dec_ref(v___x_6925_);
if (lean_obj_tag(v___x_6928_) == 0)
{
lean_object* v_a_6929_; lean_object* v___x_6930_; lean_object* v___x_6931_; 
v_a_6929_ = lean_ctor_get(v___x_6928_, 0);
lean_inc(v_a_6929_);
lean_dec_ref(v___x_6928_);
v___x_6930_ = l_Lean_Expr_app___override(v_fst_6909_, v_a_6929_);
v___x_6931_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6910_, v___x_6930_, v___x_6908_, v___x_6926_, v___x_6908_, v___x_6926_, v___x_6927_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_);
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
return v___x_6931_;
}
else
{
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
lean_dec_ref(v_fst_6909_);
return v___x_6928_;
}
}
else
{
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
lean_dec_ref(v_fst_6909_);
lean_dec_ref(v___x_6902_);
lean_dec_ref(v___x_6901_);
return v___x_6920_;
}
}
else
{
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
lean_dec_ref(v_fst_6909_);
lean_dec_ref(v_decrTactics_6907_);
lean_dec_ref(v_argsPacker_6906_);
lean_dec_ref(v_funNames_6905_);
lean_dec_ref(v___x_6902_);
lean_dec_ref(v___x_6901_);
return v___x_6918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6932_ = _args[0];
lean_object* v___x_6933_ = _args[1];
lean_object* v___x_6934_ = _args[2];
lean_object* v___f_6935_ = _args[3];
lean_object* v_funNames_6936_ = _args[4];
lean_object* v_argsPacker_6937_ = _args[5];
lean_object* v_decrTactics_6938_ = _args[6];
lean_object* v___x_6939_ = _args[7];
lean_object* v_fst_6940_ = _args[8];
lean_object* v_prefixArgs_6941_ = _args[9];
lean_object* v___y_6942_ = _args[10];
lean_object* v___y_6943_ = _args[11];
lean_object* v___y_6944_ = _args[12];
lean_object* v___y_6945_ = _args[13];
lean_object* v___y_6946_ = _args[14];
lean_object* v___y_6947_ = _args[15];
lean_object* v___y_6948_ = _args[16];
_start:
{
uint8_t v___x_6067__boxed_6949_; lean_object* v_res_6950_; 
v___x_6067__boxed_6949_ = lean_unbox(v___x_6939_);
v_res_6950_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6932_, v___x_6933_, v___x_6934_, v___f_6935_, v_funNames_6936_, v_argsPacker_6937_, v_decrTactics_6938_, v___x_6067__boxed_6949_, v_fst_6940_, v_prefixArgs_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
lean_dec_ref(v_prefixArgs_6941_);
return v_res_6950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6951_, lean_object* v_snd_6952_, lean_object* v___x_6953_, lean_object* v_prefixArgs_6954_, lean_object* v_value_6955_, lean_object* v___f_6956_, lean_object* v_funNames_6957_, lean_object* v_argsPacker_6958_, lean_object* v_decrTactics_6959_, uint8_t v___x_6960_, lean_object* v_fst_6961_, lean_object* v_xs_6962_, lean_object* v_x_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_){
_start:
{
lean_object* v_lctx_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; lean_object* v___x_6979_; lean_object* v___f_6980_; lean_object* v___x_6981_; 
v_lctx_6971_ = lean_ctor_get(v___y_6966_, 2);
v___x_6972_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_6951_);
v___x_6973_ = lean_array_get_borrowed(v___x_6951_, v_xs_6962_, v___x_6972_);
v___x_6974_ = l_Lean_Expr_fvarId_x21(v___x_6973_);
lean_inc_ref(v_lctx_6971_);
v___x_6975_ = l_Lean_LocalContext_setUserName(v_lctx_6971_, v___x_6974_, v_snd_6952_);
v___x_6976_ = lean_array_get_borrowed(v___x_6951_, v_xs_6962_, v___x_6953_);
lean_inc(v___x_6973_);
lean_inc_ref(v_prefixArgs_6954_);
v___x_6977_ = lean_array_push(v_prefixArgs_6954_, v___x_6973_);
v___x_6978_ = l_Lean_Expr_beta(v_value_6955_, v___x_6977_);
v___x_6979_ = lean_box(v___x_6960_);
lean_inc(v___x_6976_);
lean_inc(v___x_6973_);
v___f_6980_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6980_, 0, v___x_6973_);
lean_closure_set(v___f_6980_, 1, v___x_6976_);
lean_closure_set(v___f_6980_, 2, v___x_6978_);
lean_closure_set(v___f_6980_, 3, v___f_6956_);
lean_closure_set(v___f_6980_, 4, v_funNames_6957_);
lean_closure_set(v___f_6980_, 5, v_argsPacker_6958_);
lean_closure_set(v___f_6980_, 6, v_decrTactics_6959_);
lean_closure_set(v___f_6980_, 7, v___x_6979_);
lean_closure_set(v___f_6980_, 8, v_fst_6961_);
lean_closure_set(v___f_6980_, 9, v_prefixArgs_6954_);
v___x_6981_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6975_, v___f_6980_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_);
return v___x_6981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6982_ = _args[0];
lean_object* v_snd_6983_ = _args[1];
lean_object* v___x_6984_ = _args[2];
lean_object* v_prefixArgs_6985_ = _args[3];
lean_object* v_value_6986_ = _args[4];
lean_object* v___f_6987_ = _args[5];
lean_object* v_funNames_6988_ = _args[6];
lean_object* v_argsPacker_6989_ = _args[7];
lean_object* v_decrTactics_6990_ = _args[8];
lean_object* v___x_6991_ = _args[9];
lean_object* v_fst_6992_ = _args[10];
lean_object* v_xs_6993_ = _args[11];
lean_object* v_x_6994_ = _args[12];
lean_object* v___y_6995_ = _args[13];
lean_object* v___y_6996_ = _args[14];
lean_object* v___y_6997_ = _args[15];
lean_object* v___y_6998_ = _args[16];
lean_object* v___y_6999_ = _args[17];
lean_object* v___y_7000_ = _args[18];
lean_object* v___y_7001_ = _args[19];
_start:
{
uint8_t v___x_6137__boxed_7002_; lean_object* v_res_7003_; 
v___x_6137__boxed_7002_ = lean_unbox(v___x_6991_);
v_res_7003_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6982_, v_snd_6983_, v___x_6984_, v_prefixArgs_6985_, v_value_6986_, v___f_6987_, v_funNames_6988_, v_argsPacker_6989_, v_decrTactics_6990_, v___x_6137__boxed_7002_, v_fst_6992_, v_xs_6993_, v_x_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_, v___y_7000_);
lean_dec_ref(v_x_6994_);
lean_dec_ref(v_xs_6993_);
lean_dec(v___x_6984_);
return v_res_7003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_7008_, lean_object* v_prefixArgs_7009_, lean_object* v_argsPacker_7010_, lean_object* v_wfRel_7011_, lean_object* v_funNames_7012_, lean_object* v_decrTactics_7013_, lean_object* v_a_7014_, lean_object* v_a_7015_, lean_object* v_a_7016_, lean_object* v_a_7017_, lean_object* v_a_7018_, lean_object* v_a_7019_){
_start:
{
lean_object* v_declName_7021_; lean_object* v_type_7022_; lean_object* v_value_7023_; lean_object* v___x_7024_; 
v_declName_7021_ = lean_ctor_get(v_preDef_7008_, 3);
lean_inc(v_declName_7021_);
v_type_7022_ = lean_ctor_get(v_preDef_7008_, 6);
lean_inc_ref(v_type_7022_);
v_value_7023_ = lean_ctor_get(v_preDef_7008_, 7);
lean_inc_ref(v_value_7023_);
lean_dec_ref(v_preDef_7008_);
lean_inc(v_a_7019_);
lean_inc_ref(v_a_7018_);
lean_inc(v_a_7017_);
lean_inc_ref(v_a_7016_);
v___x_7024_ = l_Lean_Meta_instantiateForall(v_type_7022_, v_prefixArgs_7009_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
if (lean_obj_tag(v___x_7024_) == 0)
{
lean_object* v_a_7025_; lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v___f_7028_; lean_object* v___x_7029_; uint8_t v___x_7030_; lean_object* v___x_7031_; 
v_a_7025_ = lean_ctor_get(v___x_7024_, 0);
lean_inc(v_a_7025_);
lean_dec_ref(v___x_7024_);
v___x_7026_ = l_Lean_instInhabitedExpr;
v___x_7027_ = lean_unsigned_to_nat(1u);
v___f_7028_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_7028_, 0, v___x_7026_);
lean_closure_set(v___f_7028_, 1, v___x_7027_);
lean_closure_set(v___f_7028_, 2, v_wfRel_7011_);
v___x_7029_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_7030_ = 0;
lean_inc(v_a_7019_);
lean_inc_ref(v_a_7018_);
lean_inc(v_a_7017_);
lean_inc_ref(v_a_7016_);
lean_inc(v_a_7015_);
lean_inc_ref(v_a_7014_);
v___x_7031_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_7025_, v___x_7029_, v___f_7028_, v___x_7030_, v___x_7030_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
if (lean_obj_tag(v___x_7031_) == 0)
{
lean_object* v_a_7032_; lean_object* v_fst_7033_; lean_object* v_snd_7034_; lean_object* v___x_7035_; 
v_a_7032_ = lean_ctor_get(v___x_7031_, 0);
lean_inc(v_a_7032_);
lean_dec_ref(v___x_7031_);
v_fst_7033_ = lean_ctor_get(v_a_7032_, 0);
lean_inc(v_fst_7033_);
v_snd_7034_ = lean_ctor_get(v_a_7032_, 1);
lean_inc(v_snd_7034_);
lean_dec(v_a_7032_);
lean_inc(v_a_7019_);
lean_inc_ref(v_a_7018_);
lean_inc(v_a_7017_);
lean_inc_ref(v_a_7016_);
lean_inc(v_fst_7033_);
v___x_7035_ = lean_infer_type(v_fst_7033_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
if (lean_obj_tag(v___x_7035_) == 0)
{
lean_object* v_a_7036_; lean_object* v___x_7037_; 
v_a_7036_ = lean_ctor_get(v___x_7035_, 0);
lean_inc(v_a_7036_);
lean_dec_ref(v___x_7035_);
lean_inc(v_a_7019_);
lean_inc_ref(v_a_7018_);
lean_inc(v_a_7017_);
lean_inc_ref(v_a_7016_);
v___x_7037_ = lean_whnf(v_a_7036_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
if (lean_obj_tag(v___x_7037_) == 0)
{
lean_object* v_a_7038_; lean_object* v___f_7039_; lean_object* v___x_7040_; lean_object* v___f_7041_; lean_object* v___x_7042_; lean_object* v___x_7043_; lean_object* v___x_7044_; 
v_a_7038_ = lean_ctor_get(v___x_7037_, 0);
lean_inc(v_a_7038_);
lean_dec_ref(v___x_7037_);
lean_inc_ref(v_prefixArgs_7009_);
v___f_7039_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_7039_, 0, v_prefixArgs_7009_);
lean_closure_set(v___f_7039_, 1, v_declName_7021_);
v___x_7040_ = lean_box(v___x_7030_);
v___f_7041_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_7041_, 0, v___x_7026_);
lean_closure_set(v___f_7041_, 1, v_snd_7034_);
lean_closure_set(v___f_7041_, 2, v___x_7027_);
lean_closure_set(v___f_7041_, 3, v_prefixArgs_7009_);
lean_closure_set(v___f_7041_, 4, v_value_7023_);
lean_closure_set(v___f_7041_, 5, v___f_7039_);
lean_closure_set(v___f_7041_, 6, v_funNames_7012_);
lean_closure_set(v___f_7041_, 7, v_argsPacker_7010_);
lean_closure_set(v___f_7041_, 8, v_decrTactics_7013_);
lean_closure_set(v___f_7041_, 9, v___x_7040_);
lean_closure_set(v___f_7041_, 10, v_fst_7033_);
v___x_7042_ = l_Lean_Expr_bindingDomain_x21(v_a_7038_);
lean_dec(v_a_7038_);
v___x_7043_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_7044_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_7042_, v___x_7043_, v___f_7041_, v___x_7030_, v___x_7030_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
return v___x_7044_;
}
else
{
lean_dec(v_snd_7034_);
lean_dec(v_fst_7033_);
lean_dec_ref(v_value_7023_);
lean_dec(v_declName_7021_);
lean_dec(v_a_7019_);
lean_dec_ref(v_a_7018_);
lean_dec(v_a_7017_);
lean_dec_ref(v_a_7016_);
lean_dec(v_a_7015_);
lean_dec_ref(v_a_7014_);
lean_dec_ref(v_decrTactics_7013_);
lean_dec_ref(v_funNames_7012_);
lean_dec_ref(v_argsPacker_7010_);
lean_dec_ref(v_prefixArgs_7009_);
return v___x_7037_;
}
}
else
{
lean_dec(v_snd_7034_);
lean_dec(v_fst_7033_);
lean_dec_ref(v_value_7023_);
lean_dec(v_declName_7021_);
lean_dec(v_a_7019_);
lean_dec_ref(v_a_7018_);
lean_dec(v_a_7017_);
lean_dec_ref(v_a_7016_);
lean_dec(v_a_7015_);
lean_dec_ref(v_a_7014_);
lean_dec_ref(v_decrTactics_7013_);
lean_dec_ref(v_funNames_7012_);
lean_dec_ref(v_argsPacker_7010_);
lean_dec_ref(v_prefixArgs_7009_);
return v___x_7035_;
}
}
else
{
lean_object* v_a_7045_; lean_object* v___x_7047_; uint8_t v_isShared_7048_; uint8_t v_isSharedCheck_7052_; 
lean_dec_ref(v_value_7023_);
lean_dec(v_declName_7021_);
lean_dec(v_a_7019_);
lean_dec_ref(v_a_7018_);
lean_dec(v_a_7017_);
lean_dec_ref(v_a_7016_);
lean_dec(v_a_7015_);
lean_dec_ref(v_a_7014_);
lean_dec_ref(v_decrTactics_7013_);
lean_dec_ref(v_funNames_7012_);
lean_dec_ref(v_argsPacker_7010_);
lean_dec_ref(v_prefixArgs_7009_);
v_a_7045_ = lean_ctor_get(v___x_7031_, 0);
v_isSharedCheck_7052_ = !lean_is_exclusive(v___x_7031_);
if (v_isSharedCheck_7052_ == 0)
{
v___x_7047_ = v___x_7031_;
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
else
{
lean_inc(v_a_7045_);
lean_dec(v___x_7031_);
v___x_7047_ = lean_box(0);
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
v_resetjp_7046_:
{
lean_object* v___x_7050_; 
if (v_isShared_7048_ == 0)
{
v___x_7050_ = v___x_7047_;
goto v_reusejp_7049_;
}
else
{
lean_object* v_reuseFailAlloc_7051_; 
v_reuseFailAlloc_7051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7051_, 0, v_a_7045_);
v___x_7050_ = v_reuseFailAlloc_7051_;
goto v_reusejp_7049_;
}
v_reusejp_7049_:
{
return v___x_7050_;
}
}
}
}
else
{
lean_dec_ref(v_value_7023_);
lean_dec(v_declName_7021_);
lean_dec(v_a_7019_);
lean_dec_ref(v_a_7018_);
lean_dec(v_a_7017_);
lean_dec_ref(v_a_7016_);
lean_dec(v_a_7015_);
lean_dec_ref(v_a_7014_);
lean_dec_ref(v_decrTactics_7013_);
lean_dec_ref(v_funNames_7012_);
lean_dec_ref(v_wfRel_7011_);
lean_dec_ref(v_argsPacker_7010_);
lean_dec_ref(v_prefixArgs_7009_);
return v___x_7024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_7053_, lean_object* v_prefixArgs_7054_, lean_object* v_argsPacker_7055_, lean_object* v_wfRel_7056_, lean_object* v_funNames_7057_, lean_object* v_decrTactics_7058_, lean_object* v_a_7059_, lean_object* v_a_7060_, lean_object* v_a_7061_, lean_object* v_a_7062_, lean_object* v_a_7063_, lean_object* v_a_7064_, lean_object* v_a_7065_){
_start:
{
lean_object* v_res_7066_; 
v_res_7066_ = l_Lean_Elab_WF_mkFix(v_preDef_7053_, v_prefixArgs_7054_, v_argsPacker_7055_, v_wfRel_7056_, v_funNames_7057_, v_decrTactics_7058_, v_a_7059_, v_a_7060_, v_a_7061_, v_a_7062_, v_a_7063_, v_a_7064_);
return v_res_7066_;
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
res = l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
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
