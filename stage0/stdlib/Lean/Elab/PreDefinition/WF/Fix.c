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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
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
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
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
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___boxed(lean_object* v_decreasingProp_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v_decreasingProp_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
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
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
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
v___x_131_ = lean_panic_fn_borrowed(v___x_130_, v_msg_129_);
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
goto v___jp_206_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v___x_216_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5);
v___x_217_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_216_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
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
v_size_208_ = lean_ctor_get(v_decls_207_, 2);
v___x_209_ = l_Lean_LocalContext_size(v_lctx_204_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_sub(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_nat_dec_lt(v___x_211_, v_size_208_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec(v___x_211_);
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
lean_dec_ref(v_a_226_);
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
lean_dec_ref(v_a_256_);
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
lean_dec_ref(v_a_267_);
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
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_315_; double v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_float_of_nat(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object* v_cls_320_, lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_ref_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_373_; 
v_ref_327_ = lean_ctor_get(v___y_324_, 5);
v___x_328_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_373_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_373_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_373_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v_traceState_334_; lean_object* v_env_335_; lean_object* v_nextMacroScope_336_; lean_object* v_ngen_337_; lean_object* v_auxDeclNGen_338_; lean_object* v_cache_339_; lean_object* v_messages_340_; lean_object* v_infoState_341_; lean_object* v_snapshotTasks_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_372_; 
v___x_333_ = lean_st_ref_take(v___y_325_);
v_traceState_334_ = lean_ctor_get(v___x_333_, 4);
v_env_335_ = lean_ctor_get(v___x_333_, 0);
v_nextMacroScope_336_ = lean_ctor_get(v___x_333_, 1);
v_ngen_337_ = lean_ctor_get(v___x_333_, 2);
v_auxDeclNGen_338_ = lean_ctor_get(v___x_333_, 3);
v_cache_339_ = lean_ctor_get(v___x_333_, 5);
v_messages_340_ = lean_ctor_get(v___x_333_, 6);
v_infoState_341_ = lean_ctor_get(v___x_333_, 7);
v_snapshotTasks_342_ = lean_ctor_get(v___x_333_, 8);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_372_ == 0)
{
v___x_344_ = v___x_333_;
v_isShared_345_ = v_isSharedCheck_372_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snapshotTasks_342_);
lean_inc(v_infoState_341_);
lean_inc(v_messages_340_);
lean_inc(v_cache_339_);
lean_inc(v_traceState_334_);
lean_inc(v_auxDeclNGen_338_);
lean_inc(v_ngen_337_);
lean_inc(v_nextMacroScope_336_);
lean_inc(v_env_335_);
lean_dec(v___x_333_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_372_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint64_t v_tid_346_; lean_object* v_traces_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_371_; 
v_tid_346_ = lean_ctor_get_uint64(v_traceState_334_, sizeof(void*)*1);
v_traces_347_ = lean_ctor_get(v_traceState_334_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_traceState_334_);
if (v_isSharedCheck_371_ == 0)
{
v___x_349_ = v_traceState_334_;
v_isShared_350_ = v_isSharedCheck_371_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_traces_347_);
lean_dec(v_traceState_334_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_371_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; double v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_351_ = lean_box(0);
v___x_352_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_353_ = 0;
v___x_354_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_355_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_355_, 0, v_cls_320_);
lean_ctor_set(v___x_355_, 1, v___x_351_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set_float(v___x_355_, sizeof(void*)*3, v___x_352_);
lean_ctor_set_float(v___x_355_, sizeof(void*)*3 + 8, v___x_352_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*3 + 16, v___x_353_);
v___x_356_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_357_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v_a_329_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_inc(v_ref_327_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_ref_327_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_PersistentArray_push___redArg(v_traces_347_, v___x_358_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_359_);
v___x_361_ = v___x_349_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_359_);
lean_ctor_set_uint64(v_reuseFailAlloc_370_, sizeof(void*)*1, v_tid_346_);
v___x_361_ = v_reuseFailAlloc_370_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v___x_361_);
v___x_363_ = v___x_344_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_env_335_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_nextMacroScope_336_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_ngen_337_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_auxDeclNGen_338_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_369_, 5, v_cache_339_);
lean_ctor_set(v_reuseFailAlloc_369_, 6, v_messages_340_);
lean_ctor_set(v_reuseFailAlloc_369_, 7, v_infoState_341_);
lean_ctor_set(v_reuseFailAlloc_369_, 8, v_snapshotTasks_342_);
v___x_363_ = v_reuseFailAlloc_369_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_364_ = lean_st_ref_set(v___y_325_, v___x_363_);
v___x_365_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_365_);
v___x_367_ = v___x_331_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object* v_cls_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_374_, v_msg_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
return v_x_382_;
}
else
{
lean_object* v_key_384_; lean_object* v_value_385_; lean_object* v_tail_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_409_; 
v_key_384_ = lean_ctor_get(v_x_383_, 0);
v_value_385_ = lean_ctor_get(v_x_383_, 1);
v_tail_386_ = lean_ctor_get(v_x_383_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_409_ == 0)
{
v___x_388_ = v_x_383_;
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_tail_386_);
lean_inc(v_value_385_);
lean_inc(v_key_384_);
lean_dec(v_x_383_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v_fold_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_390_ = lean_array_get_size(v_x_382_);
v___x_391_ = l_Lean_Expr_hash(v_key_384_);
v___x_392_ = 32ULL;
v___x_393_ = lean_uint64_shift_right(v___x_391_, v___x_392_);
v_fold_394_ = lean_uint64_xor(v___x_391_, v___x_393_);
v___x_395_ = 16ULL;
v___x_396_ = lean_uint64_shift_right(v_fold_394_, v___x_395_);
v___x_397_ = lean_uint64_xor(v_fold_394_, v___x_396_);
v___x_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = lean_usize_of_nat(v___x_390_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_sub(v___x_399_, v___x_400_);
v___x_402_ = lean_usize_land(v___x_398_, v___x_401_);
v___x_403_ = lean_array_uget_borrowed(v_x_382_, v___x_402_);
lean_inc(v___x_403_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 2, v___x_403_);
v___x_405_ = v___x_388_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_key_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_value_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v___x_403_);
v___x_405_ = v_reuseFailAlloc_408_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_array_uset(v_x_382_, v___x_402_, v___x_405_);
v_x_382_ = v___x_406_;
v_x_383_ = v_tail_386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(lean_object* v_i_410_, lean_object* v_source_411_, lean_object* v_target_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_source_411_);
v___x_414_ = lean_nat_dec_lt(v_i_410_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_source_411_);
lean_dec(v_i_410_);
return v_target_412_;
}
else
{
lean_object* v_es_415_; lean_object* v___x_416_; lean_object* v_source_417_; lean_object* v_target_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_es_415_ = lean_array_fget(v_source_411_, v_i_410_);
v___x_416_ = lean_box(0);
v_source_417_ = lean_array_fset(v_source_411_, v_i_410_, v___x_416_);
v_target_418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_target_412_, v_es_415_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_add(v_i_410_, v___x_419_);
lean_dec(v_i_410_);
v_i_410_ = v___x_420_;
v_source_411_ = v_source_417_;
v_target_412_ = v_target_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(lean_object* v_data_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_nbuckets_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_423_ = lean_array_get_size(v_data_422_);
v___x_424_ = lean_unsigned_to_nat(2u);
v_nbuckets_425_ = lean_nat_mul(v___x_423_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_box(0);
v___x_428_ = lean_mk_array(v_nbuckets_425_, v___x_427_);
v___x_429_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_426_, v_data_422_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
else
{
lean_object* v_key_433_; lean_object* v_tail_434_; uint8_t v___x_435_; 
v_key_433_ = lean_ctor_get(v_x_431_, 0);
v_tail_434_ = lean_ctor_get(v_x_431_, 2);
v___x_435_ = lean_expr_eqv(v_key_433_, v_a_430_);
if (v___x_435_ == 0)
{
v_x_431_ = v_tail_434_;
goto _start;
}
else
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec_ref(v_a_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_dec(v_b_442_);
lean_dec_ref(v_a_441_);
return v_x_443_;
}
else
{
lean_object* v_key_444_; lean_object* v_value_445_; lean_object* v_tail_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_458_; 
v_key_444_ = lean_ctor_get(v_x_443_, 0);
v_value_445_ = lean_ctor_get(v_x_443_, 1);
v_tail_446_ = lean_ctor_get(v_x_443_, 2);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_458_ == 0)
{
v___x_448_ = v_x_443_;
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_tail_446_);
lean_inc(v_value_445_);
lean_inc(v_key_444_);
lean_dec(v_x_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
uint8_t v___x_450_; 
v___x_450_ = lean_expr_eqv(v_key_444_, v_a_441_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_441_, v_b_442_, v_tail_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_key_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_value_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_value_445_);
lean_dec(v_key_444_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v_b_442_);
lean_ctor_set(v___x_448_, 0, v_a_441_);
v___x_456_ = v___x_448_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_b_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_tail_446_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_459_, lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
lean_object* v_size_462_; lean_object* v_buckets_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_506_; 
v_size_462_ = lean_ctor_get(v_m_459_, 0);
v_buckets_463_ = lean_ctor_get(v_m_459_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_m_459_);
if (v_isSharedCheck_506_ == 0)
{
v___x_465_ = v_m_459_;
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_buckets_463_);
lean_inc(v_size_462_);
lean_dec(v_m_459_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v_fold_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v_bkt_480_; uint8_t v___x_481_; 
v___x_467_ = lean_array_get_size(v_buckets_463_);
v___x_468_ = l_Lean_Expr_hash(v_a_460_);
v___x_469_ = 32ULL;
v___x_470_ = lean_uint64_shift_right(v___x_468_, v___x_469_);
v_fold_471_ = lean_uint64_xor(v___x_468_, v___x_470_);
v___x_472_ = 16ULL;
v___x_473_ = lean_uint64_shift_right(v_fold_471_, v___x_472_);
v___x_474_ = lean_uint64_xor(v_fold_471_, v___x_473_);
v___x_475_ = lean_uint64_to_usize(v___x_474_);
v___x_476_ = lean_usize_of_nat(v___x_467_);
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_sub(v___x_476_, v___x_477_);
v___x_479_ = lean_usize_land(v___x_475_, v___x_478_);
v_bkt_480_ = lean_array_uget_borrowed(v_buckets_463_, v___x_479_);
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_460_, v_bkt_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v_size_x27_483_; lean_object* v___x_484_; lean_object* v_buckets_x27_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v_size_x27_483_ = lean_nat_add(v_size_462_, v___x_482_);
lean_dec(v_size_462_);
lean_inc(v_bkt_480_);
v___x_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_484_, 0, v_a_460_);
lean_ctor_set(v___x_484_, 1, v_b_461_);
lean_ctor_set(v___x_484_, 2, v_bkt_480_);
v_buckets_x27_485_ = lean_array_uset(v_buckets_463_, v___x_479_, v___x_484_);
v___x_486_ = lean_unsigned_to_nat(4u);
v___x_487_ = lean_nat_mul(v_size_x27_483_, v___x_486_);
v___x_488_ = lean_unsigned_to_nat(3u);
v___x_489_ = lean_nat_div(v___x_487_, v___x_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_array_get_size(v_buckets_x27_485_);
v___x_491_ = lean_nat_dec_le(v___x_489_, v___x_490_);
lean_dec(v___x_489_);
if (v___x_491_ == 0)
{
lean_object* v_val_492_; lean_object* v___x_494_; 
v_val_492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_485_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v_val_492_);
lean_ctor_set(v___x_465_, 0, v_size_x27_483_);
v___x_494_ = v___x_465_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_size_x27_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_val_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_497_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v_buckets_x27_485_);
lean_ctor_set(v___x_465_, 0, v_size_x27_483_);
v___x_497_ = v___x_465_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_size_x27_483_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_buckets_x27_485_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v___x_499_; lean_object* v_buckets_x27_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
lean_inc(v_bkt_480_);
v___x_499_ = lean_box(0);
v_buckets_x27_500_ = lean_array_uset(v_buckets_463_, v___x_479_, v___x_499_);
v___x_501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_460_, v_b_461_, v_bkt_480_);
v___x_502_ = lean_array_uset(v_buckets_x27_500_, v___x_479_, v___x_501_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_502_);
v___x_504_ = v___x_465_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_size_462_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_ref_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_ref_513_ = lean_ctor_get(v___y_510_, 5);
v___x_514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_inc(v_ref_513_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_ref_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_546_, lean_object* v_e_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_639_; 
lean_inc_ref(v_a_546_);
v___x_639_ = l_Lean_Meta_isTypeCorrect(v_a_546_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; uint8_t v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_547_);
v___x_643_ = l_Lean_indentExpr(v_e_547_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_inc_ref(v_a_546_);
v___x_647_ = l_Lean_indentExpr(v_a_546_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_648_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_dec_ref(v___x_649_);
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
v___y_563_ = v___y_553_;
v___y_564_ = v___y_554_;
v___y_565_ = v___y_555_;
goto v___jp_557_;
}
else
{
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
return v___x_649_;
}
}
else
{
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
v___y_563_ = v___y_553_;
v___y_564_ = v___y_554_;
v___y_565_ = v___y_555_;
goto v___jp_557_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v_a_650_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_639_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_639_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
v___jp_557_:
{
lean_object* v___x_566_; 
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc_ref(v_e_547_);
v___x_566_ = lean_infer_type(v_e_547_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref(v___x_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc_ref(v_a_546_);
v___x_568_ = lean_infer_type(v_a_546_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_n(v_a_569_, 2);
lean_dec_ref(v___x_568_);
lean_inc(v_a_567_);
v___x_570_ = l_Lean_Meta_isExprDefEq(v_a_567_, v_a_569_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_614_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_614_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_614_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_614_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
uint8_t v___x_575_; 
v___x_575_ = lean_unbox(v_a_571_);
lean_dec(v_a_571_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_del_object(v___x_573_);
v___x_576_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_567_, v_a_569_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_601_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v_fst_578_ = lean_ctor_get(v_a_577_, 0);
v_snd_579_ = lean_ctor_get(v_a_577_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_a_577_);
if (v_isSharedCheck_601_ == 0)
{
v___x_581_ = v_a_577_;
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_inc(v_fst_578_);
lean_dec(v_a_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_584_ = l_Lean_indentExpr(v_e_547_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 7);
lean_ctor_set(v___x_581_, 1, v___x_584_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_600_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_indentExpr(v_a_546_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_indentExpr(v_fst_578_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_indentExpr(v_snd_579_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_598_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v_a_602_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_576_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_576_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_612_; 
lean_dec(v_a_569_);
lean_dec(v_a_567_);
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v___x_610_ = lean_box(0);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_610_);
v___x_612_ = v___x_573_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_569_);
lean_dec(v_a_567_);
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v_a_615_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_570_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_570_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_567_);
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v_a_623_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_568_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_568_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_e_547_);
lean_dec_ref(v_a_546_);
v_a_631_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_566_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_566_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_658_, lean_object* v_e_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_658_, v_e_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
return v_res_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_670_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
lean_ctor_set(v___x_675_, 3, v___x_674_);
lean_ctor_set(v___x_675_, 4, v___x_673_);
lean_ctor_set(v___x_675_, 5, v___x_673_);
lean_ctor_set(v___x_675_, 6, v___x_673_);
lean_ctor_set(v___x_675_, 7, v___x_673_);
lean_ctor_set(v___x_675_, 8, v___x_673_);
lean_ctor_set(v___x_675_, 9, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_unsigned_to_nat(32u);
v___x_677_ = lean_mk_empty_array_with_capacity(v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_679_ = ((size_t)5ULL);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_unsigned_to_nat(32u);
v___x_682_ = lean_mk_empty_array_with_capacity(v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_684_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
lean_ctor_set(v___x_684_, 2, v___x_680_);
lean_ctor_set(v___x_684_, 3, v___x_680_);
lean_ctor_set_usize(v___x_684_, 4, v___x_679_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_box(1);
v___x_686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_710_, lean_object* v_declHint_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; lean_object* v_env_715_; uint8_t v___x_716_; 
v___x_714_ = lean_st_ref_get(v___y_712_);
v_env_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_env_715_);
lean_dec(v___x_714_);
v___x_716_ = l_Lean_Name_isAnonymous(v_declHint_711_);
if (v___x_716_ == 0)
{
uint8_t v_isExporting_717_; 
v_isExporting_717_ = lean_ctor_get_uint8(v_env_715_, sizeof(void*)*8);
if (v_isExporting_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v_env_715_);
lean_dec(v_declHint_711_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_msg_710_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
lean_inc_ref(v_env_715_);
v___x_719_ = l_Lean_Environment_setExporting(v_env_715_, v___x_716_);
lean_inc(v_declHint_711_);
lean_inc_ref(v___x_719_);
v___x_720_ = l_Lean_Environment_contains(v___x_719_, v_declHint_711_, v_isExporting_717_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v___x_719_);
lean_dec_ref(v_env_715_);
lean_dec(v_declHint_711_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_msg_710_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_c_727_; lean_object* v___x_728_; 
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_724_ = l_Lean_Options_empty;
v___x_725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_725_, 0, v___x_719_);
lean_ctor_set(v___x_725_, 1, v___x_722_);
lean_ctor_set(v___x_725_, 2, v___x_723_);
lean_ctor_set(v___x_725_, 3, v___x_724_);
lean_inc(v_declHint_711_);
v___x_726_ = l_Lean_MessageData_ofConstName(v_declHint_711_, v___x_716_);
v_c_727_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_727_, 0, v___x_725_);
lean_ctor_set(v_c_727_, 1, v___x_726_);
v___x_728_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_715_, v_declHint_711_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref(v_env_715_);
lean_dec(v_declHint_711_);
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_c_727_);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = l_Lean_MessageData_note(v___x_732_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v_msg_710_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v_val_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_771_; 
v_val_736_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_771_ == 0)
{
v___x_738_ = v___x_728_;
v_isShared_739_ = v_isSharedCheck_771_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_val_736_);
lean_dec(v___x_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_771_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_mod_743_; uint8_t v___x_744_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Lean_Environment_header(v_env_715_);
lean_dec_ref(v_env_715_);
v___x_742_ = l_Lean_EnvironmentHeader_moduleNames(v___x_741_);
v_mod_743_ = lean_array_get(v___x_740_, v___x_742_, v_val_736_);
lean_dec(v_val_736_);
lean_dec_ref(v___x_742_);
v___x_744_ = l_Lean_isPrivateName(v_declHint_711_);
lean_dec(v_declHint_711_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_c_727_);
v___x_747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_MessageData_ofName(v_mod_743_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_MessageData_note(v___x_752_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v_msg_710_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
lean_ctor_set(v___x_738_, 0, v___x_754_);
v___x_756_ = v___x_738_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v_c_727_);
v___x_760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_MessageData_ofName(v_mod_743_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_MessageData_note(v___x_765_);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v_msg_710_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
lean_ctor_set(v___x_738_, 0, v___x_767_);
v___x_769_ = v___x_738_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_772_; 
lean_dec_ref(v_env_715_);
lean_dec(v_declHint_711_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_msg_710_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_773_, lean_object* v_declHint_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_773_, v_declHint_774_, v___y_775_);
lean_dec(v___y_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_778_, lean_object* v_declHint_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_799_; 
v___x_789_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_778_, v_declHint_779_, v___y_787_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_799_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = l_Lean_unknownIdentifierMessageTag;
v___x_795_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_a_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_795_);
v___x_797_ = v___x_792_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_800_, lean_object* v_declHint_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_800_, v_declHint_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_812_, lean_object* v_msg_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_fileName_823_; lean_object* v_fileMap_824_; lean_object* v_options_825_; lean_object* v_currRecDepth_826_; lean_object* v_maxRecDepth_827_; lean_object* v_ref_828_; lean_object* v_currNamespace_829_; lean_object* v_openDecls_830_; lean_object* v_initHeartbeats_831_; lean_object* v_maxHeartbeats_832_; lean_object* v_quotContext_833_; lean_object* v_currMacroScope_834_; uint8_t v_diag_835_; lean_object* v_cancelTk_x3f_836_; uint8_t v_suppressElabErrors_837_; lean_object* v_inheritedTraceOptions_838_; lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_fileName_823_ = lean_ctor_get(v___y_820_, 0);
v_fileMap_824_ = lean_ctor_get(v___y_820_, 1);
v_options_825_ = lean_ctor_get(v___y_820_, 2);
v_currRecDepth_826_ = lean_ctor_get(v___y_820_, 3);
v_maxRecDepth_827_ = lean_ctor_get(v___y_820_, 4);
v_ref_828_ = lean_ctor_get(v___y_820_, 5);
v_currNamespace_829_ = lean_ctor_get(v___y_820_, 6);
v_openDecls_830_ = lean_ctor_get(v___y_820_, 7);
v_initHeartbeats_831_ = lean_ctor_get(v___y_820_, 8);
v_maxHeartbeats_832_ = lean_ctor_get(v___y_820_, 9);
v_quotContext_833_ = lean_ctor_get(v___y_820_, 10);
v_currMacroScope_834_ = lean_ctor_get(v___y_820_, 11);
v_diag_835_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*14);
v_cancelTk_x3f_836_ = lean_ctor_get(v___y_820_, 12);
v_suppressElabErrors_837_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_838_ = lean_ctor_get(v___y_820_, 13);
v_ref_839_ = l_Lean_replaceRef(v_ref_812_, v_ref_828_);
lean_inc_ref(v_inheritedTraceOptions_838_);
lean_inc(v_cancelTk_x3f_836_);
lean_inc(v_currMacroScope_834_);
lean_inc(v_quotContext_833_);
lean_inc(v_maxHeartbeats_832_);
lean_inc(v_initHeartbeats_831_);
lean_inc(v_openDecls_830_);
lean_inc(v_currNamespace_829_);
lean_inc(v_maxRecDepth_827_);
lean_inc(v_currRecDepth_826_);
lean_inc_ref(v_options_825_);
lean_inc_ref(v_fileMap_824_);
lean_inc_ref(v_fileName_823_);
v___x_840_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_840_, 0, v_fileName_823_);
lean_ctor_set(v___x_840_, 1, v_fileMap_824_);
lean_ctor_set(v___x_840_, 2, v_options_825_);
lean_ctor_set(v___x_840_, 3, v_currRecDepth_826_);
lean_ctor_set(v___x_840_, 4, v_maxRecDepth_827_);
lean_ctor_set(v___x_840_, 5, v_ref_839_);
lean_ctor_set(v___x_840_, 6, v_currNamespace_829_);
lean_ctor_set(v___x_840_, 7, v_openDecls_830_);
lean_ctor_set(v___x_840_, 8, v_initHeartbeats_831_);
lean_ctor_set(v___x_840_, 9, v_maxHeartbeats_832_);
lean_ctor_set(v___x_840_, 10, v_quotContext_833_);
lean_ctor_set(v___x_840_, 11, v_currMacroScope_834_);
lean_ctor_set(v___x_840_, 12, v_cancelTk_x3f_836_);
lean_ctor_set(v___x_840_, 13, v_inheritedTraceOptions_838_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*14, v_diag_835_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*14 + 1, v_suppressElabErrors_837_);
v___x_841_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_813_, v___y_818_, v___y_819_, v___x_840_, v___y_821_);
lean_dec_ref(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_842_, lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_842_, v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v_ref_842_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_854_, lean_object* v_msg_855_, lean_object* v_declHint_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_868_; 
v___x_866_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_855_, v_declHint_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_854_, v_a_867_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_869_, lean_object* v_msg_870_, lean_object* v_declHint_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_869_, v_msg_870_, v_declHint_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v_ref_869_);
return v_res_881_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_888_, lean_object* v_constName_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_899_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_900_ = 0;
lean_inc(v_constName_889_);
v___x_901_ = l_Lean_MessageData_ofConstName(v_constName_889_, v___x_900_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_888_, v___x_904_, v_constName_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_906_, lean_object* v_constName_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_906_, v_constName_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v_ref_906_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_ref_928_; lean_object* v___x_929_; 
v_ref_928_ = lean_ctor_get(v___y_925_, 5);
v___x_929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_928_, v_constName_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_env_952_; uint8_t v___x_953_; lean_object* v___x_954_; 
v___x_951_ = lean_st_ref_get(v___y_949_);
v_env_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_env_952_);
lean_dec(v___x_951_);
v___x_953_ = 0;
lean_inc(v_constName_941_);
v___x_954_ = l_Lean_Environment_find_x3f(v_env_952_, v_constName_941_, v___x_953_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_955_;
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_constName_941_);
v_val_956_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_954_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v___x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_val_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_979_, v_declName_975_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_982_, v___y_983_);
lean_dec(v___y_983_);
return v_res_985_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_instMonadEIO(lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_toApplicative_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1098_; 
v___x_1003_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_1004_ = l_StateRefT_x27_instMonad___redArg(v___x_1003_);
v_toApplicative_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v___x_1004_, 1);
lean_dec(v_unused_1099_);
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1098_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_toApplicative_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1098_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_toFunctor_1009_; lean_object* v_toSeq_1010_; lean_object* v_toSeqLeft_1011_; lean_object* v_toSeqRight_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1096_; 
v_toFunctor_1009_ = lean_ctor_get(v_toApplicative_1005_, 0);
v_toSeq_1010_ = lean_ctor_get(v_toApplicative_1005_, 2);
v_toSeqLeft_1011_ = lean_ctor_get(v_toApplicative_1005_, 3);
v_toSeqRight_1012_ = lean_ctor_get(v_toApplicative_1005_, 4);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_toApplicative_1005_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_toApplicative_1005_, 1);
lean_dec(v_unused_1097_);
v___x_1014_ = v_toApplicative_1005_;
v_isShared_1015_ = v_isSharedCheck_1096_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_toSeqRight_1012_);
lean_inc(v_toSeqLeft_1011_);
lean_inc(v_toSeq_1010_);
lean_inc(v_toFunctor_1009_);
lean_dec(v_toApplicative_1005_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1096_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1025_; 
v___f_1016_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1017_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1009_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toFunctor_1009_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toFunctor_1009_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___f_1018_);
lean_ctor_set(v___x_1020_, 1, v___f_1019_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toSeqRight_1012_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeqLeft_1011_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toSeq_1010_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v___f_1021_);
lean_ctor_set(v___x_1014_, 3, v___f_1022_);
lean_ctor_set(v___x_1014_, 2, v___f_1023_);
lean_ctor_set(v___x_1014_, 1, v___f_1016_);
lean_ctor_set(v___x_1014_, 0, v___x_1020_);
v___x_1025_ = v___x_1014_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___f_1016_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v___f_1023_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v___f_1022_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___f_1021_);
v___x_1025_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___f_1017_);
lean_ctor_set(v___x_1007_, 0, v___x_1025_);
v___x_1027_ = v___x_1007_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___f_1017_);
v___x_1027_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v_toApplicative_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1092_; 
v___x_1028_ = l_StateRefT_x27_instMonad___redArg(v___x_1027_);
v_toApplicative_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1028_, 1);
lean_dec(v_unused_1093_);
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1092_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_toApplicative_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1092_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_toFunctor_1033_; lean_object* v_toSeq_1034_; lean_object* v_toSeqLeft_1035_; lean_object* v_toSeqRight_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1090_; 
v_toFunctor_1033_ = lean_ctor_get(v_toApplicative_1029_, 0);
v_toSeq_1034_ = lean_ctor_get(v_toApplicative_1029_, 2);
v_toSeqLeft_1035_ = lean_ctor_get(v_toApplicative_1029_, 3);
v_toSeqRight_1036_ = lean_ctor_get(v_toApplicative_1029_, 4);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_toApplicative_1029_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_toApplicative_1029_, 1);
lean_dec(v_unused_1091_);
v___x_1038_ = v_toApplicative_1029_;
v_isShared_1039_ = v_isSharedCheck_1090_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_toSeqRight_1036_);
lean_inc(v_toSeqLeft_1035_);
lean_inc(v_toSeq_1034_);
lean_inc(v_toFunctor_1033_);
lean_dec(v_toApplicative_1029_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1090_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1049_; 
v___f_1040_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1041_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1033_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toFunctor_1033_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toFunctor_1033_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___f_1042_);
lean_ctor_set(v___x_1044_, 1, v___f_1043_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toSeqRight_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toSeqLeft_1035_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeq_1034_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 4, v___f_1045_);
lean_ctor_set(v___x_1038_, 3, v___f_1046_);
lean_ctor_set(v___x_1038_, 2, v___f_1047_);
lean_ctor_set(v___x_1038_, 1, v___f_1040_);
lean_ctor_set(v___x_1038_, 0, v___x_1044_);
v___x_1049_ = v___x_1038_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v___f_1047_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v___f_1046_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v___f_1045_);
v___x_1049_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___f_1041_);
lean_ctor_set(v___x_1031_, 0, v___x_1049_);
v___x_1051_ = v___x_1031_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___f_1041_);
v___x_1051_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v_toApplicative_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1086_; 
v___x_1052_ = l_StateRefT_x27_instMonad___redArg(v___x_1051_);
v_toApplicative_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1052_, 1);
lean_dec(v_unused_1087_);
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1086_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_toApplicative_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1086_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_toFunctor_1057_; lean_object* v_toSeq_1058_; lean_object* v_toSeqLeft_1059_; lean_object* v_toSeqRight_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1084_; 
v_toFunctor_1057_ = lean_ctor_get(v_toApplicative_1053_, 0);
v_toSeq_1058_ = lean_ctor_get(v_toApplicative_1053_, 2);
v_toSeqLeft_1059_ = lean_ctor_get(v_toApplicative_1053_, 3);
v_toSeqRight_1060_ = lean_ctor_get(v_toApplicative_1053_, 4);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_toApplicative_1053_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_dec(v_unused_1085_);
v___x_1062_ = v_toApplicative_1053_;
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_toSeqRight_1060_);
lean_inc(v_toSeqLeft_1059_);
lean_inc(v_toSeq_1058_);
lean_inc(v_toFunctor_1057_);
lean_dec(v_toApplicative_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1073_; 
v___f_1064_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1065_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1057_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toFunctor_1057_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toFunctor_1057_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___f_1066_);
lean_ctor_set(v___x_1068_, 1, v___f_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1069_, 0, v_toSeqRight_1060_);
v___f_1070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1070_, 0, v_toSeqLeft_1059_);
v___f_1071_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1071_, 0, v_toSeq_1058_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___f_1069_);
lean_ctor_set(v___x_1062_, 3, v___f_1070_);
lean_ctor_set(v___x_1062_, 2, v___f_1071_);
lean_ctor_set(v___x_1062_, 1, v___f_1064_);
lean_ctor_set(v___x_1062_, 0, v___x_1068_);
v___x_1073_ = v___x_1062_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___f_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v___f_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___f_1069_);
v___x_1073_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___f_1065_);
lean_ctor_set(v___x_1055_, 0, v___x_1073_);
v___x_1075_ = v___x_1055_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1065_);
v___x_1075_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_58733__overap_1080_; lean_object* v___x_1081_; 
v___x_1076_ = l_StateRefT_x27_instMonad___redArg(v___x_1075_);
v___x_1077_ = l_StateRefT_x27_instMonad___redArg(v___x_1076_);
v___x_1078_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1079_ = l_instInhabitedOfMonad___redArg(v___x_1077_, v___x_1078_);
v___x_58733__overap_1080_ = lean_panic_fn_borrowed(v___x_1079_, v_msg_993_);
lean_dec(v___x_1079_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc(v___y_994_);
v___x_1081_ = lean_apply_9(v___x_58733__overap_1080_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, lean_box(0));
return v___x_1081_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
return v_res_1110_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1115_ = lean_unsigned_to_nat(53u);
v___x_1116_ = lean_unsigned_to_nat(62u);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1119_ = l_mkPanicMessageWithDecl(v___x_1118_, v___x_1117_, v___x_1116_, v___x_1115_, v___x_1114_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1120_, size_t v_i_1121_, lean_object* v_bs_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_usize_dec_lt(v_i_1121_, v_sz_1120_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_bs_1122_);
return v___x_1133_;
}
else
{
lean_object* v_v_1134_; lean_object* v___x_1135_; 
v_v_1134_ = lean_array_uget_borrowed(v_bs_1122_, v_i_1121_);
lean_inc(v_v_1134_);
v___x_1135_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1134_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v_bs_x27_1138_; lean_object* v_a_1140_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v_bs_x27_1138_ = lean_array_uset(v_bs_1122_, v_i_1121_, v___x_1137_);
if (lean_obj_tag(v_a_1136_) == 6)
{
lean_object* v_val_1145_; lean_object* v_numFields_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_val_1145_ = lean_ctor_get(v_a_1136_, 0);
lean_inc_ref(v_val_1145_);
lean_dec_ref(v_a_1136_);
v_numFields_1146_ = lean_ctor_get(v_val_1145_, 4);
lean_inc(v_numFields_1146_);
lean_dec_ref(v_val_1145_);
v___x_1147_ = 0;
v___x_1148_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1148_, 0, v_numFields_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1137_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*2, v___x_1147_);
v_a_1140_ = v___x_1148_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_a_1136_);
v___x_1149_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1150_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1149_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v_a_1140_ = v_a_1151_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_bs_x27_1138_);
v_a_1152_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1150_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1150_);
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
v___jp_1139_:
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1121_, v___x_1141_);
v___x_1143_ = lean_array_uset(v_bs_x27_1138_, v_i_1121_, v_a_1140_);
v_i_1121_ = v___x_1142_;
v_bs_1122_ = v___x_1143_;
goto _start;
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_bs_1122_);
v_a_1160_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1135_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1135_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_bs_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
size_t v_sz_boxed_1180_; size_t v_i_boxed_1181_; lean_object* v_res_1182_; 
v_sz_boxed_1180_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1181_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1180_, v_i_boxed_1181_, v_bs_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v___y_1171_);
return v_res_1182_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1183_; lean_object* v_dummy_1184_; 
v___x_1183_ = lean_box(0);
v_dummy_1184_ = l_Lean_Expr_sort___override(v___x_1183_);
return v_dummy_1184_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_unsigned_to_nat(16u);
v___x_1187_ = lean_mk_array(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1193_, uint8_t v_alsoCasesOn_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_Expr_isApp(v_e_1193_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_e_1193_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Expr_getAppFn(v_e_1193_);
if (lean_obj_tag(v___x_1210_) == 4)
{
lean_object* v_declName_1211_; lean_object* v_us_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1368_; 
v_declName_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_n(v_declName_1211_, 2);
v_us_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_us_1212_);
lean_dec_ref(v___x_1210_);
v___x_1213_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1211_, v___y_1202_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1368_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1368_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
if (lean_obj_tag(v_a_1214_) == 1)
{
lean_object* v_val_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1260_; 
v_val_1218_ = lean_ctor_get(v_a_1214_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1220_ = v_a_1214_;
v_isShared_1221_ = v_isSharedCheck_1260_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_val_1218_);
lean_dec(v_a_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1260_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_dummy_1222_; lean_object* v_nargs_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_args_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_dummy_1222_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1223_ = l_Lean_Expr_getAppNumArgs(v_e_1193_);
lean_inc(v_nargs_1223_);
v___x_1224_ = lean_mk_array(v_nargs_1223_, v_dummy_1222_);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_sub(v_nargs_1223_, v___x_1225_);
lean_dec(v_nargs_1223_);
v_args_1227_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1193_, v___x_1224_, v___x_1226_);
v___x_1228_ = lean_array_get_size(v_args_1227_);
v___x_1229_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1218_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v_numParams_1231_; lean_object* v_numDiscrs_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v_numParams_1231_ = lean_ctor_get(v_val_1218_, 0);
v_numDiscrs_1232_ = lean_ctor_get(v_val_1218_, 1);
v___x_1233_ = lean_array_mk(v_us_1212_);
v___x_1234_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1231_);
v___x_1235_ = l_Array_extract___redArg(v_args_1227_, v___x_1234_, v_numParams_1231_);
v___x_1236_ = l_Lean_instInhabitedExpr;
v___x_1237_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1218_);
v___x_1238_ = lean_array_get(v___x_1236_, v_args_1227_, v___x_1237_);
lean_dec(v___x_1237_);
v___x_1239_ = lean_nat_add(v_numParams_1231_, v___x_1225_);
v___x_1240_ = lean_nat_add(v___x_1239_, v_numDiscrs_1232_);
lean_inc(v___x_1240_);
lean_inc_ref_n(v_args_1227_, 2);
v___x_1241_ = l_Array_toSubarray___redArg(v_args_1227_, v___x_1239_, v___x_1240_);
v___x_1242_ = l_Subarray_copy___redArg(v___x_1241_);
v___x_1243_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1218_);
v___x_1244_ = lean_nat_add(v___x_1240_, v___x_1243_);
lean_dec(v___x_1243_);
lean_inc(v___x_1244_);
v___x_1245_ = l_Array_toSubarray___redArg(v_args_1227_, v___x_1240_, v___x_1244_);
v___x_1246_ = l_Subarray_copy___redArg(v___x_1245_);
v___x_1247_ = l_Array_toSubarray___redArg(v_args_1227_, v___x_1244_, v___x_1228_);
v___x_1248_ = l_Subarray_copy___redArg(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1249_, 0, v_val_1218_);
lean_ctor_set(v___x_1249_, 1, v_declName_1211_);
lean_ctor_set(v___x_1249_, 2, v___x_1233_);
lean_ctor_set(v___x_1249_, 3, v___x_1235_);
lean_ctor_set(v___x_1249_, 4, v___x_1238_);
lean_ctor_set(v___x_1249_, 5, v___x_1242_);
lean_ctor_set(v___x_1249_, 6, v___x_1246_);
lean_ctor_set(v___x_1249_, 7, v___x_1248_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1249_);
v___x_1251_ = v___x_1220_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1251_);
v___x_1253_ = v___x_1216_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec_ref(v_args_1227_);
lean_del_object(v___x_1220_);
lean_dec(v_val_1218_);
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
v___x_1256_ = lean_box(0);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1256_);
v___x_1258_ = v___x_1216_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v___x_1261_; 
lean_del_object(v___x_1216_);
lean_dec(v_a_1214_);
v___x_1261_ = lean_st_ref_get(v___y_1202_);
if (v_alsoCasesOn_1194_ == 0)
{
lean_dec(v___x_1261_);
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
lean_dec_ref(v_e_1193_);
goto v___jp_1204_;
}
else
{
lean_object* v_env_1262_; uint8_t v___x_1263_; 
v_env_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref(v_env_1262_);
lean_dec(v___x_1261_);
lean_inc(v_declName_1211_);
v___x_1263_ = l_Lean_isCasesOnRecursor(v_env_1262_, v_declName_1211_);
if (v___x_1263_ == 0)
{
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
lean_dec_ref(v_e_1193_);
goto v___jp_1204_;
}
else
{
lean_object* v_indName_1264_; lean_object* v___x_1265_; 
v_indName_1264_ = l_Lean_Name_getPrefix(v_declName_1211_);
v___x_1265_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1264_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1359_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1359_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1359_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 5)
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1354_; 
v_val_1270_ = lean_ctor_get(v_a_1266_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1266_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1272_ = v_a_1266_;
v_isShared_1273_ = v_isSharedCheck_1354_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v_a_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1354_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_toConstantVal_1274_; lean_object* v_numParams_1275_; lean_object* v_numIndices_1276_; lean_object* v_ctors_1277_; lean_object* v_nargs_1278_; lean_object* v_dummy_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_args_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_toConstantVal_1274_ = lean_ctor_get(v_val_1270_, 0);
lean_inc_ref(v_toConstantVal_1274_);
v_numParams_1275_ = lean_ctor_get(v_val_1270_, 1);
lean_inc(v_numParams_1275_);
v_numIndices_1276_ = lean_ctor_get(v_val_1270_, 2);
lean_inc(v_numIndices_1276_);
v_ctors_1277_ = lean_ctor_get(v_val_1270_, 4);
lean_inc(v_ctors_1277_);
v_nargs_1278_ = l_Lean_Expr_getAppNumArgs(v_e_1193_);
v_dummy_1279_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1278_);
v___x_1280_ = lean_mk_array(v_nargs_1278_, v_dummy_1279_);
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_sub(v_nargs_1278_, v___x_1281_);
lean_dec(v_nargs_1278_);
v_args_1283_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1193_, v___x_1280_, v___x_1282_);
v___x_1284_ = lean_nat_add(v_numParams_1275_, v___x_1281_);
v___x_1285_ = lean_nat_add(v___x_1284_, v_numIndices_1276_);
v___x_1286_ = lean_nat_add(v___x_1285_, v___x_1281_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_InductiveVal_numCtors(v_val_1270_);
lean_dec_ref(v_val_1270_);
v___x_1288_ = lean_nat_add(v___x_1286_, v___x_1287_);
lean_dec(v___x_1287_);
v___x_1289_ = lean_array_get_size(v_args_1283_);
v___x_1290_ = lean_nat_dec_le(v___x_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v___x_1288_);
lean_dec(v___x_1286_);
lean_dec(v___x_1284_);
lean_dec_ref(v_args_1283_);
lean_dec(v_ctors_1277_);
lean_dec(v_numIndices_1276_);
lean_dec(v_numParams_1275_);
lean_dec_ref(v_toConstantVal_1274_);
lean_del_object(v___x_1272_);
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
v___x_1291_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1291_);
v___x_1293_ = v___x_1268_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1295_; lean_object* v_params_1296_; lean_object* v___x_1297_; lean_object* v_motive_1298_; lean_object* v_discrs_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_discrInfos_1302_; lean_object* v_alts_1303_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v_lower_1345_; lean_object* v_upper_1346_; uint8_t v___x_1353_; 
lean_del_object(v___x_1268_);
v___x_1295_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1275_);
lean_inc_ref_n(v_args_1283_, 3);
v_params_1296_ = l_Array_toSubarray___redArg(v_args_1283_, v___x_1295_, v_numParams_1275_);
v___x_1297_ = l_Lean_instInhabitedExpr;
v_motive_1298_ = lean_array_get(v___x_1297_, v_args_1283_, v_numParams_1275_);
lean_dec(v_numParams_1275_);
lean_inc(v___x_1286_);
v_discrs_1299_ = l_Array_toSubarray___redArg(v_args_1283_, v___x_1284_, v___x_1286_);
v___x_1300_ = lean_nat_add(v_numIndices_1276_, v___x_1281_);
lean_dec(v_numIndices_1276_);
v___x_1301_ = lean_box(0);
v_discrInfos_1302_ = lean_mk_array(v___x_1300_, v___x_1301_);
lean_inc(v___x_1288_);
v_alts_1303_ = l_Array_toSubarray___redArg(v_args_1283_, v___x_1286_, v___x_1288_);
v___x_1353_ = lean_nat_dec_le(v___x_1288_, v___x_1295_);
if (v___x_1353_ == 0)
{
v_lower_1345_ = v___x_1288_;
v_upper_1346_ = v___x_1289_;
goto v___jp_1344_;
}
else
{
lean_dec(v___x_1288_);
v_lower_1345_ = v___x_1295_;
v_upper_1346_ = v___x_1289_;
goto v___jp_1344_;
}
v___jp_1304_:
{
lean_object* v___x_1307_; size_t v_sz_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_array_mk(v_ctors_1277_);
v_sz_1308_ = lean_array_size(v___x_1307_);
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1308_, v___x_1309_, v___x_1307_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1335_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1335_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1335_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_start_1315_; lean_object* v_stop_1316_; lean_object* v_start_1317_; lean_object* v_stop_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v_start_1315_ = lean_ctor_get(v_params_1296_, 1);
lean_inc(v_start_1315_);
v_stop_1316_ = lean_ctor_get(v_params_1296_, 2);
lean_inc(v_stop_1316_);
v_start_1317_ = lean_ctor_get(v_discrs_1299_, 1);
lean_inc(v_start_1317_);
v_stop_1318_ = lean_ctor_get(v_discrs_1299_, 2);
lean_inc(v_stop_1318_);
v___x_1319_ = lean_nat_sub(v_stop_1316_, v_start_1315_);
lean_dec(v_start_1315_);
lean_dec(v_stop_1316_);
v___x_1320_ = lean_nat_sub(v_stop_1318_, v_start_1317_);
lean_dec(v_start_1317_);
lean_dec(v_stop_1318_);
v___x_1321_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1319_);
lean_ctor_set(v___x_1322_, 1, v___x_1320_);
lean_ctor_set(v___x_1322_, 2, v_a_1311_);
lean_ctor_set(v___x_1322_, 3, v___y_1306_);
lean_ctor_set(v___x_1322_, 4, v_discrInfos_1302_);
lean_ctor_set(v___x_1322_, 5, v___x_1321_);
v___x_1323_ = lean_array_mk(v_us_1212_);
v___x_1324_ = l_Subarray_copy___redArg(v_params_1296_);
v___x_1325_ = l_Subarray_copy___redArg(v_discrs_1299_);
v___x_1326_ = l_Subarray_copy___redArg(v_alts_1303_);
v___x_1327_ = l_Subarray_copy___redArg(v___y_1305_);
v___x_1328_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1322_);
lean_ctor_set(v___x_1328_, 1, v_declName_1211_);
lean_ctor_set(v___x_1328_, 2, v___x_1323_);
lean_ctor_set(v___x_1328_, 3, v___x_1324_);
lean_ctor_set(v___x_1328_, 4, v_motive_1298_);
lean_ctor_set(v___x_1328_, 5, v___x_1325_);
lean_ctor_set(v___x_1328_, 6, v___x_1326_);
lean_ctor_set(v___x_1328_, 7, v___x_1327_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1328_);
v___x_1330_ = v___x_1272_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1330_);
v___x_1332_ = v___x_1313_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
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
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_alts_1303_);
lean_dec_ref(v_discrInfos_1302_);
lean_dec_ref(v_discrs_1299_);
lean_dec(v_motive_1298_);
lean_dec_ref(v_params_1296_);
lean_del_object(v___x_1272_);
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
v_a_1336_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1310_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1310_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
v___jp_1344_:
{
lean_object* v_levelParams_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_levelParams_1347_ = lean_ctor_get(v_toConstantVal_1274_, 1);
lean_inc(v_levelParams_1347_);
lean_dec_ref(v_toConstantVal_1274_);
v___x_1348_ = l_Array_toSubarray___redArg(v_args_1283_, v_lower_1345_, v_upper_1346_);
v___x_1349_ = l_List_lengthTR___redArg(v_levelParams_1347_);
lean_dec(v_levelParams_1347_);
v___x_1350_ = l_List_lengthTR___redArg(v_us_1212_);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
lean_dec(v___x_1350_);
lean_dec(v___x_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1305_ = v___x_1348_;
v___y_1306_ = v___x_1352_;
goto v___jp_1304_;
}
else
{
v___y_1305_ = v___x_1348_;
v___y_1306_ = v___x_1301_;
goto v___jp_1304_;
}
}
}
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec(v_a_1266_);
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
lean_dec_ref(v_e_1193_);
v___x_1355_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1355_);
v___x_1357_ = v___x_1268_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_us_1212_);
lean_dec(v_declName_1211_);
lean_dec_ref(v_e_1193_);
v_a_1360_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1265_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1265_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
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
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_e_1193_);
goto v___jp_1204_;
}
}
v___jp_1204_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1369_, lean_object* v_alsoCasesOn_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1380_; lean_object* v_res_1381_; 
v_alsoCasesOn_boxed_1380_ = lean_unbox(v_alsoCasesOn_1370_);
v_res_1381_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1369_, v_alsoCasesOn_boxed_1380_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec(v___y_1371_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v_b_1387_, lean_object* v_c_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc(v___y_1383_);
v___x_1394_ = lean_apply_11(v_k_1382_, v_b_1387_, v_c_1388_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, lean_box(0));
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v_b_1400_, lean_object* v_c_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v_b_1400_, v_c_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1408_, lean_object* v_maxFVars_1409_, lean_object* v_k_1410_, uint8_t v_cleanupAnnotations_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___f_1421_; uint8_t v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc(v___y_1412_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1421_, 0, v_k_1410_);
lean_closure_set(v___f_1421_, 1, v___y_1412_);
lean_closure_set(v___f_1421_, 2, v___y_1413_);
lean_closure_set(v___f_1421_, 3, v___y_1414_);
lean_closure_set(v___f_1421_, 4, v___y_1415_);
v___x_1422_ = 1;
v___x_1423_ = 0;
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_maxFVars_1409_);
v___x_1425_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1408_, v___x_1422_, v___x_1423_, v___x_1422_, v___x_1423_, v___x_1424_, v___f_1421_, v_cleanupAnnotations_1411_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec_ref(v___x_1424_);
if (lean_obj_tag(v___x_1425_) == 0)
{
return v___x_1425_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1434_, lean_object* v_maxFVars_1435_, lean_object* v_k_1436_, lean_object* v_cleanupAnnotations_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1447_; lean_object* v_res_1448_; 
v_cleanupAnnotations_boxed_1447_ = lean_unbox(v_cleanupAnnotations_1437_);
v_res_1448_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1434_, v_maxFVars_1435_, v_k_1436_, v_cleanupAnnotations_boxed_1447_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc(v___y_1450_);
v___x_1460_ = lean_apply_10(v_k_1449_, v_b_1454_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, lean_box(0));
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1473_, lean_object* v_type_1474_, lean_object* v_val_1475_, lean_object* v_k_1476_, uint8_t v_nondep_1477_, uint8_t v_kind_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___f_1488_; lean_object* v___x_1489_; 
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc(v___y_1479_);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1488_, 0, v_k_1476_);
lean_closure_set(v___f_1488_, 1, v___y_1479_);
lean_closure_set(v___f_1488_, 2, v___y_1480_);
lean_closure_set(v___f_1488_, 3, v___y_1481_);
lean_closure_set(v___f_1488_, 4, v___y_1482_);
v___x_1489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1473_, v_type_1474_, v_val_1475_, v___f_1488_, v_nondep_1477_, v_kind_1478_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1489_) == 0)
{
return v___x_1489_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1498_, lean_object* v_type_1499_, lean_object* v_val_1500_, lean_object* v_k_1501_, lean_object* v_nondep_1502_, lean_object* v_kind_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v_nondep_boxed_1513_; uint8_t v_kind_boxed_1514_; lean_object* v_res_1515_; 
v_nondep_boxed_1513_ = lean_unbox(v_nondep_1502_);
v_kind_boxed_1514_ = lean_unbox(v_kind_1503_);
v_res_1515_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1498_, v_type_1499_, v_val_1500_, v_k_1501_, v_nondep_boxed_1513_, v_kind_boxed_1514_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1516_, uint8_t v_usedLetOnly_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v_x_1518_);
v___x_1528_ = lean_apply_10(v_k_1516_, v_x_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, lean_box(0));
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_array_push(v___x_1531_, v_x_1518_);
v___x_1533_ = 0;
v___x_1534_ = 1;
v___x_1535_ = l_Lean_Meta_mkLetFVars(v___x_1532_, v_a_1529_, v_usedLetOnly_1517_, v___x_1533_, v___x_1534_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec_ref(v___x_1532_);
return v___x_1535_;
}
else
{
lean_dec_ref(v_x_1518_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1536_, lean_object* v_usedLetOnly_1537_, lean_object* v_x_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
uint8_t v_usedLetOnly_boxed_1548_; lean_object* v_res_1549_; 
v_usedLetOnly_boxed_1548_ = lean_unbox(v_usedLetOnly_1537_);
v_res_1549_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1536_, v_usedLetOnly_boxed_1548_, v_x_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1550_, lean_object* v_type_1551_, lean_object* v_val_1552_, lean_object* v_k_1553_, uint8_t v_nondep_1554_, uint8_t v_kind_1555_, uint8_t v_usedLetOnly_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_box(v_usedLetOnly_1556_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1567_, 0, v_k_1553_);
lean_closure_set(v___f_1567_, 1, v___x_1566_);
v___x_1568_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1550_, v_type_1551_, v_val_1552_, v___f_1567_, v_nondep_1554_, v_kind_1555_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1569_, lean_object* v_type_1570_, lean_object* v_val_1571_, lean_object* v_k_1572_, lean_object* v_nondep_1573_, lean_object* v_kind_1574_, lean_object* v_usedLetOnly_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v_nondep_boxed_1585_; uint8_t v_kind_boxed_1586_; uint8_t v_usedLetOnly_boxed_1587_; lean_object* v_res_1588_; 
v_nondep_boxed_1585_ = lean_unbox(v_nondep_1573_);
v_kind_boxed_1586_ = lean_unbox(v_kind_1574_);
v_usedLetOnly_boxed_1587_ = lean_unbox(v_usedLetOnly_1575_);
v_res_1588_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1569_, v_type_1570_, v_val_1571_, v_k_1572_, v_nondep_boxed_1585_, v_kind_boxed_1586_, v_usedLetOnly_boxed_1587_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec(v___y_1576_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1589_, uint8_t v_bi_1590_, lean_object* v_type_1591_, lean_object* v_k_1592_, uint8_t v_kind_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___f_1603_; lean_object* v___x_1604_; 
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
lean_inc(v___y_1595_);
lean_inc(v___y_1594_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1603_, 0, v_k_1592_);
lean_closure_set(v___f_1603_, 1, v___y_1594_);
lean_closure_set(v___f_1603_, 2, v___y_1595_);
lean_closure_set(v___f_1603_, 3, v___y_1596_);
lean_closure_set(v___f_1603_, 4, v___y_1597_);
v___x_1604_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1589_, v_bi_1590_, v_type_1591_, v___f_1603_, v_kind_1593_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1604_) == 0)
{
return v___x_1604_;
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1613_, lean_object* v_bi_1614_, lean_object* v_type_1615_, lean_object* v_k_1616_, lean_object* v_kind_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_bi_boxed_1627_; uint8_t v_kind_boxed_1628_; lean_object* v_res_1629_; 
v_bi_boxed_1627_ = lean_unbox(v_bi_1614_);
v_kind_boxed_1628_ = lean_unbox(v_kind_1617_);
v_res_1629_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1613_, v_bi_boxed_1627_, v_type_1615_, v_k_1616_, v_kind_boxed_1628_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec(v___y_1618_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; 
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc(v___y_1631_);
v___x_1640_ = lean_apply_9(v_k_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, lean_box(0));
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec(v___y_1642_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1652_, uint8_t v_allowLevelAssignments_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___f_1663_; lean_object* v___x_1664_; 
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc(v___y_1654_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1663_, 0, v_k_1652_);
lean_closure_set(v___f_1663_, 1, v___y_1654_);
lean_closure_set(v___f_1663_, 2, v___y_1655_);
lean_closure_set(v___f_1663_, 3, v___y_1656_);
lean_closure_set(v___f_1663_, 4, v___y_1657_);
v___x_1664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1653_, v___f_1663_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1664_) == 0)
{
return v___x_1664_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1673_, lean_object* v_allowLevelAssignments_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1684_; lean_object* v_res_1685_; 
v_allowLevelAssignments_boxed_1684_ = lean_unbox(v_allowLevelAssignments_1674_);
v_res_1685_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1673_, v_allowLevelAssignments_boxed_1684_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec(v___y_1675_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_box(0);
return v___x_1688_;
}
else
{
lean_object* v_key_1689_; lean_object* v_value_1690_; lean_object* v_tail_1691_; uint8_t v___x_1692_; 
v_key_1689_ = lean_ctor_get(v_x_1687_, 0);
v_value_1690_ = lean_ctor_get(v_x_1687_, 1);
v_tail_1691_ = lean_ctor_get(v_x_1687_, 2);
v___x_1692_ = lean_expr_eqv(v_key_1689_, v_a_1686_);
if (v___x_1692_ == 0)
{
v_x_1687_ = v_tail_1691_;
goto _start;
}
else
{
lean_object* v___x_1694_; 
lean_inc(v_value_1690_);
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_value_1690_);
return v___x_1694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1695_, v_x_1696_);
lean_dec(v_x_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_buckets_1700_; lean_object* v___x_1701_; uint64_t v___x_1702_; uint64_t v___x_1703_; uint64_t v___x_1704_; uint64_t v_fold_1705_; uint64_t v___x_1706_; uint64_t v___x_1707_; uint64_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_buckets_1700_ = lean_ctor_get(v_m_1698_, 1);
v___x_1701_ = lean_array_get_size(v_buckets_1700_);
v___x_1702_ = l_Lean_Expr_hash(v_a_1699_);
v___x_1703_ = 32ULL;
v___x_1704_ = lean_uint64_shift_right(v___x_1702_, v___x_1703_);
v_fold_1705_ = lean_uint64_xor(v___x_1702_, v___x_1704_);
v___x_1706_ = 16ULL;
v___x_1707_ = lean_uint64_shift_right(v_fold_1705_, v___x_1706_);
v___x_1708_ = lean_uint64_xor(v_fold_1705_, v___x_1707_);
v___x_1709_ = lean_uint64_to_usize(v___x_1708_);
v___x_1710_ = lean_usize_of_nat(v___x_1701_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_sub(v___x_1710_, v___x_1711_);
v___x_1713_ = lean_usize_land(v___x_1709_, v___x_1712_);
v___x_1714_ = lean_array_uget_borrowed(v_buckets_1700_, v___x_1713_);
v___x_1715_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1699_, v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1716_, v_a_1717_);
lean_dec_ref(v_a_1717_);
lean_dec_ref(v_m_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1719_, lean_object* v_opt_1720_){
_start:
{
lean_object* v_name_1721_; lean_object* v_defValue_1722_; lean_object* v_map_1723_; lean_object* v___x_1724_; 
v_name_1721_ = lean_ctor_get(v_opt_1720_, 0);
v_defValue_1722_ = lean_ctor_get(v_opt_1720_, 1);
v_map_1723_ = lean_ctor_get(v_opts_1719_, 0);
v___x_1724_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1723_, v_name_1721_);
if (lean_obj_tag(v___x_1724_) == 0)
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_unbox(v_defValue_1722_);
return v___x_1725_;
}
else
{
lean_object* v_val_1726_; 
v_val_1726_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_val_1726_);
lean_dec_ref(v___x_1724_);
if (lean_obj_tag(v_val_1726_) == 1)
{
uint8_t v_v_1727_; 
v_v_1727_ = lean_ctor_get_uint8(v_val_1726_, 0);
lean_dec_ref(v_val_1726_);
return v_v_1727_;
}
else
{
uint8_t v___x_1728_; 
lean_dec(v_val_1726_);
v___x_1728_ = lean_unbox(v_defValue_1722_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1729_, lean_object* v_opt_1730_){
_start:
{
uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_res_1731_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1729_, v_opt_1730_);
lean_dec_ref(v_opt_1730_);
lean_dec_ref(v_opts_1729_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v_array_1735_; lean_object* v_start_1736_; lean_object* v_stop_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1750_; 
v_array_1735_ = lean_ctor_get(v_a_1733_, 0);
v_start_1736_ = lean_ctor_get(v_a_1733_, 1);
v_stop_1737_ = lean_ctor_get(v_a_1733_, 2);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_a_1733_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1739_ = v_a_1733_;
v_isShared_1740_ = v_isSharedCheck_1750_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_stop_1737_);
lean_inc(v_start_1736_);
lean_inc(v_array_1735_);
lean_dec(v_a_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1750_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_lt(v_start_1736_, v_stop_1737_);
if (v___x_1741_ == 0)
{
lean_del_object(v___x_1739_);
lean_dec(v_stop_1737_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
return v_b_1734_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_start_1736_, v___x_1742_);
lean_inc_ref(v_array_1735_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1743_);
v___x_1745_ = v___x_1739_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_array_1735_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_stop_1737_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_array_fget(v_array_1735_, v_start_1736_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
v___x_1747_ = lean_array_push(v_b_1734_, v___x_1746_);
v_a_1733_ = v___x_1745_;
v_b_1734_ = v___x_1747_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1751_, lean_object* v_recFnName_1752_, lean_object* v_fixedPrefixSize_1753_, lean_object* v_F_1754_, lean_object* v_x_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_expr_instantiate1(v_body_1751_, v_x_1755_);
v___x_1766_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1752_, v_fixedPrefixSize_1753_, v_F_1754_, v___x_1765_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
v___x_1770_ = lean_array_push(v___x_1769_, v_x_1755_);
v___x_1771_ = 0;
v___x_1772_ = 1;
v___x_1773_ = 1;
v___x_1774_ = l_Lean_Meta_mkLambdaFVars(v___x_1770_, v_a_1767_, v___x_1771_, v___x_1772_, v___x_1771_, v___x_1772_, v___x_1773_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec_ref(v___x_1770_);
return v___x_1774_;
}
else
{
lean_dec_ref(v_x_1755_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1775_, lean_object* v_recFnName_1776_, lean_object* v_fixedPrefixSize_1777_, lean_object* v_F_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1775_, v_recFnName_1776_, v_fixedPrefixSize_1777_, v_F_1778_, v_x_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v_body_1775_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1790_, lean_object* v_recFnName_1791_, lean_object* v_fixedPrefixSize_1792_, lean_object* v_F_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_expr_instantiate1(v_body_1790_, v_x_1794_);
v___x_1805_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1791_, v_fixedPrefixSize_1792_, v_F_1793_, v___x_1804_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
v___x_1809_ = lean_array_push(v___x_1808_, v_x_1794_);
v___x_1810_ = 0;
v___x_1811_ = 1;
v___x_1812_ = 1;
v___x_1813_ = l_Lean_Meta_mkForallFVars(v___x_1809_, v_a_1806_, v___x_1810_, v___x_1811_, v___x_1811_, v___x_1812_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec_ref(v___x_1809_);
return v___x_1813_;
}
else
{
lean_dec_ref(v_x_1794_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1814_, lean_object* v_recFnName_1815_, lean_object* v_fixedPrefixSize_1816_, lean_object* v_F_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1814_, v_recFnName_1815_, v_fixedPrefixSize_1816_, v_F_1817_, v_x_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v_body_1814_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1829_, lean_object* v_recFnName_1830_, lean_object* v_fixedPrefixSize_1831_, lean_object* v_F_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1829_, v_recFnName_1830_, v_fixedPrefixSize_1831_, v_F_1832_, v_x_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v_x_1833_);
lean_dec_ref(v_body_1829_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1846_, lean_object* v_fixedPrefixSize_1847_, lean_object* v_F_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_bs_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_F_1848_);
lean_dec(v_fixedPrefixSize_1847_);
lean_dec(v_recFnName_1846_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_bs_1851_);
return v___x_1862_;
}
else
{
lean_object* v_v_1863_; lean_object* v___x_1864_; 
v_v_1863_ = lean_array_uget_borrowed(v_bs_1851_, v_i_1850_);
lean_inc(v_v_1863_);
lean_inc_ref(v_F_1848_);
lean_inc(v_fixedPrefixSize_1847_);
lean_inc(v_recFnName_1846_);
v___x_1864_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1846_, v_fixedPrefixSize_1847_, v_F_1848_, v_v_1863_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; lean_object* v_bs_x27_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v_bs_x27_1867_ = lean_array_uset(v_bs_1851_, v_i_1850_, v___x_1866_);
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_i_1850_, v___x_1868_);
v___x_1870_ = lean_array_uset(v_bs_x27_1867_, v_i_1850_, v_a_1865_);
v_i_1850_ = v___x_1869_;
v_bs_1851_ = v___x_1870_;
goto _start;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_bs_1851_);
lean_dec_ref(v_F_1848_);
lean_dec(v_fixedPrefixSize_1847_);
lean_dec(v_recFnName_1846_);
v_a_1872_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1864_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1864_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_cls_1887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1888_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1889_ = l_Lean_Name_append(v___x_1888_, v_cls_1887_);
return v___x_1889_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1893_, lean_object* v_fixedPrefixSize_1894_, lean_object* v_F_1895_, lean_object* v_e_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1918_ = l_Lean_Expr_getAppNumArgs(v_e_1896_);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_add(v_fixedPrefixSize_1894_, v___x_1919_);
v___x_1921_ = lean_nat_dec_lt(v___x_1918_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v_dummy_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_args_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_dummy_1922_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1918_);
v___x_1923_ = lean_mk_array(v___x_1918_, v_dummy_1922_);
v___x_1924_ = lean_nat_sub(v___x_1918_, v___x_1919_);
lean_dec(v___x_1918_);
v_args_1925_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1896_, v___x_1923_, v___x_1924_);
v___x_1926_ = l_Lean_instInhabitedExpr;
v___x_1927_ = lean_array_get(v___x_1926_, v_args_1925_, v_fixedPrefixSize_1894_);
lean_inc_ref(v_F_1895_);
lean_inc(v_fixedPrefixSize_1894_);
lean_inc(v_recFnName_1893_);
v___x_1928_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1893_, v_fixedPrefixSize_1894_, v_F_1895_, v___x_1927_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
lean_inc_ref(v_F_1895_);
v___x_1930_ = l_Lean_Expr_app___override(v_F_1895_, v_a_1929_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1903_);
lean_inc(v_a_1902_);
lean_inc_ref(v_a_1901_);
lean_inc_ref(v___x_1930_);
v___x_1931_ = lean_infer_type(v___x_1930_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1903_);
lean_inc(v_a_1902_);
lean_inc_ref(v_a_1901_);
v___x_1933_ = lean_whnf(v_a_1932_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = l_Lean_Expr_bindingDomain_x21(v_a_1934_);
lean_dec(v_a_1934_);
v___x_1936_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1935_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v_lower_1940_; lean_object* v_upper_1941_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_Lean_Expr_app___override(v___x_1930_, v_a_1937_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get_size(v_args_1925_);
v___x_1967_ = lean_nat_dec_le(v___x_1920_, v___x_1965_);
if (v___x_1967_ == 0)
{
v_lower_1940_ = v___x_1920_;
v_upper_1941_ = v___x_1966_;
goto v___jp_1939_;
}
else
{
lean_dec(v___x_1920_);
v_lower_1940_ = v___x_1965_;
v_upper_1941_ = v___x_1966_;
goto v___jp_1939_;
}
v___jp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; size_t v_sz_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1942_ = l_Array_toSubarray___redArg(v_args_1925_, v_lower_1940_, v_upper_1941_);
v___x_1943_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1944_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1942_, v___x_1943_);
v_sz_1945_ = lean_array_size(v___x_1944_);
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1893_, v_fixedPrefixSize_1894_, v_F_1895_, v_sz_1945_, v___x_1946_, v___x_1944_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_mkAppN(v___x_1938_, v_a_1948_);
lean_dec(v_a_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v___x_1938_);
v_a_1957_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1947_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1947_);
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
else
{
lean_dec_ref(v___x_1930_);
lean_dec_ref(v_args_1925_);
lean_dec(v___x_1920_);
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
return v___x_1936_;
}
}
else
{
lean_dec_ref(v___x_1930_);
lean_dec_ref(v_args_1925_);
lean_dec(v___x_1920_);
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
return v___x_1933_;
}
}
else
{
lean_dec_ref(v___x_1930_);
lean_dec_ref(v_args_1925_);
lean_dec(v___x_1920_);
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v_args_1925_);
lean_dec(v___x_1920_);
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
return v___x_1928_;
}
}
else
{
lean_object* v_options_1968_; uint8_t v_hasTrace_1969_; 
lean_dec(v___x_1920_);
lean_dec(v___x_1918_);
v_options_1968_ = lean_ctor_get(v_a_1903_, 2);
v_hasTrace_1969_ = lean_ctor_get_uint8(v_options_1968_, sizeof(void*)*1);
if (v_hasTrace_1969_ == 0)
{
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
goto v___jp_1906_;
}
else
{
lean_object* v_inheritedTraceOptions_1970_; lean_object* v_cls_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_inheritedTraceOptions_1970_ = lean_ctor_get(v_a_1903_, 13);
v_cls_1971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1972_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1973_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1970_, v_options_1968_, v___x_1972_);
if (v___x_1973_ == 0)
{
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1896_);
v___x_1975_ = l_Lean_indentExpr(v_e_1896_);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1971_, v___x_1976_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_dec_ref(v___x_1977_);
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_e_1896_);
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
v___jp_1906_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_etaExpand(v_e_1896_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1893_, v_fixedPrefixSize_1894_, v_F_1895_, v_a_1916_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
return v___x_1917_;
}
else
{
lean_dec_ref(v_F_1895_);
lean_dec(v_fixedPrefixSize_1894_);
lean_dec(v_recFnName_1893_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1986_, lean_object* v_fixedPrefixSize_1987_, lean_object* v_F_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 5)
{
lean_object* v_fn_2001_; lean_object* v_arg_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_fn_2001_ = lean_ctor_get(v_x_1989_, 0);
lean_inc_ref(v_fn_2001_);
v_arg_2002_ = lean_ctor_get(v_x_1989_, 1);
lean_inc_ref(v_arg_2002_);
lean_dec_ref(v_x_1989_);
v___x_2003_ = lean_array_set(v_x_1990_, v_x_1991_, v_arg_2002_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_sub(v_x_1991_, v___x_2004_);
lean_dec(v_x_1991_);
v_x_1989_ = v_fn_2001_;
v_x_1990_ = v___x_2003_;
v_x_1991_ = v___x_2005_;
goto _start;
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_x_1991_);
lean_inc_ref(v_F_1988_);
lean_inc(v_fixedPrefixSize_1987_);
lean_inc(v_recFnName_1986_);
v___x_2007_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1986_, v_fixedPrefixSize_1987_, v_F_1988_, v_x_1989_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; size_t v_sz_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v_sz_2009_ = lean_array_size(v_x_1990_);
v___x_2010_ = ((size_t)0ULL);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1986_, v_fixedPrefixSize_1987_, v_F_1988_, v_sz_2009_, v___x_2010_, v_x_1990_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = l_Lean_mkAppN(v_a_2008_, v_a_2012_);
lean_dec(v_a_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_2008_);
v_a_2021_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2011_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2011_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_dec_ref(v_x_1990_);
lean_dec_ref(v_F_1988_);
lean_dec(v_fixedPrefixSize_1987_);
lean_dec(v_recFnName_1986_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2029_, lean_object* v_fixedPrefixSize_2030_, lean_object* v_F_2031_, lean_object* v_e_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_isAppOf(v_e_2032_, v_recFnName_2029_);
if (v___x_2042_ == 0)
{
lean_object* v_dummy_2043_; lean_object* v_nargs_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_dummy_2043_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2044_ = l_Lean_Expr_getAppNumArgs(v_e_2032_);
lean_inc(v_nargs_2044_);
v___x_2045_ = lean_mk_array(v_nargs_2044_, v_dummy_2043_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_sub(v_nargs_2044_, v___x_2046_);
lean_dec(v_nargs_2044_);
v___x_2048_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2029_, v_fixedPrefixSize_2030_, v_F_2031_, v_e_2032_, v___x_2045_, v___x_2047_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2029_, v_fixedPrefixSize_2030_, v_F_2031_, v_e_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2049_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2056_, lean_object* v_b_2057_, lean_object* v_recFnName_2058_, lean_object* v_fixedPrefixSize_2059_, uint8_t v___x_2060_, lean_object* v___x_2061_, lean_object* v_a_2062_, lean_object* v_e_2063_, lean_object* v_xs_2064_, lean_object* v_altBody_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_array_get_size(v_xs_2064_);
v___x_2083_ = lean_nat_dec_eq(v___x_2082_, v___x_2061_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_altBody_2065_);
lean_dec(v_fixedPrefixSize_2059_);
lean_dec(v_recFnName_2058_);
v___x_2084_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2085_ = l_Lean_indentExpr(v_a_2062_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_indentExpr(v_e_2063_);
v___x_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2090_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_dec_ref(v_e_2063_);
lean_dec_ref(v_a_2062_);
goto v___jp_2075_;
}
v___jp_2075_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_array_get_borrowed(v___x_2056_, v_xs_2064_, v_b_2057_);
lean_inc(v___x_2076_);
v___x_2077_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2058_, v_fixedPrefixSize_2059_, v___x_2076_, v_altBody_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = 0;
v___x_2080_ = 1;
v___x_2081_ = l_Lean_Meta_mkLambdaFVars(v_xs_2064_, v_a_2078_, v___x_2079_, v___x_2060_, v___x_2079_, v___x_2060_, v___x_2080_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2081_;
}
else
{
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2100_ = _args[0];
lean_object* v_b_2101_ = _args[1];
lean_object* v_recFnName_2102_ = _args[2];
lean_object* v_fixedPrefixSize_2103_ = _args[3];
lean_object* v___x_2104_ = _args[4];
lean_object* v___x_2105_ = _args[5];
lean_object* v_a_2106_ = _args[6];
lean_object* v_e_2107_ = _args[7];
lean_object* v_xs_2108_ = _args[8];
lean_object* v_altBody_2109_ = _args[9];
lean_object* v___y_2110_ = _args[10];
lean_object* v___y_2111_ = _args[11];
lean_object* v___y_2112_ = _args[12];
lean_object* v___y_2113_ = _args[13];
lean_object* v___y_2114_ = _args[14];
lean_object* v___y_2115_ = _args[15];
lean_object* v___y_2116_ = _args[16];
lean_object* v___y_2117_ = _args[17];
lean_object* v___y_2118_ = _args[18];
_start:
{
uint8_t v___x_67130__boxed_2119_; lean_object* v_res_2120_; 
v___x_67130__boxed_2119_ = lean_unbox(v___x_2104_);
v_res_2120_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2100_, v_b_2101_, v_recFnName_2102_, v_fixedPrefixSize_2103_, v___x_67130__boxed_2119_, v___x_2105_, v_a_2106_, v_e_2107_, v_xs_2108_, v_altBody_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v_xs_2108_);
lean_dec(v___x_2105_);
lean_dec(v_b_2101_);
lean_dec_ref(v___x_2100_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2121_, lean_object* v_fixedPrefixSize_2122_, lean_object* v_e_2123_, lean_object* v_as_2124_, lean_object* v_bs_2125_, lean_object* v_i_2126_, lean_object* v_cs_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_array_get_size(v_as_2124_);
v___x_2138_ = lean_nat_dec_lt(v_i_2126_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_dec(v_i_2126_);
lean_dec_ref(v_e_2123_);
lean_dec(v_fixedPrefixSize_2122_);
lean_dec(v_recFnName_2121_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_cs_2127_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_array_get_size(v_bs_2125_);
v___x_2141_ = lean_nat_dec_lt(v_i_2126_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v_i_2126_);
lean_dec_ref(v_e_2123_);
lean_dec(v_fixedPrefixSize_2122_);
lean_dec(v_recFnName_2121_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_cs_2127_);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; lean_object* v_a_2144_; lean_object* v_b_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2143_ = l_Lean_instInhabitedExpr;
v_a_2144_ = lean_array_fget_borrowed(v_as_2124_, v_i_2126_);
v_b_2145_ = lean_array_fget_borrowed(v_bs_2125_, v_i_2126_);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_b_2145_, v___x_2146_);
v___x_2148_ = lean_box(v___x_2141_);
lean_inc_ref(v_e_2123_);
lean_inc_n(v_a_2144_, 2);
lean_inc(v___x_2147_);
lean_inc(v_fixedPrefixSize_2122_);
lean_inc(v_recFnName_2121_);
lean_inc(v_b_2145_);
v___f_2149_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2149_, 0, v___x_2143_);
lean_closure_set(v___f_2149_, 1, v_b_2145_);
lean_closure_set(v___f_2149_, 2, v_recFnName_2121_);
lean_closure_set(v___f_2149_, 3, v_fixedPrefixSize_2122_);
lean_closure_set(v___f_2149_, 4, v___x_2148_);
lean_closure_set(v___f_2149_, 5, v___x_2147_);
lean_closure_set(v___f_2149_, 6, v_a_2144_);
lean_closure_set(v___f_2149_, 7, v_e_2123_);
v___x_2150_ = 0;
v___x_2151_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2144_, v___x_2147_, v___f_2149_, v___x_2150_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = lean_nat_add(v_i_2126_, v___x_2146_);
lean_dec(v_i_2126_);
v___x_2154_ = lean_array_push(v_cs_2127_, v_a_2152_);
v_i_2126_ = v___x_2153_;
v_cs_2127_ = v___x_2154_;
goto _start;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_cs_2127_);
lean_dec(v_i_2126_);
lean_dec_ref(v_e_2123_);
lean_dec(v_fixedPrefixSize_2122_);
lean_dec(v_recFnName_2121_);
v_a_2156_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2151_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2151_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2164_, lean_object* v_fixedPrefixSize_2165_, lean_object* v_F_2166_, lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
switch(lean_obj_tag(v_e_2167_))
{
case 6:
{
lean_object* v_binderName_2177_; lean_object* v_binderType_2178_; lean_object* v_body_2179_; uint8_t v_binderInfo_2180_; lean_object* v___x_2181_; 
v_binderName_2177_ = lean_ctor_get(v_e_2167_, 0);
lean_inc(v_binderName_2177_);
v_binderType_2178_ = lean_ctor_get(v_e_2167_, 1);
lean_inc_ref(v_binderType_2178_);
v_body_2179_ = lean_ctor_get(v_e_2167_, 2);
lean_inc_ref(v_body_2179_);
v_binderInfo_2180_ = lean_ctor_get_uint8(v_e_2167_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2167_);
lean_inc_ref(v_F_2166_);
lean_inc(v_fixedPrefixSize_2165_);
lean_inc(v_recFnName_2164_);
v___x_2181_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_binderType_2178_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___f_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2183_, 0, v_body_2179_);
lean_closure_set(v___f_2183_, 1, v_recFnName_2164_);
lean_closure_set(v___f_2183_, 2, v_fixedPrefixSize_2165_);
lean_closure_set(v___f_2183_, 3, v_F_2166_);
v___x_2184_ = 0;
v___x_2185_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2177_, v_binderInfo_2180_, v_a_2182_, v___f_2183_, v___x_2184_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2185_;
}
else
{
lean_dec_ref(v_body_2179_);
lean_dec(v_binderName_2177_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
return v___x_2181_;
}
}
case 7:
{
lean_object* v_binderName_2186_; lean_object* v_binderType_2187_; lean_object* v_body_2188_; uint8_t v_binderInfo_2189_; lean_object* v___x_2190_; 
v_binderName_2186_ = lean_ctor_get(v_e_2167_, 0);
lean_inc(v_binderName_2186_);
v_binderType_2187_ = lean_ctor_get(v_e_2167_, 1);
lean_inc_ref(v_binderType_2187_);
v_body_2188_ = lean_ctor_get(v_e_2167_, 2);
lean_inc_ref(v_body_2188_);
v_binderInfo_2189_ = lean_ctor_get_uint8(v_e_2167_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2167_);
lean_inc_ref(v_F_2166_);
lean_inc(v_fixedPrefixSize_2165_);
lean_inc(v_recFnName_2164_);
v___x_2190_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_binderType_2187_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___f_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___f_2192_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2192_, 0, v_body_2188_);
lean_closure_set(v___f_2192_, 1, v_recFnName_2164_);
lean_closure_set(v___f_2192_, 2, v_fixedPrefixSize_2165_);
lean_closure_set(v___f_2192_, 3, v_F_2166_);
v___x_2193_ = 0;
v___x_2194_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2186_, v_binderInfo_2189_, v_a_2191_, v___f_2192_, v___x_2193_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2194_;
}
else
{
lean_dec_ref(v_body_2188_);
lean_dec(v_binderName_2186_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
return v___x_2190_;
}
}
case 8:
{
lean_object* v_declName_2195_; lean_object* v_type_2196_; lean_object* v_value_2197_; lean_object* v_body_2198_; uint8_t v_nondep_2199_; lean_object* v___x_2200_; 
v_declName_2195_ = lean_ctor_get(v_e_2167_, 0);
lean_inc(v_declName_2195_);
v_type_2196_ = lean_ctor_get(v_e_2167_, 1);
lean_inc_ref(v_type_2196_);
v_value_2197_ = lean_ctor_get(v_e_2167_, 2);
lean_inc_ref(v_value_2197_);
v_body_2198_ = lean_ctor_get(v_e_2167_, 3);
lean_inc_ref(v_body_2198_);
v_nondep_2199_ = lean_ctor_get_uint8(v_e_2167_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2167_);
lean_inc_ref(v_F_2166_);
lean_inc(v_fixedPrefixSize_2165_);
lean_inc(v_recFnName_2164_);
v___x_2200_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_type_2196_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
lean_inc_ref(v_F_2166_);
lean_inc(v_fixedPrefixSize_2165_);
lean_inc(v_recFnName_2164_);
v___x_2202_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_value_2197_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___f_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2204_, 0, v_body_2198_);
lean_closure_set(v___f_2204_, 1, v_recFnName_2164_);
lean_closure_set(v___f_2204_, 2, v_fixedPrefixSize_2165_);
lean_closure_set(v___f_2204_, 3, v_F_2166_);
v___x_2205_ = 0;
v___x_2206_ = 0;
v___x_2207_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2195_, v_a_2201_, v_a_2203_, v___f_2204_, v_nondep_2199_, v___x_2205_, v___x_2206_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2207_;
}
else
{
lean_dec(v_a_2201_);
lean_dec_ref(v_body_2198_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
return v___x_2202_;
}
}
else
{
lean_dec_ref(v_body_2198_);
lean_dec_ref(v_value_2197_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
return v___x_2200_;
}
}
case 10:
{
lean_object* v_data_2208_; lean_object* v_expr_2209_; lean_object* v___x_2210_; 
v_data_2208_ = lean_ctor_get(v_e_2167_, 0);
lean_inc(v_data_2208_);
v_expr_2209_ = lean_ctor_get(v_e_2167_, 1);
lean_inc_ref(v_expr_2209_);
v___x_2210_ = l_Lean_getRecAppSyntax_x3f(v_e_2167_);
lean_dec_ref(v_e_2167_);
if (lean_obj_tag(v___x_2210_) == 1)
{
lean_object* v_val_2211_; lean_object* v_fileName_2212_; lean_object* v_fileMap_2213_; lean_object* v_options_2214_; lean_object* v_currRecDepth_2215_; lean_object* v_maxRecDepth_2216_; lean_object* v_ref_2217_; lean_object* v_currNamespace_2218_; lean_object* v_openDecls_2219_; lean_object* v_initHeartbeats_2220_; lean_object* v_maxHeartbeats_2221_; lean_object* v_quotContext_2222_; lean_object* v_currMacroScope_2223_; uint8_t v_diag_2224_; lean_object* v_cancelTk_x3f_2225_; uint8_t v_suppressElabErrors_2226_; lean_object* v_inheritedTraceOptions_2227_; lean_object* v_ref_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v_data_2208_);
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2211_);
lean_dec_ref(v___x_2210_);
v_fileName_2212_ = lean_ctor_get(v_a_2174_, 0);
v_fileMap_2213_ = lean_ctor_get(v_a_2174_, 1);
v_options_2214_ = lean_ctor_get(v_a_2174_, 2);
v_currRecDepth_2215_ = lean_ctor_get(v_a_2174_, 3);
v_maxRecDepth_2216_ = lean_ctor_get(v_a_2174_, 4);
v_ref_2217_ = lean_ctor_get(v_a_2174_, 5);
v_currNamespace_2218_ = lean_ctor_get(v_a_2174_, 6);
v_openDecls_2219_ = lean_ctor_get(v_a_2174_, 7);
v_initHeartbeats_2220_ = lean_ctor_get(v_a_2174_, 8);
v_maxHeartbeats_2221_ = lean_ctor_get(v_a_2174_, 9);
v_quotContext_2222_ = lean_ctor_get(v_a_2174_, 10);
v_currMacroScope_2223_ = lean_ctor_get(v_a_2174_, 11);
v_diag_2224_ = lean_ctor_get_uint8(v_a_2174_, sizeof(void*)*14);
v_cancelTk_x3f_2225_ = lean_ctor_get(v_a_2174_, 12);
v_suppressElabErrors_2226_ = lean_ctor_get_uint8(v_a_2174_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2227_ = lean_ctor_get(v_a_2174_, 13);
v_ref_2228_ = l_Lean_replaceRef(v_val_2211_, v_ref_2217_);
lean_dec(v_val_2211_);
lean_inc_ref(v_inheritedTraceOptions_2227_);
lean_inc(v_cancelTk_x3f_2225_);
lean_inc(v_currMacroScope_2223_);
lean_inc(v_quotContext_2222_);
lean_inc(v_maxHeartbeats_2221_);
lean_inc(v_initHeartbeats_2220_);
lean_inc(v_openDecls_2219_);
lean_inc(v_currNamespace_2218_);
lean_inc(v_maxRecDepth_2216_);
lean_inc(v_currRecDepth_2215_);
lean_inc_ref(v_options_2214_);
lean_inc_ref(v_fileMap_2213_);
lean_inc_ref(v_fileName_2212_);
v___x_2229_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2229_, 0, v_fileName_2212_);
lean_ctor_set(v___x_2229_, 1, v_fileMap_2213_);
lean_ctor_set(v___x_2229_, 2, v_options_2214_);
lean_ctor_set(v___x_2229_, 3, v_currRecDepth_2215_);
lean_ctor_set(v___x_2229_, 4, v_maxRecDepth_2216_);
lean_ctor_set(v___x_2229_, 5, v_ref_2228_);
lean_ctor_set(v___x_2229_, 6, v_currNamespace_2218_);
lean_ctor_set(v___x_2229_, 7, v_openDecls_2219_);
lean_ctor_set(v___x_2229_, 8, v_initHeartbeats_2220_);
lean_ctor_set(v___x_2229_, 9, v_maxHeartbeats_2221_);
lean_ctor_set(v___x_2229_, 10, v_quotContext_2222_);
lean_ctor_set(v___x_2229_, 11, v_currMacroScope_2223_);
lean_ctor_set(v___x_2229_, 12, v_cancelTk_x3f_2225_);
lean_ctor_set(v___x_2229_, 13, v_inheritedTraceOptions_2227_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*14, v_diag_2224_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*14 + 1, v_suppressElabErrors_2226_);
v___x_2230_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_expr_2209_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v___x_2229_, v_a_2175_);
lean_dec_ref(v___x_2229_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; 
lean_dec(v___x_2210_);
v___x_2231_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_expr_2209_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2240_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = l_Lean_mkMData(v_data_2208_, v_a_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_dec(v_data_2208_);
return v___x_2231_;
}
}
}
case 11:
{
lean_object* v_typeName_2241_; lean_object* v_idx_2242_; lean_object* v_struct_2243_; lean_object* v___x_2244_; 
v_typeName_2241_ = lean_ctor_get(v_e_2167_, 0);
lean_inc(v_typeName_2241_);
v_idx_2242_ = lean_ctor_get(v_e_2167_, 1);
lean_inc(v_idx_2242_);
v_struct_2243_ = lean_ctor_get(v_e_2167_, 2);
lean_inc_ref(v_struct_2243_);
lean_dec_ref(v_e_2167_);
v___x_2244_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_struct_2243_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_mkProj(v_typeName_2241_, v_idx_2242_, v_a_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_dec(v_idx_2242_);
lean_dec(v_typeName_2241_);
return v___x_2244_;
}
}
case 4:
{
uint8_t v___x_2254_; 
v___x_2254_ = l_Lean_Expr_isConstOf(v_e_2167_, v_recFnName_2164_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_e_2167_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2256_;
}
}
case 5:
{
uint8_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = 1;
lean_inc_ref(v_e_2167_);
v___x_2258_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2167_, v___x_2257_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
if (lean_obj_tag(v_a_2259_) == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2260_;
}
else
{
lean_object* v_val_2261_; lean_object* v___x_2262_; 
v_val_2261_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_val_2261_);
lean_dec_ref(v_a_2259_);
lean_inc_ref(v_F_2166_);
v___x_2262_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2261_, v_F_2166_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
if (lean_obj_tag(v_a_2263_) == 1)
{
lean_object* v_val_2264_; lean_object* v_toMatcherInfo_2265_; lean_object* v_matcherName_2266_; lean_object* v_matcherLevels_2267_; lean_object* v_params_2268_; lean_object* v_motive_2269_; lean_object* v_discrs_2270_; lean_object* v_alts_2271_; lean_object* v_remaining_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_val_2264_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_val_2264_);
lean_dec_ref(v_a_2263_);
v_toMatcherInfo_2265_ = lean_ctor_get(v_val_2264_, 0);
lean_inc_ref(v_toMatcherInfo_2265_);
v_matcherName_2266_ = lean_ctor_get(v_val_2264_, 1);
lean_inc(v_matcherName_2266_);
v_matcherLevels_2267_ = lean_ctor_get(v_val_2264_, 2);
lean_inc_ref(v_matcherLevels_2267_);
v_params_2268_ = lean_ctor_get(v_val_2264_, 3);
lean_inc_ref(v_params_2268_);
v_motive_2269_ = lean_ctor_get(v_val_2264_, 4);
lean_inc_ref(v_motive_2269_);
v_discrs_2270_ = lean_ctor_get(v_val_2264_, 5);
lean_inc_ref(v_discrs_2270_);
v_alts_2271_ = lean_ctor_get(v_val_2264_, 6);
lean_inc_ref(v_alts_2271_);
v_remaining_2272_ = lean_ctor_get(v_val_2264_, 7);
lean_inc_ref(v_remaining_2272_);
v___x_2273_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2264_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2165_);
lean_inc(v_recFnName_2164_);
v___x_2276_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_e_2167_, v_alts_2271_, v___x_2273_, v___x_2274_, v___x_2275_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v_alts_2271_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; size_t v_sz_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v_sz_2278_ = lean_array_size(v_discrs_2270_);
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_sz_2278_, v___x_2279_, v_discrs_2270_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2290_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2285_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2285_, 0, v_toMatcherInfo_2265_);
lean_ctor_set(v___x_2285_, 1, v_matcherName_2266_);
lean_ctor_set(v___x_2285_, 2, v_matcherLevels_2267_);
lean_ctor_set(v___x_2285_, 3, v_params_2268_);
lean_ctor_set(v___x_2285_, 4, v_motive_2269_);
lean_ctor_set(v___x_2285_, 5, v_a_2281_);
lean_ctor_set(v___x_2285_, 6, v_a_2277_);
lean_ctor_set(v___x_2285_, 7, v_remaining_2272_);
v___x_2286_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2285_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2286_);
v___x_2288_ = v___x_2283_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2277_);
lean_dec_ref(v_remaining_2272_);
lean_dec_ref(v_motive_2269_);
lean_dec_ref(v_params_2268_);
lean_dec_ref(v_matcherLevels_2267_);
lean_dec(v_matcherName_2266_);
lean_dec_ref(v_toMatcherInfo_2265_);
v_a_2291_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2280_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2280_);
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
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_remaining_2272_);
lean_dec_ref(v_discrs_2270_);
lean_dec_ref(v_motive_2269_);
lean_dec_ref(v_params_2268_);
lean_dec_ref(v_matcherLevels_2267_);
lean_dec(v_matcherName_2266_);
lean_dec_ref(v_toMatcherInfo_2265_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
v_a_2299_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2276_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2276_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v___x_2307_; 
lean_dec(v_a_2263_);
v___x_2307_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2164_, v_fixedPrefixSize_2165_, v_F_2166_, v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2307_;
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_e_2167_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
v_a_2308_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2262_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2262_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_e_2167_);
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
lean_dec(v_recFnName_2164_);
v_a_2316_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2258_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2258_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
default: 
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_F_2166_);
lean_dec(v_fixedPrefixSize_2165_);
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = lean_mk_empty_array_with_capacity(v___x_2324_);
v___x_2326_ = lean_array_push(v___x_2325_, v_recFnName_2164_);
lean_inc_ref(v_e_2167_);
v___x_2327_ = l_Lean_Elab_ensureNoRecFn(v___x_2326_, v_e_2167_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2327_, 0);
lean_dec(v_unused_2335_);
v___x_2329_ = v___x_2327_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v___x_2327_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v_e_2167_);
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_e_2167_);
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
lean_dec_ref(v_e_2167_);
v_a_2336_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2327_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2327_);
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
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0(void){
_start:
{
uint8_t v___x_2344_; uint64_t v___x_2345_; 
v___x_2344_ = 0;
v___x_2345_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2346_, lean_object* v_fixedPrefixSize_2347_, lean_object* v_F_2348_, lean_object* v_e_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc_ref(v_e_2349_);
lean_inc(v_recFnName_2346_);
v___x_2359_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2346_, v_e_2349_, v_a_2350_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2498_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2498_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2498_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_unbox(v_a_2360_);
lean_dec(v_a_2360_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2366_; 
lean_dec_ref(v_F_2348_);
lean_dec(v_fixedPrefixSize_2347_);
lean_dec(v_recFnName_2346_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v_e_2349_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_e_2349_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
else
{
lean_object* v___x_2368_; uint8_t v___x_2369_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___x_2476_; 
lean_del_object(v___x_2362_);
v___x_2368_ = lean_st_ref_get(v_a_2351_);
v___x_2369_ = 0;
v___x_2476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2368_, v_e_2349_);
lean_dec(v___x_2368_);
if (lean_obj_tag(v___x_2476_) == 1)
{
lean_object* v_val_2477_; lean_object* v_fst_2478_; lean_object* v_snd_2479_; lean_object* v___x_2480_; 
v_val_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_val_2477_);
lean_dec_ref(v___x_2476_);
v_fst_2478_ = lean_ctor_get(v_val_2477_, 0);
lean_inc(v_fst_2478_);
v_snd_2479_ = lean_ctor_get(v_val_2477_, 1);
lean_inc(v_snd_2479_);
lean_dec(v_val_2477_);
v___x_2480_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2479_, v_a_2354_);
lean_dec(v_snd_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2489_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_unbox(v_a_2481_);
lean_dec(v_a_2481_);
if (v___x_2485_ == 0)
{
lean_del_object(v___x_2483_);
lean_dec(v_fst_2478_);
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
v___y_2375_ = v_a_2354_;
v___y_2376_ = v_a_2355_;
v___y_2377_ = v_a_2356_;
v___y_2378_ = v_a_2357_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2487_; 
lean_dec_ref(v_e_2349_);
lean_dec_ref(v_F_2348_);
lean_dec(v_fixedPrefixSize_2347_);
lean_dec(v_recFnName_2346_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v_fst_2478_);
v___x_2487_ = v___x_2483_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_fst_2478_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_fst_2478_);
lean_dec_ref(v_e_2349_);
lean_dec_ref(v_F_2348_);
lean_dec(v_fixedPrefixSize_2347_);
lean_dec(v_recFnName_2346_);
v_a_2490_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2480_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2480_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_dec(v___x_2476_);
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
v___y_2373_ = v_a_2352_;
v___y_2374_ = v_a_2353_;
v___y_2375_ = v_a_2354_;
v___y_2376_ = v_a_2355_;
v___y_2377_ = v_a_2356_;
v___y_2378_ = v_a_2357_;
goto v___jp_2370_;
}
v___jp_2370_:
{
lean_object* v___x_2379_; 
lean_inc_ref(v_e_2349_);
v___x_2379_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2346_, v_fixedPrefixSize_2347_, v_F_2348_, v_e_2349_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2467_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2467_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2467_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_options_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2386_ = lean_st_ref_take(v___y_2372_);
lean_inc(v_a_2380_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_a_2380_);
lean_ctor_set(v___x_2387_, 1, v_a_2382_);
lean_inc_ref(v_e_2349_);
v___x_2388_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2386_, v_e_2349_, v___x_2387_);
v___x_2389_ = lean_st_ref_set(v___y_2372_, v___x_2388_);
v_options_2390_ = lean_ctor_get(v___y_2377_, 2);
v___x_2391_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2392_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2394_; 
lean_dec_ref(v_e_2349_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_a_2380_);
v___x_2394_ = v___x_2384_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2380_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
else
{
lean_object* v___x_2396_; uint8_t v_foApprox_2397_; uint8_t v_ctxApprox_2398_; uint8_t v_quasiPatternApprox_2399_; uint8_t v_constApprox_2400_; uint8_t v_isDefEqStuckEx_2401_; uint8_t v_unificationHints_2402_; uint8_t v_proofIrrelevance_2403_; uint8_t v_assignSyntheticOpaque_2404_; uint8_t v_offsetCnstrs_2405_; uint8_t v_etaStruct_2406_; uint8_t v_univApprox_2407_; uint8_t v_iota_2408_; uint8_t v_beta_2409_; uint8_t v_proj_2410_; uint8_t v_zeta_2411_; uint8_t v_zetaDelta_2412_; uint8_t v_zetaUnused_2413_; uint8_t v_zetaHave_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2466_; 
lean_del_object(v___x_2384_);
v___x_2396_ = l_Lean_Meta_Context_config(v___y_2375_);
v_foApprox_2397_ = lean_ctor_get_uint8(v___x_2396_, 0);
v_ctxApprox_2398_ = lean_ctor_get_uint8(v___x_2396_, 1);
v_quasiPatternApprox_2399_ = lean_ctor_get_uint8(v___x_2396_, 2);
v_constApprox_2400_ = lean_ctor_get_uint8(v___x_2396_, 3);
v_isDefEqStuckEx_2401_ = lean_ctor_get_uint8(v___x_2396_, 4);
v_unificationHints_2402_ = lean_ctor_get_uint8(v___x_2396_, 5);
v_proofIrrelevance_2403_ = lean_ctor_get_uint8(v___x_2396_, 6);
v_assignSyntheticOpaque_2404_ = lean_ctor_get_uint8(v___x_2396_, 7);
v_offsetCnstrs_2405_ = lean_ctor_get_uint8(v___x_2396_, 8);
v_etaStruct_2406_ = lean_ctor_get_uint8(v___x_2396_, 10);
v_univApprox_2407_ = lean_ctor_get_uint8(v___x_2396_, 11);
v_iota_2408_ = lean_ctor_get_uint8(v___x_2396_, 12);
v_beta_2409_ = lean_ctor_get_uint8(v___x_2396_, 13);
v_proj_2410_ = lean_ctor_get_uint8(v___x_2396_, 14);
v_zeta_2411_ = lean_ctor_get_uint8(v___x_2396_, 15);
v_zetaDelta_2412_ = lean_ctor_get_uint8(v___x_2396_, 16);
v_zetaUnused_2413_ = lean_ctor_get_uint8(v___x_2396_, 17);
v_zetaHave_2414_ = lean_ctor_get_uint8(v___x_2396_, 18);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2416_ = v___x_2396_;
v_isShared_2417_ = v_isSharedCheck_2466_;
goto v_resetjp_2415_;
}
else
{
lean_dec(v___x_2396_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2466_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
uint8_t v_trackZetaDelta_2418_; lean_object* v_zetaDeltaSet_2419_; lean_object* v_lctx_2420_; lean_object* v_localInstances_2421_; lean_object* v_defEqCtx_x3f_2422_; lean_object* v_synthPendingDepth_2423_; lean_object* v_canUnfold_x3f_2424_; uint8_t v_univApprox_2425_; uint8_t v_inTypeClassResolution_2426_; uint8_t v_cacheInferType_2427_; uint8_t v___x_2428_; lean_object* v_config_2430_; 
v_trackZetaDelta_2418_ = lean_ctor_get_uint8(v___y_2375_, sizeof(void*)*7);
v_zetaDeltaSet_2419_ = lean_ctor_get(v___y_2375_, 1);
v_lctx_2420_ = lean_ctor_get(v___y_2375_, 2);
v_localInstances_2421_ = lean_ctor_get(v___y_2375_, 3);
v_defEqCtx_x3f_2422_ = lean_ctor_get(v___y_2375_, 4);
v_synthPendingDepth_2423_ = lean_ctor_get(v___y_2375_, 5);
v_canUnfold_x3f_2424_ = lean_ctor_get(v___y_2375_, 6);
v_univApprox_2425_ = lean_ctor_get_uint8(v___y_2375_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2426_ = lean_ctor_get_uint8(v___y_2375_, sizeof(void*)*7 + 2);
v_cacheInferType_2427_ = lean_ctor_get_uint8(v___y_2375_, sizeof(void*)*7 + 3);
v___x_2428_ = 0;
if (v_isShared_2417_ == 0)
{
v_config_2430_ = v___x_2416_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 0, v_foApprox_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 1, v_ctxApprox_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 2, v_quasiPatternApprox_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 3, v_constApprox_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 4, v_isDefEqStuckEx_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 5, v_unificationHints_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 6, v_proofIrrelevance_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 7, v_assignSyntheticOpaque_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 8, v_offsetCnstrs_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 10, v_etaStruct_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 11, v_univApprox_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 12, v_iota_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 13, v_beta_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 14, v_proj_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 15, v_zeta_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 16, v_zetaDelta_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 17, v_zetaUnused_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 18, v_zetaHave_2414_);
v_config_2430_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; lean_object* v___f_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; uint64_t v_key_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_ctor_set_uint8(v_config_2430_, 9, v___x_2428_);
v___x_2431_ = l_Lean_Meta_Context_configKey(v___y_2375_);
v___x_2432_ = 2ULL;
v___x_2433_ = lean_uint64_shift_right(v___x_2431_, v___x_2432_);
lean_inc(v_a_2380_);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2434_, 0, v_a_2380_);
lean_closure_set(v___f_2434_, 1, v_e_2349_);
v___x_2435_ = lean_uint64_shift_left(v___x_2433_, v___x_2432_);
v___x_2436_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2437_ = lean_uint64_lor(v___x_2435_, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2438_, 0, v_config_2430_);
lean_ctor_set_uint64(v___x_2438_, sizeof(void*)*1, v_key_2437_);
lean_inc(v_canUnfold_x3f_2424_);
lean_inc(v_synthPendingDepth_2423_);
lean_inc(v_defEqCtx_x3f_2422_);
lean_inc_ref(v_localInstances_2421_);
lean_inc_ref(v_lctx_2420_);
lean_inc(v_zetaDeltaSet_2419_);
v___x_2439_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v_zetaDeltaSet_2419_);
lean_ctor_set(v___x_2439_, 2, v_lctx_2420_);
lean_ctor_set(v___x_2439_, 3, v_localInstances_2421_);
lean_ctor_set(v___x_2439_, 4, v_defEqCtx_x3f_2422_);
lean_ctor_set(v___x_2439_, 5, v_synthPendingDepth_2423_);
lean_ctor_set(v___x_2439_, 6, v_canUnfold_x3f_2424_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*7, v_trackZetaDelta_2418_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*7 + 1, v_univApprox_2425_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2426_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*7 + 3, v_cacheInferType_2427_);
v___x_2440_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2434_, v___x_2369_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___x_2439_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec_ref(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2440_, 0);
lean_dec(v_unused_2448_);
v___x_2442_ = v___x_2440_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_dec(v___x_2440_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v_a_2380_);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2380_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2440_, 0);
lean_dec(v_unused_2456_);
v___x_2450_ = v___x_2440_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v___x_2440_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 0);
lean_ctor_set(v___x_2450_, 0, v_a_2380_);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2380_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_a_2380_);
v_a_2457_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2440_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2440_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
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
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_a_2380_);
lean_dec_ref(v_e_2349_);
v_a_2468_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2381_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2381_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_dec_ref(v_e_2349_);
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v_e_2349_);
lean_dec_ref(v_F_2348_);
lean_dec(v_fixedPrefixSize_2347_);
lean_dec(v_recFnName_2346_);
v_a_2499_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2359_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2359_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2507_, lean_object* v_recFnName_2508_, lean_object* v_fixedPrefixSize_2509_, lean_object* v_F_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_expr_instantiate1(v_body_2507_, v_x_2511_);
v___x_2522_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2508_, v_fixedPrefixSize_2509_, v_F_2510_, v___x_2521_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2523_, lean_object* v_fixedPrefixSize_2524_, lean_object* v_F_2525_, lean_object* v_e_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2523_, v_fixedPrefixSize_2524_, v_F_2525_, v_e_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2537_, lean_object* v_fixedPrefixSize_2538_, lean_object* v_F_2539_, lean_object* v_sz_2540_, lean_object* v_i_2541_, lean_object* v_bs_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_sz_boxed_2552_; size_t v_i_boxed_2553_; lean_object* v_res_2554_; 
v_sz_boxed_2552_ = lean_unbox_usize(v_sz_2540_);
lean_dec(v_sz_2540_);
v_i_boxed_2553_ = lean_unbox_usize(v_i_2541_);
lean_dec(v_i_2541_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2537_, v_fixedPrefixSize_2538_, v_F_2539_, v_sz_boxed_2552_, v_i_boxed_2553_, v_bs_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2555_, lean_object* v_fixedPrefixSize_2556_, lean_object* v_F_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2555_, v_fixedPrefixSize_2556_, v_F_2557_, v_x_2558_, v_x_2559_, v_x_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec(v___y_2561_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2571_, lean_object* v_fixedPrefixSize_2572_, lean_object* v_e_2573_, lean_object* v_as_2574_, lean_object* v_bs_2575_, lean_object* v_i_2576_, lean_object* v_cs_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2571_, v_fixedPrefixSize_2572_, v_e_2573_, v_as_2574_, v_bs_2575_, v_i_2576_, v_cs_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v_bs_2575_);
lean_dec_ref(v_as_2574_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2588_, lean_object* v_fixedPrefixSize_2589_, lean_object* v_F_2590_, lean_object* v_e_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2588_, v_fixedPrefixSize_2589_, v_F_2590_, v_e_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec(v_a_2592_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2602_, lean_object* v_fixedPrefixSize_2603_, lean_object* v_F_2604_, lean_object* v_e_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2602_, v_fixedPrefixSize_2603_, v_F_2604_, v_e_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec(v_a_2606_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2616_, lean_object* v_fixedPrefixSize_2617_, lean_object* v_F_2618_, lean_object* v_e_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2616_, v_fixedPrefixSize_2617_, v_F_2618_, v_e_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec(v_a_2620_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2630_, lean_object* v_k_2631_, uint8_t v_allowLevelAssignments_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2631_, v_allowLevelAssignments_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_k_2644_, lean_object* v_allowLevelAssignments_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2655_; lean_object* v_res_2656_; 
v_allowLevelAssignments_boxed_2655_ = lean_unbox(v_allowLevelAssignments_2645_);
v_res_2656_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2643_, v_k_2644_, v_allowLevelAssignments_boxed_2655_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2657_, lean_object* v_name_2658_, uint8_t v_bi_2659_, lean_object* v_type_2660_, lean_object* v_k_2661_, uint8_t v_kind_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2658_, v_bi_2659_, v_type_2660_, v_k_2661_, v_kind_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_name_2674_, lean_object* v_bi_2675_, lean_object* v_type_2676_, lean_object* v_k_2677_, lean_object* v_kind_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_bi_boxed_2688_; uint8_t v_kind_boxed_2689_; lean_object* v_res_2690_; 
v_bi_boxed_2688_ = lean_unbox(v_bi_2675_);
v_kind_boxed_2689_ = lean_unbox(v_kind_2678_);
v_res_2690_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2673_, v_name_2674_, v_bi_boxed_2688_, v_type_2676_, v_k_2677_, v_kind_boxed_2689_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2691_, lean_object* v_e_2692_, lean_object* v_maxFVars_2693_, lean_object* v_k_2694_, uint8_t v_cleanupAnnotations_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2692_, v_maxFVars_2693_, v_k_2694_, v_cleanupAnnotations_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_e_2707_, lean_object* v_maxFVars_2708_, lean_object* v_k_2709_, lean_object* v_cleanupAnnotations_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2720_; lean_object* v_res_2721_; 
v_cleanupAnnotations_boxed_2720_ = lean_unbox(v_cleanupAnnotations_2710_);
v_res_2721_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2706_, v_e_2707_, v_maxFVars_2708_, v_k_2709_, v_cleanupAnnotations_boxed_2720_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2722_, lean_object* v_R_2723_, lean_object* v_a_2724_, lean_object* v_b_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2724_, v_b_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2727_, lean_object* v_msg_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2727_, v_msg_2728_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2739_, lean_object* v_msg_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2739_, v_msg_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2751_, lean_object* v_m_2752_, lean_object* v_a_2753_, lean_object* v_b_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2752_, v_a_2753_, v_b_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2756_, lean_object* v_msg_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2757_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2768_, v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___y_2770_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2780_, lean_object* v_m_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2781_, v_a_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2784_, lean_object* v_m_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2784_, v_m_2785_, v_a_2786_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_m_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2788_, lean_object* v_name_2789_, lean_object* v_type_2790_, lean_object* v_val_2791_, lean_object* v_k_2792_, uint8_t v_nondep_2793_, uint8_t v_kind_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2789_, v_type_2790_, v_val_2791_, v_k_2792_, v_nondep_2793_, v_kind_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2805_, lean_object* v_name_2806_, lean_object* v_type_2807_, lean_object* v_val_2808_, lean_object* v_k_2809_, lean_object* v_nondep_2810_, lean_object* v_kind_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v_nondep_boxed_2821_; uint8_t v_kind_boxed_2822_; lean_object* v_res_2823_; 
v_nondep_boxed_2821_ = lean_unbox(v_nondep_2810_);
v_kind_boxed_2822_ = lean_unbox(v_kind_2811_);
v_res_2823_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2805_, v_name_2806_, v_type_2807_, v_val_2808_, v_k_2809_, v_nondep_boxed_2821_, v_kind_boxed_2822_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2824_, v___y_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
return v_res_2845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2846_, lean_object* v_a_2847_, lean_object* v_x_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2847_, v_x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2850_, lean_object* v_a_2851_, lean_object* v_x_2852_){
_start:
{
uint8_t v_res_2853_; lean_object* v_r_2854_; 
v_res_2853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2850_, v_a_2851_, v_x_2852_);
lean_dec(v_x_2852_);
lean_dec_ref(v_a_2851_);
v_r_2854_ = lean_box(v_res_2853_);
return v_r_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2855_, lean_object* v_data_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2858_, lean_object* v_a_2859_, lean_object* v_b_2860_, lean_object* v_x_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2859_, v_b_2860_, v_x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2863_, lean_object* v_a_2864_, lean_object* v_x_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2864_, v_x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2867_, lean_object* v_a_2868_, lean_object* v_x_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2867_, v_a_2868_, v_x_2869_);
lean_dec(v_x_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2871_, lean_object* v_i_2872_, lean_object* v_source_2873_, lean_object* v_target_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2872_, v_source_2873_, v_target_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2876_, lean_object* v_constName_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_constName_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2888_, v_constName_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec(v___y_2890_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2901_, v_x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2904_, lean_object* v_ref_2905_, lean_object* v_constName_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2905_, v_constName_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_ref_2918_, lean_object* v_constName_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2917_, v_ref_2918_, v_constName_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v_ref_2918_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2930_, lean_object* v_ref_2931_, lean_object* v_msg_2932_, lean_object* v_declHint_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2931_, v_msg_2932_, v_declHint_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_ref_2945_, lean_object* v_msg_2946_, lean_object* v_declHint_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2944_, v_ref_2945_, v_msg_2946_, v_declHint_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v_ref_2945_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2958_, lean_object* v_declHint_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2958_, v_declHint_2959_, v___y_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2970_, lean_object* v_declHint_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2970_, v_declHint_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2983_, v_msg_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2995_, lean_object* v_ref_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2995_, v_ref_2996_, v_msg_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec(v_ref_2996_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3008_, lean_object* v_msg_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_ref_3015_; lean_object* v___x_3016_; lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3061_; 
v_ref_3015_ = lean_ctor_get(v___y_3012_, 5);
v___x_3016_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3061_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3061_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v_traceState_3022_; lean_object* v_env_3023_; lean_object* v_nextMacroScope_3024_; lean_object* v_ngen_3025_; lean_object* v_auxDeclNGen_3026_; lean_object* v_cache_3027_; lean_object* v_messages_3028_; lean_object* v_infoState_3029_; lean_object* v_snapshotTasks_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3060_; 
v___x_3021_ = lean_st_ref_take(v___y_3013_);
v_traceState_3022_ = lean_ctor_get(v___x_3021_, 4);
v_env_3023_ = lean_ctor_get(v___x_3021_, 0);
v_nextMacroScope_3024_ = lean_ctor_get(v___x_3021_, 1);
v_ngen_3025_ = lean_ctor_get(v___x_3021_, 2);
v_auxDeclNGen_3026_ = lean_ctor_get(v___x_3021_, 3);
v_cache_3027_ = lean_ctor_get(v___x_3021_, 5);
v_messages_3028_ = lean_ctor_get(v___x_3021_, 6);
v_infoState_3029_ = lean_ctor_get(v___x_3021_, 7);
v_snapshotTasks_3030_ = lean_ctor_get(v___x_3021_, 8);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3032_ = v___x_3021_;
v_isShared_3033_ = v_isSharedCheck_3060_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_snapshotTasks_3030_);
lean_inc(v_infoState_3029_);
lean_inc(v_messages_3028_);
lean_inc(v_cache_3027_);
lean_inc(v_traceState_3022_);
lean_inc(v_auxDeclNGen_3026_);
lean_inc(v_ngen_3025_);
lean_inc(v_nextMacroScope_3024_);
lean_inc(v_env_3023_);
lean_dec(v___x_3021_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3060_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
uint64_t v_tid_3034_; lean_object* v_traces_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3059_; 
v_tid_3034_ = lean_ctor_get_uint64(v_traceState_3022_, sizeof(void*)*1);
v_traces_3035_ = lean_ctor_get(v_traceState_3022_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_traceState_3022_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3037_ = v_traceState_3022_;
v_isShared_3038_ = v_isSharedCheck_3059_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_traces_3035_);
lean_dec(v_traceState_3022_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3059_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; double v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3041_ = 0;
v___x_3042_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3043_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3043_, 0, v_cls_3008_);
lean_ctor_set(v___x_3043_, 1, v___x_3039_);
lean_ctor_set(v___x_3043_, 2, v___x_3042_);
lean_ctor_set_float(v___x_3043_, sizeof(void*)*3, v___x_3040_);
lean_ctor_set_float(v___x_3043_, sizeof(void*)*3 + 8, v___x_3040_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*3 + 16, v___x_3041_);
v___x_3044_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3045_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v_a_3017_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
lean_inc(v_ref_3015_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_ref_3015_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_PersistentArray_push___redArg(v_traces_3035_, v___x_3046_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3047_);
v___x_3049_ = v___x_3037_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3047_);
lean_ctor_set_uint64(v_reuseFailAlloc_3058_, sizeof(void*)*1, v_tid_3034_);
v___x_3049_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 4, v___x_3049_);
v___x_3051_ = v___x_3032_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_env_3023_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_nextMacroScope_3024_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_ngen_3025_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_auxDeclNGen_3026_);
lean_ctor_set(v_reuseFailAlloc_3057_, 4, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3057_, 5, v_cache_3027_);
lean_ctor_set(v_reuseFailAlloc_3057_, 6, v_messages_3028_);
lean_ctor_set(v_reuseFailAlloc_3057_, 7, v_infoState_3029_);
lean_ctor_set(v_reuseFailAlloc_3057_, 8, v_snapshotTasks_3030_);
v___x_3051_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3052_ = lean_st_ref_set(v___y_3013_, v___x_3051_);
v___x_3053_ = lean_box(0);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3053_);
v___x_3055_ = v___x_3019_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3062_, lean_object* v_msg_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3062_, v_msg_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_unsigned_to_nat(16u);
v___x_3072_ = lean_mk_array(v___x_3071_, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3085_, lean_object* v_fixedPrefixSize_3086_, lean_object* v_F_3087_, lean_object* v_e_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_options_3117_; uint8_t v_hasTrace_3118_; 
v_options_3117_ = lean_ctor_get(v_a_3093_, 2);
v_hasTrace_3118_ = lean_ctor_get_uint8(v_options_3117_, sizeof(void*)*1);
if (v_hasTrace_3118_ == 0)
{
v___y_3097_ = v_a_3089_;
v___y_3098_ = v_a_3090_;
v___y_3099_ = v_a_3091_;
v___y_3100_ = v_a_3092_;
v___y_3101_ = v_a_3093_;
v___y_3102_ = v_a_3094_;
goto v___jp_3096_;
}
else
{
lean_object* v_inheritedTraceOptions_3119_; lean_object* v_cls_3120_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v_options_3127_; lean_object* v_inheritedTraceOptions_3128_; lean_object* v___y_3129_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_inheritedTraceOptions_3119_ = lean_ctor_get(v_a_3093_, 13);
v_cls_3120_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3150_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3119_, v_options_3117_, v___x_3150_);
if (v___x_3151_ == 0)
{
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v_options_3127_ = v_options_3117_;
v_inheritedTraceOptions_3128_ = v_inheritedTraceOptions_3119_;
v___y_3129_ = v_a_3094_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3152_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3088_);
v___x_3153_ = l_Lean_indentExpr(v_e_3088_);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3120_, v___x_3154_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_dec_ref(v___x_3155_);
v___y_3122_ = v_a_3089_;
v___y_3123_ = v_a_3090_;
v___y_3124_ = v_a_3091_;
v___y_3125_ = v_a_3092_;
v___y_3126_ = v_a_3093_;
v_options_3127_ = v_options_3117_;
v_inheritedTraceOptions_3128_ = v_inheritedTraceOptions_3119_;
v___y_3129_ = v_a_3094_;
goto v___jp_3121_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_e_3088_);
lean_dec_ref(v_F_3087_);
lean_dec(v_fixedPrefixSize_3086_);
lean_dec(v_recFnName_3085_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
v___jp_3121_:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3128_, v_options_3127_, v___x_3130_);
if (v___x_3131_ == 0)
{
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3125_;
v___y_3101_ = v___y_3126_;
v___y_3102_ = v___y_3129_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3132_; 
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc_ref(v_F_3087_);
v___x_3132_ = lean_infer_type(v_F_3087_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3129_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
v___x_3134_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3087_);
v___x_3135_ = l_Lean_MessageData_ofExpr(v_F_3087_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_indentExpr(v_a_3133_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3120_, v___x_3140_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3129_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_dec_ref(v___x_3141_);
v___y_3097_ = v___y_3122_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3124_;
v___y_3100_ = v___y_3125_;
v___y_3101_ = v___y_3126_;
v___y_3102_ = v___y_3129_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v_e_3088_);
lean_dec_ref(v_F_3087_);
lean_dec(v_fixedPrefixSize_3086_);
lean_dec(v_recFnName_3085_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_dec_ref(v_e_3088_);
lean_dec_ref(v_F_3087_);
lean_dec(v_fixedPrefixSize_3086_);
lean_dec(v_recFnName_3085_);
return v___x_3132_;
}
}
}
}
v___jp_3096_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3104_ = lean_st_mk_ref(v___x_3103_);
v___x_3105_ = lean_st_mk_ref(v___x_3103_);
v___x_3106_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3085_, v_fixedPrefixSize_3086_, v_F_3087_, v_e_3088_, v___x_3105_, v___x_3104_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3116_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3116_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3116_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3111_ = lean_st_ref_get(v___x_3105_);
lean_dec(v___x_3105_);
lean_dec(v___x_3111_);
v___x_3112_ = lean_st_ref_get(v___x_3104_);
lean_dec(v___x_3104_);
lean_dec(v___x_3112_);
if (v_isShared_3110_ == 0)
{
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3107_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_dec(v___x_3105_);
lean_dec(v___x_3104_);
return v___x_3106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3164_, lean_object* v_fixedPrefixSize_3165_, lean_object* v_F_3166_, lean_object* v_e_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3164_, v_fixedPrefixSize_3165_, v_F_3166_, v_e_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3176_, lean_object* v_msg_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3176_, v_msg_3177_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3186_, lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3186_, v_msg_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v_b_3199_, lean_object* v_c_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
lean_inc(v___y_3204_);
lean_inc_ref(v___y_3203_);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
v___x_3206_ = lean_apply_9(v_k_3196_, v_b_3199_, v_c_3200_, v___y_3197_, v___y_3198_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, lean_box(0));
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v_b_3210_, lean_object* v_c_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3207_, v___y_3208_, v___y_3209_, v_b_3210_, v_c_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3218_, lean_object* v_k_3219_, uint8_t v_cleanupAnnotations_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___f_3228_; uint8_t v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___f_3228_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3241_, lean_object* v_k_3242_, lean_object* v_cleanupAnnotations_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3251_; lean_object* v_res_3252_; 
v_cleanupAnnotations_boxed_3251_ = lean_unbox(v_cleanupAnnotations_3243_);
v_res_3252_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3241_, v_k_3242_, v_cleanupAnnotations_boxed_3251_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3253_, lean_object* v_e_3254_, lean_object* v_k_3255_, uint8_t v_cleanupAnnotations_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3254_, v_k_3255_, v_cleanupAnnotations_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_e_3266_, lean_object* v_k_3267_, lean_object* v_cleanupAnnotations_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3276_; lean_object* v_res_3277_; 
v_cleanupAnnotations_boxed_3276_ = lean_unbox(v_cleanupAnnotations_3268_);
v_res_3277_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3265_, v_e_3266_, v_k_3267_, v_cleanupAnnotations_boxed_3276_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3278_, lean_object* v_maxFVars_3279_, lean_object* v_k_3280_, uint8_t v_cleanupAnnotations_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___f_3289_; uint8_t v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3289_, 0, v_k_3280_);
lean_closure_set(v___f_3289_, 1, v___y_3282_);
lean_closure_set(v___f_3289_, 2, v___y_3283_);
v___x_3290_ = 1;
v___x_3291_ = 0;
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_maxFVars_3279_);
v___x_3293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3278_, v___x_3290_, v___x_3291_, v___x_3290_, v___x_3291_, v___x_3292_, v___f_3289_, v_cleanupAnnotations_3281_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref(v___x_3292_);
if (lean_obj_tag(v___x_3293_) == 0)
{
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3302_, lean_object* v_maxFVars_3303_, lean_object* v_k_3304_, lean_object* v_cleanupAnnotations_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3313_; lean_object* v_res_3314_; 
v_cleanupAnnotations_boxed_3313_ = lean_unbox(v_cleanupAnnotations_3305_);
v_res_3314_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3302_, v_maxFVars_3303_, v_k_3304_, v_cleanupAnnotations_boxed_3313_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3315_, lean_object* v_e_3316_, lean_object* v_maxFVars_3317_, lean_object* v_k_3318_, uint8_t v_cleanupAnnotations_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3316_, v_maxFVars_3317_, v_k_3318_, v_cleanupAnnotations_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3328_, lean_object* v_e_3329_, lean_object* v_maxFVars_3330_, lean_object* v_k_3331_, lean_object* v_cleanupAnnotations_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3340_; lean_object* v_res_3341_; 
v_cleanupAnnotations_boxed_3340_ = lean_unbox(v_cleanupAnnotations_3332_);
v_res_3341_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3328_, v_e_3329_, v_maxFVars_3330_, v_k_3331_, v_cleanupAnnotations_boxed_3340_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3342_, lean_object* v___x_3343_, lean_object* v___x_3344_, lean_object* v_x_3345_, uint8_t v___x_3346_, lean_object* v_xs_3347_, lean_object* v_type_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3356_ = l_Lean_LocalDecl_type(v_a_3342_);
v___x_3357_ = lean_array_get_borrowed(v___x_3343_, v_xs_3347_, v___x_3344_);
v___x_3358_ = l_Lean_Expr_replaceFVar(v___x_3356_, v_x_3345_, v___x_3357_);
lean_dec_ref(v___x_3356_);
v___x_3359_ = l_Lean_mkArrow(v___x_3358_, v_type_3348_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; uint8_t v___x_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_n(v_a_3360_, 2);
lean_dec_ref(v___x_3359_);
v___x_3361_ = 0;
v___x_3362_ = 1;
v___x_3363_ = l_Lean_Meta_mkLambdaFVars(v_xs_3347_, v_a_3360_, v___x_3361_, v___x_3346_, v___x_3361_, v___x_3346_, v___x_3362_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = l_Lean_Meta_getLevel(v_a_3360_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3374_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3370_, 0, v_a_3364_);
lean_ctor_set(v___x_3370_, 1, v_a_3366_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3370_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3364_);
v_a_3375_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3365_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3365_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_a_3360_);
v_a_3383_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3363_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3363_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3359_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3359_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3399_, lean_object* v___x_3400_, lean_object* v___x_3401_, lean_object* v_x_3402_, lean_object* v___x_3403_, lean_object* v_xs_3404_, lean_object* v_type_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
uint8_t v___x_6703__boxed_3413_; lean_object* v_res_3414_; 
v___x_6703__boxed_3413_ = lean_unbox(v___x_3403_);
v_res_3414_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3399_, v___x_3400_, v___x_3401_, v_x_3402_, v___x_6703__boxed_3413_, v_xs_3404_, v_type_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec_ref(v_xs_3404_);
lean_dec(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec_ref(v_a_3399_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v_b_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___x_3424_; 
lean_inc(v___y_3422_);
lean_inc_ref(v___y_3421_);
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3419_);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
v___x_3424_ = lean_apply_8(v_k_3415_, v_b_3418_, v___y_3416_, v___y_3417_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, lean_box(0));
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v_b_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3425_, v___y_3426_, v___y_3427_, v_b_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3435_, uint8_t v_bi_3436_, lean_object* v_type_3437_, lean_object* v_k_3438_, uint8_t v_kind_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___f_3447_; lean_object* v___x_3448_; 
lean_inc(v___y_3441_);
lean_inc_ref(v___y_3440_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3447_, 0, v_k_3438_);
lean_closure_set(v___f_3447_, 1, v___y_3440_);
lean_closure_set(v___f_3447_, 2, v___y_3441_);
v___x_3448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3435_, v_bi_3436_, v_type_3437_, v___f_3447_, v_kind_3439_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3448_) == 0)
{
return v___x_3448_;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3457_, lean_object* v_bi_3458_, lean_object* v_type_3459_, lean_object* v_k_3460_, lean_object* v_kind_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
uint8_t v_bi_boxed_3469_; uint8_t v_kind_boxed_3470_; lean_object* v_res_3471_; 
v_bi_boxed_3469_ = lean_unbox(v_bi_3458_);
v_kind_boxed_3470_ = lean_unbox(v_kind_3461_);
v_res_3471_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3457_, v_bi_boxed_3469_, v_type_3459_, v_k_3460_, v_kind_boxed_3470_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3472_, lean_object* v_type_3473_, lean_object* v_k_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
uint8_t v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = 0;
v___x_3483_ = 0;
v___x_3484_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3472_, v___x_3482_, v_type_3473_, v_k_3474_, v___x_3483_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3485_, lean_object* v_type_3486_, lean_object* v_k_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3485_, v_type_3486_, v_k_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3509_, lean_object* v_F_3510_, lean_object* v_val_3511_, lean_object* v_k_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
uint8_t v___y_3521_; uint8_t v___x_3636_; 
v___x_3636_ = l_Lean_Expr_isFVar(v_x_3509_);
if (v___x_3636_ == 0)
{
v___y_3521_ = v___x_3636_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3638_ = lean_unsigned_to_nat(6u);
v___x_3639_ = l_Lean_Expr_isAppOfArity(v_val_3511_, v___x_3637_, v___x_3638_);
v___y_3521_ = v___x_3639_;
goto v___jp_3520_;
}
v___jp_3520_:
{
if (v___y_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_inc(v_a_3518_);
lean_inc_ref(v_a_3517_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3522_ = lean_apply_10(v_k_3512_, v_x_3509_, v_F_3510_, v_val_3511_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, lean_box(0));
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3523_ = lean_unsigned_to_nat(3u);
v___x_3524_ = l_Lean_Expr_getAppNumArgs(v_val_3511_);
v___x_3525_ = lean_nat_sub(v___x_3524_, v___x_3523_);
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_nat_sub(v___x_3525_, v___x_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = l_Lean_Expr_getRevArg_x21(v_val_3511_, v___x_3527_);
v___x_3529_ = lean_expr_eqv(v___x_3528_, v_x_3509_);
lean_dec_ref(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec(v___x_3524_);
lean_inc(v_a_3518_);
lean_inc_ref(v_a_3517_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3530_ = lean_apply_10(v_k_3512_, v_x_3509_, v_F_3510_, v_val_3511_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, lean_box(0));
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3531_ = lean_unsigned_to_nat(4u);
v___x_3532_ = lean_nat_sub(v___x_3524_, v___x_3531_);
v___x_3533_ = lean_nat_sub(v___x_3532_, v___x_3526_);
lean_dec(v___x_3532_);
v___x_3534_ = l_Lean_Expr_getRevArg_x21(v_val_3511_, v___x_3533_);
v___x_3535_ = l_Lean_Expr_isLambda(v___x_3534_);
lean_dec_ref(v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
lean_dec(v___x_3524_);
lean_inc(v_a_3518_);
lean_inc_ref(v_a_3517_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3536_ = lean_apply_10(v_k_3512_, v_x_3509_, v_F_3510_, v_val_3511_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, lean_box(0));
return v___x_3536_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3537_ = lean_unsigned_to_nat(5u);
v___x_3538_ = lean_nat_sub(v___x_3524_, v___x_3537_);
v___x_3539_ = lean_nat_sub(v___x_3538_, v___x_3526_);
lean_dec(v___x_3538_);
v___x_3540_ = l_Lean_Expr_getRevArg_x21(v_val_3511_, v___x_3539_);
v___x_3541_ = l_Lean_Expr_isLambda(v___x_3540_);
lean_dec_ref(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v___x_3524_);
lean_inc(v_a_3518_);
lean_inc_ref(v_a_3517_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3542_ = lean_apply_10(v_k_3512_, v_x_3509_, v_F_3510_, v_val_3511_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, lean_box(0));
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = l_Lean_Expr_fvarId_x21(v_F_3510_);
v___x_3544_ = l_Lean_FVarId_getDecl___redArg(v___x_3543_, v_a_3515_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; lean_object* v_dummy_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v_args_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc_n(v_a_3545_, 2);
lean_dec_ref(v___x_3544_);
v___x_3546_ = l_Lean_instInhabitedExpr;
v_dummy_3547_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3524_);
v___x_3548_ = lean_mk_array(v___x_3524_, v_dummy_3547_);
v___x_3549_ = lean_nat_sub(v___x_3524_, v___x_3526_);
lean_dec(v___x_3524_);
v_args_3550_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3511_, v___x_3548_, v___x_3549_);
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = lean_box(v___x_3535_);
lean_inc_ref(v_x_3509_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3553_, 0, v_a_3545_);
lean_closure_set(v___f_3553_, 1, v___x_3546_);
lean_closure_set(v___f_3553_, 2, v___x_3551_);
lean_closure_set(v___f_3553_, 3, v_x_3509_);
lean_closure_set(v___f_3553_, 4, v___x_3552_);
v___x_3554_ = lean_unsigned_to_nat(2u);
v___x_3555_ = lean_array_get(v___x_3546_, v_args_3550_, v___x_3554_);
v___x_3556_ = 0;
v___x_3557_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3555_, v___f_3553_, v___x_3556_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v_fst_3559_; lean_object* v_snd_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3619_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v_fst_3559_ = lean_ctor_get(v_a_3558_, 0);
v_snd_3560_ = lean_ctor_get(v_a_3558_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_a_3558_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3562_ = v_a_3558_;
v_isShared_3563_ = v_isSharedCheck_3619_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_snd_3560_);
lean_inc(v_fst_3559_);
lean_dec(v_a_3558_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3619_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_00_u03b1_3564_; lean_object* v_00_u03b2_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_00_u03b1_3564_ = lean_array_get(v___x_3546_, v_args_3550_, v___x_3551_);
v_00_u03b2_3565_ = lean_array_get(v___x_3546_, v_args_3550_, v___x_3526_);
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3567_ = lean_array_get(v___x_3546_, v_args_3550_, v___x_3531_);
lean_inc_ref(v_x_3509_);
lean_inc(v_a_3545_);
lean_inc_ref(v_k_3512_);
lean_inc(v_00_u03b2_3565_);
lean_inc(v_00_u03b1_3564_);
v___x_3568_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3546_, v___x_3551_, v_00_u03b1_3564_, v_00_u03b2_3565_, v___x_3523_, v_k_3512_, v___x_3554_, v___x_3556_, v___x_3535_, v_a_3545_, v_x_3509_, v___x_3526_, v___x_3566_, v___x_3567_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3571_ = lean_array_get(v___x_3546_, v_args_3550_, v___x_3537_);
lean_dec_ref(v_args_3550_);
lean_inc_ref(v_x_3509_);
lean_inc(v_00_u03b2_3565_);
lean_inc(v_00_u03b1_3564_);
v___x_3572_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3546_, v___x_3551_, v_00_u03b1_3564_, v_00_u03b2_3565_, v___x_3523_, v_k_3512_, v___x_3554_, v___x_3556_, v___x_3535_, v_a_3545_, v_x_3509_, v___x_3526_, v___x_3570_, v___x_3571_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
lean_inc(v_00_u03b1_3564_);
v___x_3574_ = l_Lean_Meta_getLevel(v_00_u03b1_3564_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
lean_inc(v_00_u03b2_3565_);
v___x_3576_ = l_Lean_Meta_getLevel(v_00_u03b2_3565_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3602_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3602_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3602_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3582_ = lean_box(0);
if (v_isShared_3563_ == 0)
{
lean_ctor_set_tag(v___x_3562_, 1);
lean_ctor_set(v___x_3562_, 1, v___x_3582_);
lean_ctor_set(v___x_3562_, 0, v_a_3577_);
v___x_3584_ = v___x_3562_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3577_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_a_3575_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3586_, 0, v_snd_3560_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = l_Lean_mkConst(v___x_3581_, v___x_3586_);
v___x_3588_ = lean_unsigned_to_nat(7u);
v___x_3589_ = lean_mk_empty_array_with_capacity(v___x_3588_);
v___x_3590_ = lean_array_push(v___x_3589_, v_00_u03b1_3564_);
v___x_3591_ = lean_array_push(v___x_3590_, v_00_u03b2_3565_);
v___x_3592_ = lean_array_push(v___x_3591_, v_fst_3559_);
v___x_3593_ = lean_array_push(v___x_3592_, v_x_3509_);
v___x_3594_ = lean_array_push(v___x_3593_, v_a_3569_);
v___x_3595_ = lean_array_push(v___x_3594_, v_a_3573_);
v___x_3596_ = lean_array_push(v___x_3595_, v_F_3510_);
v___x_3597_ = l_Lean_mkAppN(v___x_3587_, v___x_3596_);
lean_dec_ref(v___x_3596_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3597_);
v___x_3599_ = v___x_3579_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_a_3575_);
lean_dec(v_a_3573_);
lean_dec(v_a_3569_);
lean_dec(v_00_u03b2_3565_);
lean_dec(v_00_u03b1_3564_);
lean_del_object(v___x_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
v_a_3603_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3576_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3576_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_a_3573_);
lean_dec(v_a_3569_);
lean_dec(v_00_u03b2_3565_);
lean_dec(v_00_u03b1_3564_);
lean_del_object(v___x_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
v_a_3611_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3574_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3574_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_dec(v_a_3569_);
lean_dec(v_00_u03b2_3565_);
lean_dec(v_00_u03b1_3564_);
lean_del_object(v___x_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
return v___x_3572_;
}
}
else
{
lean_dec(v_00_u03b2_3565_);
lean_dec(v_00_u03b1_3564_);
lean_del_object(v___x_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec_ref(v_args_3550_);
lean_dec(v_a_3545_);
lean_dec_ref(v_k_3512_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
return v___x_3568_;
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec_ref(v_args_3550_);
lean_dec(v_a_3545_);
lean_dec_ref(v_k_3512_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
v_a_3620_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3557_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3557_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v___x_3524_);
lean_dec_ref(v_k_3512_);
lean_dec_ref(v_val_3511_);
lean_dec_ref(v_F_3510_);
lean_dec_ref(v_x_3509_);
v_a_3628_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3544_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3544_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3640_, lean_object* v_body_3641_, lean_object* v_k_3642_, lean_object* v___x_3643_, uint8_t v___x_3644_, uint8_t v___x_3645_, lean_object* v_FNew_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
lean_inc_ref(v_FNew_3646_);
lean_inc_ref(v___x_3640_);
v___x_3654_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3640_, v_FNew_3646_, v_body_3641_, v_k_3642_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref(v___x_3654_);
v___x_3656_ = lean_mk_empty_array_with_capacity(v___x_3643_);
v___x_3657_ = lean_array_push(v___x_3656_, v___x_3640_);
v___x_3658_ = lean_array_push(v___x_3657_, v_FNew_3646_);
v___x_3659_ = 1;
v___x_3660_ = l_Lean_Meta_mkLambdaFVars(v___x_3658_, v_a_3655_, v___x_3644_, v___x_3645_, v___x_3644_, v___x_3645_, v___x_3659_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec_ref(v___x_3658_);
return v___x_3660_;
}
else
{
lean_dec_ref(v_FNew_3646_);
lean_dec_ref(v___x_3640_);
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3661_, lean_object* v_body_3662_, lean_object* v_k_3663_, lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v___x_3666_, lean_object* v_FNew_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
uint8_t v___x_6949__boxed_3675_; uint8_t v___x_6950__boxed_3676_; lean_object* v_res_3677_; 
v___x_6949__boxed_3675_ = lean_unbox(v___x_3665_);
v___x_6950__boxed_3676_ = lean_unbox(v___x_3666_);
v_res_3677_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3661_, v_body_3662_, v_k_3663_, v___x_3664_, v___x_6949__boxed_3675_, v___x_6950__boxed_3676_, v_FNew_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___x_3664_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3678_, lean_object* v___x_3679_, lean_object* v_00_u03b1_3680_, lean_object* v_00_u03b2_3681_, lean_object* v___x_3682_, lean_object* v_ctorName_3683_, lean_object* v_k_3684_, lean_object* v___x_3685_, uint8_t v___x_3686_, uint8_t v___x_3687_, lean_object* v_a_3688_, lean_object* v_x_3689_, lean_object* v_xs_3690_, lean_object* v_body_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3699_ = lean_array_get_borrowed(v___x_3678_, v_xs_3690_, v___x_3679_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_00_u03b1_3680_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_00_u03b2_3681_);
lean_inc(v___x_3699_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3699_);
v___x_3703_ = lean_mk_empty_array_with_capacity(v___x_3682_);
v___x_3704_ = lean_array_push(v___x_3703_, v___x_3700_);
v___x_3705_ = lean_array_push(v___x_3704_, v___x_3701_);
v___x_3706_ = lean_array_push(v___x_3705_, v___x_3702_);
v___x_3707_ = l_Lean_Meta_mkAppOptM(v_ctorName_3683_, v___x_3706_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___f_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
v___x_3709_ = lean_box(v___x_3686_);
v___x_3710_ = lean_box(v___x_3687_);
lean_inc(v___x_3699_);
v___f_3711_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3711_, 0, v___x_3699_);
lean_closure_set(v___f_3711_, 1, v_body_3691_);
lean_closure_set(v___f_3711_, 2, v_k_3684_);
lean_closure_set(v___f_3711_, 3, v___x_3685_);
lean_closure_set(v___f_3711_, 4, v___x_3709_);
lean_closure_set(v___f_3711_, 5, v___x_3710_);
v___x_3712_ = l_Lean_LocalDecl_type(v_a_3688_);
v___x_3713_ = l_Lean_Expr_replaceFVar(v___x_3712_, v_x_3689_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v___x_3712_);
v___x_3714_ = l_Lean_LocalDecl_userName(v_a_3688_);
v___x_3715_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3714_, v___x_3713_, v___f_3711_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3715_;
}
else
{
lean_dec_ref(v_body_3691_);
lean_dec_ref(v_x_3689_);
lean_dec(v___x_3685_);
lean_dec_ref(v_k_3684_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3716_ = _args[0];
lean_object* v___x_3717_ = _args[1];
lean_object* v_00_u03b1_3718_ = _args[2];
lean_object* v_00_u03b2_3719_ = _args[3];
lean_object* v___x_3720_ = _args[4];
lean_object* v_ctorName_3721_ = _args[5];
lean_object* v_k_3722_ = _args[6];
lean_object* v___x_3723_ = _args[7];
lean_object* v___x_3724_ = _args[8];
lean_object* v___x_3725_ = _args[9];
lean_object* v_a_3726_ = _args[10];
lean_object* v_x_3727_ = _args[11];
lean_object* v_xs_3728_ = _args[12];
lean_object* v_body_3729_ = _args[13];
lean_object* v___y_3730_ = _args[14];
lean_object* v___y_3731_ = _args[15];
lean_object* v___y_3732_ = _args[16];
lean_object* v___y_3733_ = _args[17];
lean_object* v___y_3734_ = _args[18];
lean_object* v___y_3735_ = _args[19];
lean_object* v___y_3736_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3737_; uint8_t v___x_6971__boxed_3738_; lean_object* v_res_3739_; 
v___x_6970__boxed_3737_ = lean_unbox(v___x_3724_);
v___x_6971__boxed_3738_ = lean_unbox(v___x_3725_);
v_res_3739_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3716_, v___x_3717_, v_00_u03b1_3718_, v_00_u03b2_3719_, v___x_3720_, v_ctorName_3721_, v_k_3722_, v___x_3723_, v___x_6970__boxed_3737_, v___x_6971__boxed_3738_, v_a_3726_, v_x_3727_, v_xs_3728_, v_body_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec_ref(v_xs_3728_);
lean_dec_ref(v_a_3726_);
lean_dec(v___x_3720_);
lean_dec(v___x_3717_);
lean_dec_ref(v___x_3716_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3740_, lean_object* v___x_3741_, lean_object* v_00_u03b1_3742_, lean_object* v_00_u03b2_3743_, lean_object* v___x_3744_, lean_object* v_k_3745_, lean_object* v___x_3746_, uint8_t v___x_3747_, uint8_t v___x_3748_, lean_object* v_a_3749_, lean_object* v_x_3750_, lean_object* v___x_3751_, lean_object* v_ctorName_3752_, lean_object* v_minor_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_box(v___x_3747_);
v___x_3762_ = lean_box(v___x_3748_);
v___f_3763_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3763_, 0, v___x_3740_);
lean_closure_set(v___f_3763_, 1, v___x_3741_);
lean_closure_set(v___f_3763_, 2, v_00_u03b1_3742_);
lean_closure_set(v___f_3763_, 3, v_00_u03b2_3743_);
lean_closure_set(v___f_3763_, 4, v___x_3744_);
lean_closure_set(v___f_3763_, 5, v_ctorName_3752_);
lean_closure_set(v___f_3763_, 6, v_k_3745_);
lean_closure_set(v___f_3763_, 7, v___x_3746_);
lean_closure_set(v___f_3763_, 8, v___x_3761_);
lean_closure_set(v___f_3763_, 9, v___x_3762_);
lean_closure_set(v___f_3763_, 10, v_a_3749_);
lean_closure_set(v___f_3763_, 11, v_x_3750_);
v___x_3764_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3753_, v___x_3751_, v___f_3763_, v___x_3747_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3765_ = _args[0];
lean_object* v___x_3766_ = _args[1];
lean_object* v_00_u03b1_3767_ = _args[2];
lean_object* v_00_u03b2_3768_ = _args[3];
lean_object* v___x_3769_ = _args[4];
lean_object* v_k_3770_ = _args[5];
lean_object* v___x_3771_ = _args[6];
lean_object* v___x_3772_ = _args[7];
lean_object* v___x_3773_ = _args[8];
lean_object* v_a_3774_ = _args[9];
lean_object* v_x_3775_ = _args[10];
lean_object* v___x_3776_ = _args[11];
lean_object* v_ctorName_3777_ = _args[12];
lean_object* v_minor_3778_ = _args[13];
lean_object* v___y_3779_ = _args[14];
lean_object* v___y_3780_ = _args[15];
lean_object* v___y_3781_ = _args[16];
lean_object* v___y_3782_ = _args[17];
lean_object* v___y_3783_ = _args[18];
lean_object* v___y_3784_ = _args[19];
lean_object* v___y_3785_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3786_; uint8_t v___x_6935__boxed_3787_; lean_object* v_res_3788_; 
v___x_6934__boxed_3786_ = lean_unbox(v___x_3772_);
v___x_6935__boxed_3787_ = lean_unbox(v___x_3773_);
v_res_3788_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3765_, v___x_3766_, v_00_u03b1_3767_, v_00_u03b2_3768_, v___x_3769_, v_k_3770_, v___x_3771_, v___x_6934__boxed_3786_, v___x_6935__boxed_3787_, v_a_3774_, v_x_3775_, v___x_3776_, v_ctorName_3777_, v_minor_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3789_, lean_object* v_F_3790_, lean_object* v_val_3791_, lean_object* v_k_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3789_, v_F_3790_, v_val_3791_, v_k_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3801_, lean_object* v_name_3802_, uint8_t v_bi_3803_, lean_object* v_type_3804_, lean_object* v_k_3805_, uint8_t v_kind_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3802_, v_bi_3803_, v_type_3804_, v_k_3805_, v_kind_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3815_, lean_object* v_name_3816_, lean_object* v_bi_3817_, lean_object* v_type_3818_, lean_object* v_k_3819_, lean_object* v_kind_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_bi_boxed_3828_; uint8_t v_kind_boxed_3829_; lean_object* v_res_3830_; 
v_bi_boxed_3828_ = lean_unbox(v_bi_3817_);
v_kind_boxed_3829_ = lean_unbox(v_kind_3820_);
v_res_3830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3815_, v_name_3816_, v_bi_boxed_3828_, v_type_3818_, v_k_3819_, v_kind_boxed_3829_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3831_, lean_object* v_name_3832_, lean_object* v_type_3833_, lean_object* v_k_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3832_, v_type_3833_, v_k_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3843_, lean_object* v_name_3844_, lean_object* v_type_3845_, lean_object* v_k_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3843_, v_name_3844_, v_type_3845_, v_k_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
return v_res_3854_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3874__overap_3865_; lean_object* v___x_3866_; 
v___x_3864_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3865_ = lean_panic_fn_borrowed(v___x_3864_, v_msg_3856_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
v___x_3866_ = lean_apply_7(v___x_3874__overap_3865_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, lean_box(0));
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3875_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3880_ = lean_unsigned_to_nat(49u);
v___x_3881_ = lean_unsigned_to_nat(186u);
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3884_ = l_mkPanicMessageWithDecl(v___x_3883_, v___x_3882_, v___x_3881_, v___x_3880_, v___x_3879_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3890_, lean_object* v_a_3891_, lean_object* v_k_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___x_3897_, lean_object* v_FNew_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v___x_4042__boxed_3906_; uint8_t v___x_4043__boxed_3907_; uint8_t v___x_4044__boxed_3908_; lean_object* v_res_3909_; 
v___x_4042__boxed_3906_ = lean_unbox(v___x_3895_);
v___x_4043__boxed_3907_ = lean_unbox(v___x_3896_);
v___x_4044__boxed_3908_ = lean_unbox(v___x_3897_);
v_res_3909_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3890_, v_a_3891_, v_k_3892_, v___x_3893_, v___x_3894_, v___x_4042__boxed_3906_, v___x_4043__boxed_3907_, v___x_4044__boxed_3908_, v_FNew_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___x_3893_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3910_, lean_object* v___x_3911_, lean_object* v___x_3912_, lean_object* v___x_3913_, uint8_t v___x_3914_, uint8_t v___x_3915_, lean_object* v_00_u03b1_3916_, lean_object* v_00_u03b2_3917_, lean_object* v___x_3918_, lean_object* v_k_3919_, lean_object* v___x_3920_, lean_object* v_a_3921_, lean_object* v_x_3922_, lean_object* v_xs_3923_, lean_object* v_body_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; lean_object* v___x_3938_; 
v___x_3932_ = lean_array_get(v___x_3910_, v_xs_3923_, v___x_3911_);
v___x_3933_ = lean_array_get(v___x_3910_, v_xs_3923_, v___x_3912_);
v___x_3934_ = lean_array_get_size(v_xs_3923_);
v___x_3935_ = l_Array_toSubarray___redArg(v_xs_3923_, v___x_3913_, v___x_3934_);
v___x_3936_ = l_Subarray_copy___redArg(v___x_3935_);
v___x_3937_ = 1;
v___x_3938_ = l_Lean_Meta_mkLambdaFVars(v___x_3936_, v_body_3924_, v___x_3914_, v___x_3915_, v___x_3914_, v___x_3915_, v___x_3937_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec_ref(v___x_3936_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3965_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3965_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3965_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3942_ == 0)
{
lean_ctor_set_tag(v___x_3941_, 1);
lean_ctor_set(v___x_3941_, 0, v_00_u03b1_3916_);
v___x_3945_ = v___x_3941_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_00_u03b1_3916_);
v___x_3945_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v_00_u03b2_3917_);
lean_inc(v___x_3932_);
v___x_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3932_);
lean_inc(v___x_3933_);
v___x_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3933_);
v___x_3949_ = lean_mk_empty_array_with_capacity(v___x_3918_);
v___x_3950_ = lean_array_push(v___x_3949_, v___x_3945_);
v___x_3951_ = lean_array_push(v___x_3950_, v___x_3946_);
v___x_3952_ = lean_array_push(v___x_3951_, v___x_3947_);
v___x_3953_ = lean_array_push(v___x_3952_, v___x_3948_);
v___x_3954_ = l_Lean_Meta_mkAppOptM(v___x_3943_, v___x_3953_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___f_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref(v___x_3954_);
v___x_3956_ = lean_box(v___x_3914_);
v___x_3957_ = lean_box(v___x_3915_);
v___x_3958_ = lean_box(v___x_3937_);
v___f_3959_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3959_, 0, v___x_3933_);
lean_closure_set(v___f_3959_, 1, v_a_3939_);
lean_closure_set(v___f_3959_, 2, v_k_3919_);
lean_closure_set(v___f_3959_, 3, v___x_3920_);
lean_closure_set(v___f_3959_, 4, v___x_3932_);
lean_closure_set(v___f_3959_, 5, v___x_3956_);
lean_closure_set(v___f_3959_, 6, v___x_3957_);
lean_closure_set(v___f_3959_, 7, v___x_3958_);
v___x_3960_ = l_Lean_LocalDecl_type(v_a_3921_);
v___x_3961_ = l_Lean_Expr_replaceFVar(v___x_3960_, v_x_3922_, v_a_3955_);
lean_dec(v_a_3955_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = l_Lean_LocalDecl_userName(v_a_3921_);
v___x_3963_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3962_, v___x_3961_, v___f_3959_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3963_;
}
else
{
lean_dec(v_a_3939_);
lean_dec(v___x_3933_);
lean_dec(v___x_3932_);
lean_dec_ref(v_x_3922_);
lean_dec(v___x_3920_);
lean_dec_ref(v_k_3919_);
return v___x_3954_;
}
}
}
}
else
{
lean_dec(v___x_3933_);
lean_dec(v___x_3932_);
lean_dec_ref(v_x_3922_);
lean_dec(v___x_3920_);
lean_dec_ref(v_k_3919_);
lean_dec_ref(v_00_u03b2_3917_);
lean_dec_ref(v_00_u03b1_3916_);
return v___x_3938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3966_ = _args[0];
lean_object* v___x_3967_ = _args[1];
lean_object* v___x_3968_ = _args[2];
lean_object* v___x_3969_ = _args[3];
lean_object* v___x_3970_ = _args[4];
lean_object* v___x_3971_ = _args[5];
lean_object* v_00_u03b1_3972_ = _args[6];
lean_object* v_00_u03b2_3973_ = _args[7];
lean_object* v___x_3974_ = _args[8];
lean_object* v_k_3975_ = _args[9];
lean_object* v___x_3976_ = _args[10];
lean_object* v_a_3977_ = _args[11];
lean_object* v_x_3978_ = _args[12];
lean_object* v_xs_3979_ = _args[13];
lean_object* v_body_3980_ = _args[14];
lean_object* v___y_3981_ = _args[15];
lean_object* v___y_3982_ = _args[16];
lean_object* v___y_3983_ = _args[17];
lean_object* v___y_3984_ = _args[18];
lean_object* v___y_3985_ = _args[19];
lean_object* v___y_3986_ = _args[20];
lean_object* v___y_3987_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_3988_; uint8_t v___x_4070__boxed_3989_; lean_object* v_res_3990_; 
v___x_4069__boxed_3988_ = lean_unbox(v___x_3970_);
v___x_4070__boxed_3989_ = lean_unbox(v___x_3971_);
v_res_3990_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3966_, v___x_3967_, v___x_3968_, v___x_3969_, v___x_4069__boxed_3988_, v___x_4070__boxed_3989_, v_00_u03b1_3972_, v_00_u03b2_3973_, v___x_3974_, v_k_3975_, v___x_3976_, v_a_3977_, v_x_3978_, v_xs_3979_, v_body_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec_ref(v_a_3977_);
lean_dec(v___x_3974_);
lean_dec(v___x_3968_);
lean_dec(v___x_3967_);
lean_dec_ref(v___x_3966_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3994_, lean_object* v_F_3995_, lean_object* v_val_3996_, lean_object* v_k_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; uint8_t v___y_4015_; uint8_t v___x_4107_; 
v___x_4107_ = l_Lean_Expr_isFVar(v_x_3994_);
if (v___x_4107_ == 0)
{
v___y_4015_ = v___x_4107_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4108_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4109_ = lean_unsigned_to_nat(5u);
v___x_4110_ = l_Lean_Expr_isAppOfArity(v_val_3996_, v___x_4108_, v___x_4109_);
v___y_4015_ = v___x_4110_;
goto v___jp_4014_;
}
v___jp_4005_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4013_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4012_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4013_;
}
v___jp_4014_:
{
if (v___y_4015_ == 0)
{
lean_object* v___x_4016_; 
lean_dec_ref(v_x_3994_);
lean_inc(v_a_4003_);
lean_inc_ref(v_a_4002_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
v___x_4016_ = lean_apply_9(v_k_3997_, v_F_3995_, v_val_3996_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, lean_box(0));
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4017_ = lean_unsigned_to_nat(3u);
v___x_4018_ = l_Lean_Expr_getAppNumArgs(v_val_3996_);
v___x_4019_ = lean_nat_sub(v___x_4018_, v___x_4017_);
v___x_4020_ = lean_unsigned_to_nat(1u);
v___x_4021_ = lean_nat_sub(v___x_4019_, v___x_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = l_Lean_Expr_getRevArg_x21(v_val_3996_, v___x_4021_);
v___x_4023_ = lean_expr_eqv(v___x_4022_, v_x_3994_);
lean_dec_ref(v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; 
lean_dec(v___x_4018_);
lean_dec_ref(v_x_3994_);
lean_inc(v_a_4003_);
lean_inc_ref(v_a_4002_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
v___x_4024_ = lean_apply_9(v_k_3997_, v_F_3995_, v_val_3996_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, lean_box(0));
return v___x_4024_;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v___x_4025_ = lean_unsigned_to_nat(4u);
v___x_4026_ = lean_nat_sub(v___x_4018_, v___x_4025_);
v___x_4027_ = lean_nat_sub(v___x_4026_, v___x_4020_);
lean_dec(v___x_4026_);
v___x_4028_ = l_Lean_Expr_getRevArg_x21(v_val_3996_, v___x_4027_);
v___x_4029_ = l_Lean_Expr_isLambda(v___x_4028_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_dec_ref(v___x_4028_);
lean_dec(v___x_4018_);
lean_dec_ref(v_x_3994_);
lean_inc(v_a_4003_);
lean_inc_ref(v_a_4002_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
v___x_4030_ = lean_apply_9(v_k_3997_, v_F_3995_, v_val_3996_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, lean_box(0));
return v___x_4030_;
}
else
{
lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4031_ = l_Lean_Expr_bindingBody_x21(v___x_4028_);
lean_dec_ref(v___x_4028_);
v___x_4032_ = l_Lean_Expr_isLambda(v___x_4031_);
lean_dec_ref(v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec(v___x_4018_);
lean_dec_ref(v_x_3994_);
lean_inc(v_a_4003_);
lean_inc_ref(v_a_4002_);
lean_inc(v_a_4001_);
lean_inc_ref(v_a_4000_);
lean_inc(v_a_3999_);
lean_inc_ref(v_a_3998_);
v___x_4033_ = lean_apply_9(v_k_3997_, v_F_3995_, v_val_3996_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, lean_box(0));
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = l_Lean_Expr_getAppFn(v_val_3996_);
v___x_4035_ = l_Lean_Expr_constLevels_x21(v___x_4034_);
lean_dec_ref(v___x_4034_);
if (lean_obj_tag(v___x_4035_) == 1)
{
lean_object* v_tail_4036_; 
v_tail_4036_ = lean_ctor_get(v___x_4035_, 1);
lean_inc(v_tail_4036_);
lean_dec_ref(v___x_4035_);
if (lean_obj_tag(v_tail_4036_) == 1)
{
lean_object* v_tail_4037_; 
v_tail_4037_ = lean_ctor_get(v_tail_4036_, 1);
lean_inc(v_tail_4037_);
if (lean_obj_tag(v_tail_4037_) == 1)
{
lean_object* v_tail_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4105_; 
v_tail_4038_ = lean_ctor_get(v_tail_4037_, 1);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_tail_4037_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v_tail_4037_, 0);
lean_dec(v_unused_4106_);
v___x_4040_ = v_tail_4037_;
v_isShared_4041_ = v_isSharedCheck_4105_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_tail_4038_);
lean_dec(v_tail_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4105_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
if (lean_obj_tag(v_tail_4038_) == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = l_Lean_Expr_fvarId_x21(v_F_3995_);
v___x_4043_ = l_Lean_FVarId_getDecl___redArg(v___x_4042_, v_a_4000_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v_dummy_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_args_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___f_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc_n(v_a_4044_, 2);
lean_dec_ref(v___x_4043_);
v___x_4045_ = l_Lean_instInhabitedExpr;
v_dummy_4046_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_4018_);
v___x_4047_ = lean_mk_array(v___x_4018_, v_dummy_4046_);
v___x_4048_ = lean_nat_sub(v___x_4018_, v___x_4020_);
lean_dec(v___x_4018_);
v_args_4049_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3996_, v___x_4047_, v___x_4048_);
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_box(v___x_4029_);
lean_inc_ref(v_x_3994_);
v___f_4052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4052_, 0, v_a_4044_);
lean_closure_set(v___f_4052_, 1, v___x_4045_);
lean_closure_set(v___f_4052_, 2, v___x_4050_);
lean_closure_set(v___f_4052_, 3, v_x_3994_);
lean_closure_set(v___f_4052_, 4, v___x_4051_);
v___x_4053_ = lean_unsigned_to_nat(2u);
v___x_4054_ = lean_array_get(v___x_4045_, v_args_4049_, v___x_4053_);
v___x_4055_ = 0;
v___x_4056_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4054_, v___f_4052_, v___x_4055_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v_fst_4058_; lean_object* v_snd_4059_; lean_object* v_00_u03b1_4060_; lean_object* v_00_u03b2_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v_fst_4058_ = lean_ctor_get(v_a_4057_, 0);
lean_inc(v_fst_4058_);
v_snd_4059_ = lean_ctor_get(v_a_4057_, 1);
lean_inc(v_snd_4059_);
lean_dec(v_a_4057_);
v_00_u03b1_4060_ = lean_array_get(v___x_4045_, v_args_4049_, v___x_4050_);
v_00_u03b2_4061_ = lean_array_get(v___x_4045_, v_args_4049_, v___x_4020_);
v___x_4062_ = lean_box(v___x_4055_);
v___x_4063_ = lean_box(v___x_4029_);
lean_inc_ref(v_x_3994_);
lean_inc(v_00_u03b2_4061_);
lean_inc(v_00_u03b1_4060_);
v___f_4064_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4064_, 0, v___x_4045_);
lean_closure_set(v___f_4064_, 1, v___x_4050_);
lean_closure_set(v___f_4064_, 2, v___x_4020_);
lean_closure_set(v___f_4064_, 3, v___x_4053_);
lean_closure_set(v___f_4064_, 4, v___x_4062_);
lean_closure_set(v___f_4064_, 5, v___x_4063_);
lean_closure_set(v___f_4064_, 6, v_00_u03b1_4060_);
lean_closure_set(v___f_4064_, 7, v_00_u03b2_4061_);
lean_closure_set(v___f_4064_, 8, v___x_4025_);
lean_closure_set(v___f_4064_, 9, v_k_3997_);
lean_closure_set(v___f_4064_, 10, v___x_4017_);
lean_closure_set(v___f_4064_, 11, v_a_4044_);
lean_closure_set(v___f_4064_, 12, v_x_3994_);
v___x_4065_ = lean_array_get(v___x_4045_, v_args_4049_, v___x_4025_);
lean_dec_ref(v_args_4049_);
v___x_4066_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4065_, v___f_4064_, v___x_4055_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4088_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4088_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4088_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v_tail_4036_);
lean_ctor_set(v___x_4040_, 0, v_snd_4059_);
v___x_4073_ = v___x_4040_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_snd_4059_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_tail_4036_);
v___x_4073_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4074_ = l_Lean_mkConst(v___x_4071_, v___x_4073_);
v___x_4075_ = lean_unsigned_to_nat(6u);
v___x_4076_ = lean_mk_empty_array_with_capacity(v___x_4075_);
v___x_4077_ = lean_array_push(v___x_4076_, v_00_u03b1_4060_);
v___x_4078_ = lean_array_push(v___x_4077_, v_00_u03b2_4061_);
v___x_4079_ = lean_array_push(v___x_4078_, v_fst_4058_);
v___x_4080_ = lean_array_push(v___x_4079_, v_x_3994_);
v___x_4081_ = lean_array_push(v___x_4080_, v_a_4067_);
v___x_4082_ = lean_array_push(v___x_4081_, v_F_3995_);
v___x_4083_ = l_Lean_mkAppN(v___x_4074_, v___x_4082_);
lean_dec_ref(v___x_4082_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 0, v___x_4083_);
v___x_4085_ = v___x_4069_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4061_);
lean_dec(v_00_u03b1_4060_);
lean_dec(v_snd_4059_);
lean_dec(v_fst_4058_);
lean_del_object(v___x_4040_);
lean_dec_ref(v_tail_4036_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
return v___x_4066_;
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v_args_4049_);
lean_dec(v_a_4044_);
lean_del_object(v___x_4040_);
lean_dec_ref(v_tail_4036_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v_a_4089_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4056_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4056_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_del_object(v___x_4040_);
lean_dec_ref(v_tail_4036_);
lean_dec(v___x_4018_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_val_3996_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v_a_4097_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4043_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4043_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_del_object(v___x_4040_);
lean_dec(v_tail_4038_);
lean_dec_ref(v_tail_4036_);
lean_dec(v___x_4018_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_val_3996_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
v___y_4011_ = v_a_4003_;
goto v___jp_4005_;
}
}
}
else
{
lean_dec(v_tail_4037_);
lean_dec_ref(v_tail_4036_);
lean_dec(v___x_4018_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_val_3996_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
v___y_4011_ = v_a_4003_;
goto v___jp_4005_;
}
}
else
{
lean_dec(v_tail_4036_);
lean_dec(v___x_4018_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_val_3996_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
v___y_4011_ = v_a_4003_;
goto v___jp_4005_;
}
}
else
{
lean_dec(v___x_4035_);
lean_dec(v___x_4018_);
lean_dec_ref(v_k_3997_);
lean_dec_ref(v_val_3996_);
lean_dec_ref(v_F_3995_);
lean_dec_ref(v_x_3994_);
v___y_4006_ = v_a_3998_;
v___y_4007_ = v_a_3999_;
v___y_4008_ = v_a_4000_;
v___y_4009_ = v_a_4001_;
v___y_4010_ = v_a_4002_;
v___y_4011_ = v_a_4003_;
goto v___jp_4005_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4111_, lean_object* v_a_4112_, lean_object* v_k_4113_, lean_object* v___x_4114_, lean_object* v___x_4115_, uint8_t v___x_4116_, uint8_t v___x_4117_, uint8_t v___x_4118_, lean_object* v_FNew_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
lean_inc_ref(v_FNew_4119_);
lean_inc_ref(v___x_4111_);
v___x_4127_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4111_, v_FNew_4119_, v_a_4112_, v_k_4113_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = lean_mk_empty_array_with_capacity(v___x_4114_);
v___x_4130_ = lean_array_push(v___x_4129_, v___x_4115_);
v___x_4131_ = lean_array_push(v___x_4130_, v___x_4111_);
v___x_4132_ = lean_array_push(v___x_4131_, v_FNew_4119_);
v___x_4133_ = l_Lean_Meta_mkLambdaFVars(v___x_4132_, v_a_4128_, v___x_4116_, v___x_4117_, v___x_4116_, v___x_4117_, v___x_4118_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec_ref(v___x_4132_);
return v___x_4133_;
}
else
{
lean_dec_ref(v_FNew_4119_);
lean_dec_ref(v___x_4115_);
lean_dec_ref(v___x_4111_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4134_, lean_object* v_F_4135_, lean_object* v_val_4136_, lean_object* v_k_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4134_, v_F_4135_, v_val_4136_, v_k_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_ref_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec_ref(v___x_4159_);
v_ref_4160_ = lean_ctor_get(v___y_4156_, 5);
v___x_4161_ = 0;
v___x_4162_ = l_Lean_SourceInfo_fromRef(v_ref_4160_, v___x_4161_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4164_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4162_);
v___x_4165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4162_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Lean_Syntax_node1(v___x_4162_, v___x_4163_, v___x_4165_);
v___x_4167_ = l_Lean_Elab_Tactic_evalTactic(v___x_4166_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
return v___x_4167_;
}
else
{
return v___x_4159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___f_4187_; lean_object* v___x_4188_; 
v___f_4187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4188_ = l_Lean_Elab_Tactic_run(v_mvarId_4179_, v___f_4187_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4199_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4191_ = v___x_4188_;
v_isShared_4192_ = v_isSharedCheck_4199_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4199_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
uint8_t v___x_4193_; 
v___x_4193_ = l_List_isEmpty___redArg(v_a_4189_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; 
lean_del_object(v___x_4191_);
v___x_4194_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4189_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
return v___x_4194_;
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4197_; 
lean_dec(v_a_4189_);
v___x_4195_ = lean_box(0);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 0, v___x_4195_);
v___x_4197_ = v___x_4191_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
v_a_4200_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4188_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4188_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4217_, lean_object* v_x_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v_ks_4221_; lean_object* v_vs_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4246_; 
v_ks_4221_ = lean_ctor_get(v_x_4217_, 0);
v_vs_4222_ = lean_ctor_get(v_x_4217_, 1);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_x_4217_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4224_ = v_x_4217_;
v_isShared_4225_ = v_isSharedCheck_4246_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_vs_4222_);
lean_inc(v_ks_4221_);
lean_dec(v_x_4217_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4246_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4226_ = lean_array_get_size(v_ks_4221_);
v___x_4227_ = lean_nat_dec_lt(v_x_4218_, v___x_4226_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4231_; 
lean_dec(v_x_4218_);
v___x_4228_ = lean_array_push(v_ks_4221_, v_x_4219_);
v___x_4229_ = lean_array_push(v_vs_4222_, v_x_4220_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 1, v___x_4229_);
lean_ctor_set(v___x_4224_, 0, v___x_4228_);
v___x_4231_ = v___x_4224_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4228_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v___x_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
else
{
lean_object* v_k_x27_4233_; uint8_t v___x_4234_; 
v_k_x27_4233_ = lean_array_fget_borrowed(v_ks_4221_, v_x_4218_);
v___x_4234_ = l_Lean_instBEqMVarId_beq(v_x_4219_, v_k_x27_4233_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4236_; 
if (v_isShared_4225_ == 0)
{
v___x_4236_ = v___x_4224_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_ks_4221_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_vs_4222_);
v___x_4236_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_unsigned_to_nat(1u);
v___x_4238_ = lean_nat_add(v_x_4218_, v___x_4237_);
lean_dec(v_x_4218_);
v_x_4217_ = v___x_4236_;
v_x_4218_ = v___x_4238_;
goto _start;
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4241_ = lean_array_fset(v_ks_4221_, v_x_4218_, v_x_4219_);
v___x_4242_ = lean_array_fset(v_vs_4222_, v_x_4218_, v_x_4220_);
lean_dec(v_x_4218_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 1, v___x_4242_);
lean_ctor_set(v___x_4224_, 0, v___x_4241_);
v___x_4244_ = v___x_4224_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4247_, lean_object* v_k_4248_, lean_object* v_v_4249_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_unsigned_to_nat(0u);
v___x_4251_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4247_, v___x_4250_, v_k_4248_, v_v_4249_);
return v___x_4251_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4252_; size_t v___x_4253_; size_t v___x_4254_; 
v___x_4252_ = ((size_t)5ULL);
v___x_4253_ = ((size_t)1ULL);
v___x_4254_ = lean_usize_shift_left(v___x_4253_, v___x_4252_);
return v___x_4254_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; 
v___x_4255_ = ((size_t)1ULL);
v___x_4256_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4257_ = lean_usize_sub(v___x_4256_, v___x_4255_);
return v___x_4257_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4259_, size_t v_x_4260_, size_t v_x_4261_, lean_object* v_x_4262_, lean_object* v_x_4263_){
_start:
{
if (lean_obj_tag(v_x_4259_) == 0)
{
lean_object* v_es_4264_; size_t v___x_4265_; size_t v___x_4266_; size_t v___x_4267_; size_t v___x_4268_; lean_object* v_j_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v_es_4264_ = lean_ctor_get(v_x_4259_, 0);
v___x_4265_ = ((size_t)5ULL);
v___x_4266_ = ((size_t)1ULL);
v___x_4267_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4268_ = lean_usize_land(v_x_4260_, v___x_4267_);
v_j_4269_ = lean_usize_to_nat(v___x_4268_);
v___x_4270_ = lean_array_get_size(v_es_4264_);
v___x_4271_ = lean_nat_dec_lt(v_j_4269_, v___x_4270_);
if (v___x_4271_ == 0)
{
lean_dec(v_j_4269_);
lean_dec(v_x_4263_);
lean_dec(v_x_4262_);
return v_x_4259_;
}
else
{
lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4308_; 
lean_inc_ref(v_es_4264_);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_x_4259_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; 
v_unused_4309_ = lean_ctor_get(v_x_4259_, 0);
lean_dec(v_unused_4309_);
v___x_4273_ = v_x_4259_;
v_isShared_4274_ = v_isSharedCheck_4308_;
goto v_resetjp_4272_;
}
else
{
lean_dec(v_x_4259_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4308_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v_v_4275_; lean_object* v___x_4276_; lean_object* v_xs_x27_4277_; lean_object* v___y_4279_; 
v_v_4275_ = lean_array_fget(v_es_4264_, v_j_4269_);
v___x_4276_ = lean_box(0);
v_xs_x27_4277_ = lean_array_fset(v_es_4264_, v_j_4269_, v___x_4276_);
switch(lean_obj_tag(v_v_4275_))
{
case 0:
{
lean_object* v_key_4284_; lean_object* v_val_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4295_; 
v_key_4284_ = lean_ctor_get(v_v_4275_, 0);
v_val_4285_ = lean_ctor_get(v_v_4275_, 1);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_v_4275_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4287_ = v_v_4275_;
v_isShared_4288_ = v_isSharedCheck_4295_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_val_4285_);
lean_inc(v_key_4284_);
lean_dec(v_v_4275_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4295_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
uint8_t v___x_4289_; 
v___x_4289_ = l_Lean_instBEqMVarId_beq(v_x_4262_, v_key_4284_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_del_object(v___x_4287_);
v___x_4290_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4284_, v_val_4285_, v_x_4262_, v_x_4263_);
v___x_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
v___y_4279_ = v___x_4291_;
goto v___jp_4278_;
}
else
{
lean_object* v___x_4293_; 
lean_dec(v_val_4285_);
lean_dec(v_key_4284_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 1, v_x_4263_);
lean_ctor_set(v___x_4287_, 0, v_x_4262_);
v___x_4293_ = v___x_4287_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_x_4262_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_x_4263_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
v___y_4279_ = v___x_4293_;
goto v___jp_4278_;
}
}
}
}
case 1:
{
lean_object* v_node_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4306_; 
v_node_4296_ = lean_ctor_get(v_v_4275_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_v_4275_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4298_ = v_v_4275_;
v_isShared_4299_ = v_isSharedCheck_4306_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_node_4296_);
lean_dec(v_v_4275_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4306_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4300_ = lean_usize_shift_right(v_x_4260_, v___x_4265_);
v___x_4301_ = lean_usize_add(v_x_4261_, v___x_4266_);
v___x_4302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4296_, v___x_4300_, v___x_4301_, v_x_4262_, v_x_4263_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v___x_4302_);
v___x_4304_ = v___x_4298_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
v___y_4279_ = v___x_4304_;
goto v___jp_4278_;
}
}
}
default: 
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_x_4262_);
lean_ctor_set(v___x_4307_, 1, v_x_4263_);
v___y_4279_ = v___x_4307_;
goto v___jp_4278_;
}
}
v___jp_4278_:
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4280_ = lean_array_fset(v_xs_x27_4277_, v_j_4269_, v___y_4279_);
lean_dec(v_j_4269_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4280_);
v___x_4282_ = v___x_4273_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
else
{
lean_object* v_ks_4310_; lean_object* v_vs_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4331_; 
v_ks_4310_ = lean_ctor_get(v_x_4259_, 0);
v_vs_4311_ = lean_ctor_get(v_x_4259_, 1);
v_isSharedCheck_4331_ = !lean_is_exclusive(v_x_4259_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4313_ = v_x_4259_;
v_isShared_4314_ = v_isSharedCheck_4331_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_vs_4311_);
lean_inc(v_ks_4310_);
lean_dec(v_x_4259_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4331_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_ks_4310_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_vs_4311_);
v___x_4316_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v_newNode_4317_; uint8_t v___y_4319_; size_t v___x_4325_; uint8_t v___x_4326_; 
v_newNode_4317_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4316_, v_x_4262_, v_x_4263_);
v___x_4325_ = ((size_t)7ULL);
v___x_4326_ = lean_usize_dec_le(v___x_4325_, v_x_4261_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4327_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4317_);
v___x_4328_ = lean_unsigned_to_nat(4u);
v___x_4329_ = lean_nat_dec_lt(v___x_4327_, v___x_4328_);
lean_dec(v___x_4327_);
v___y_4319_ = v___x_4329_;
goto v___jp_4318_;
}
else
{
v___y_4319_ = v___x_4326_;
goto v___jp_4318_;
}
v___jp_4318_:
{
if (v___y_4319_ == 0)
{
lean_object* v_ks_4320_; lean_object* v_vs_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_ks_4320_ = lean_ctor_get(v_newNode_4317_, 0);
lean_inc_ref(v_ks_4320_);
v_vs_4321_ = lean_ctor_get(v_newNode_4317_, 1);
lean_inc_ref(v_vs_4321_);
lean_dec_ref(v_newNode_4317_);
v___x_4322_ = lean_unsigned_to_nat(0u);
v___x_4323_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_4324_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4261_, v_ks_4320_, v_vs_4321_, v___x_4322_, v___x_4323_);
lean_dec_ref(v_vs_4321_);
lean_dec_ref(v_ks_4320_);
return v___x_4324_;
}
else
{
return v_newNode_4317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4332_, lean_object* v_keys_4333_, lean_object* v_vals_4334_, lean_object* v_i_4335_, lean_object* v_entries_4336_){
_start:
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_array_get_size(v_keys_4333_);
v___x_4338_ = lean_nat_dec_lt(v_i_4335_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_dec(v_i_4335_);
return v_entries_4336_;
}
else
{
lean_object* v_k_4339_; lean_object* v_v_4340_; uint64_t v___x_4341_; size_t v_h_4342_; size_t v___x_4343_; lean_object* v___x_4344_; size_t v___x_4345_; size_t v___x_4346_; size_t v___x_4347_; size_t v_h_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_k_4339_ = lean_array_fget_borrowed(v_keys_4333_, v_i_4335_);
v_v_4340_ = lean_array_fget_borrowed(v_vals_4334_, v_i_4335_);
v___x_4341_ = l_Lean_instHashableMVarId_hash(v_k_4339_);
v_h_4342_ = lean_uint64_to_usize(v___x_4341_);
v___x_4343_ = ((size_t)5ULL);
v___x_4344_ = lean_unsigned_to_nat(1u);
v___x_4345_ = ((size_t)1ULL);
v___x_4346_ = lean_usize_sub(v_depth_4332_, v___x_4345_);
v___x_4347_ = lean_usize_mul(v___x_4343_, v___x_4346_);
v_h_4348_ = lean_usize_shift_right(v_h_4342_, v___x_4347_);
v___x_4349_ = lean_nat_add(v_i_4335_, v___x_4344_);
lean_dec(v_i_4335_);
lean_inc(v_v_4340_);
lean_inc(v_k_4339_);
v___x_4350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4336_, v_h_4348_, v_depth_4332_, v_k_4339_, v_v_4340_);
v_i_4335_ = v___x_4349_;
v_entries_4336_ = v___x_4350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4352_, lean_object* v_keys_4353_, lean_object* v_vals_4354_, lean_object* v_i_4355_, lean_object* v_entries_4356_){
_start:
{
size_t v_depth_boxed_4357_; lean_object* v_res_4358_; 
v_depth_boxed_4357_ = lean_unbox_usize(v_depth_4352_);
lean_dec(v_depth_4352_);
v_res_4358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4357_, v_keys_4353_, v_vals_4354_, v_i_4355_, v_entries_4356_);
lean_dec_ref(v_vals_4354_);
lean_dec_ref(v_keys_4353_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4359_, lean_object* v_x_4360_, lean_object* v_x_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_){
_start:
{
size_t v_x_4261__boxed_4364_; size_t v_x_4262__boxed_4365_; lean_object* v_res_4366_; 
v_x_4261__boxed_4364_ = lean_unbox_usize(v_x_4360_);
lean_dec(v_x_4360_);
v_x_4262__boxed_4365_ = lean_unbox_usize(v_x_4361_);
lean_dec(v_x_4361_);
v_res_4366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4359_, v_x_4261__boxed_4364_, v_x_4262__boxed_4365_, v_x_4362_, v_x_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4367_, lean_object* v_x_4368_, lean_object* v_x_4369_){
_start:
{
uint64_t v___x_4370_; size_t v___x_4371_; size_t v___x_4372_; lean_object* v___x_4373_; 
v___x_4370_ = l_Lean_instHashableMVarId_hash(v_x_4368_);
v___x_4371_ = lean_uint64_to_usize(v___x_4370_);
v___x_4372_ = ((size_t)1ULL);
v___x_4373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4367_, v___x_4371_, v___x_4372_, v_x_4368_, v_x_4369_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4374_, lean_object* v_val_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v_mctx_4379_; lean_object* v_cache_4380_; lean_object* v_zetaDeltaFVarIds_4381_; lean_object* v_postponed_4382_; lean_object* v_diag_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4411_; 
v___x_4378_ = lean_st_ref_take(v___y_4376_);
v_mctx_4379_ = lean_ctor_get(v___x_4378_, 0);
v_cache_4380_ = lean_ctor_get(v___x_4378_, 1);
v_zetaDeltaFVarIds_4381_ = lean_ctor_get(v___x_4378_, 2);
v_postponed_4382_ = lean_ctor_get(v___x_4378_, 3);
v_diag_4383_ = lean_ctor_get(v___x_4378_, 4);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4385_ = v___x_4378_;
v_isShared_4386_ = v_isSharedCheck_4411_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_diag_4383_);
lean_inc(v_postponed_4382_);
lean_inc(v_zetaDeltaFVarIds_4381_);
lean_inc(v_cache_4380_);
lean_inc(v_mctx_4379_);
lean_dec(v___x_4378_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4411_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v_depth_4387_; lean_object* v_levelAssignDepth_4388_; lean_object* v_lmvarCounter_4389_; lean_object* v_mvarCounter_4390_; lean_object* v_lDecls_4391_; lean_object* v_decls_4392_; lean_object* v_userNames_4393_; lean_object* v_lAssignment_4394_; lean_object* v_eAssignment_4395_; lean_object* v_dAssignment_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4410_; 
v_depth_4387_ = lean_ctor_get(v_mctx_4379_, 0);
v_levelAssignDepth_4388_ = lean_ctor_get(v_mctx_4379_, 1);
v_lmvarCounter_4389_ = lean_ctor_get(v_mctx_4379_, 2);
v_mvarCounter_4390_ = lean_ctor_get(v_mctx_4379_, 3);
v_lDecls_4391_ = lean_ctor_get(v_mctx_4379_, 4);
v_decls_4392_ = lean_ctor_get(v_mctx_4379_, 5);
v_userNames_4393_ = lean_ctor_get(v_mctx_4379_, 6);
v_lAssignment_4394_ = lean_ctor_get(v_mctx_4379_, 7);
v_eAssignment_4395_ = lean_ctor_get(v_mctx_4379_, 8);
v_dAssignment_4396_ = lean_ctor_get(v_mctx_4379_, 9);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_mctx_4379_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4398_ = v_mctx_4379_;
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_dAssignment_4396_);
lean_inc(v_eAssignment_4395_);
lean_inc(v_lAssignment_4394_);
lean_inc(v_userNames_4393_);
lean_inc(v_decls_4392_);
lean_inc(v_lDecls_4391_);
lean_inc(v_mvarCounter_4390_);
lean_inc(v_lmvarCounter_4389_);
lean_inc(v_levelAssignDepth_4388_);
lean_inc(v_depth_4387_);
lean_dec(v_mctx_4379_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4400_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4395_, v_mvarId_4374_, v_val_4375_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 8, v___x_4400_);
v___x_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_depth_4387_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_levelAssignDepth_4388_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_lmvarCounter_4389_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_mvarCounter_4390_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v_lDecls_4391_);
lean_ctor_set(v_reuseFailAlloc_4409_, 5, v_decls_4392_);
lean_ctor_set(v_reuseFailAlloc_4409_, 6, v_userNames_4393_);
lean_ctor_set(v_reuseFailAlloc_4409_, 7, v_lAssignment_4394_);
lean_ctor_set(v_reuseFailAlloc_4409_, 8, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4409_, 9, v_dAssignment_4396_);
v___x_4402_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4404_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4402_);
v___x_4404_ = v___x_4385_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_cache_4380_);
lean_ctor_set(v_reuseFailAlloc_4408_, 2, v_zetaDeltaFVarIds_4381_);
lean_ctor_set(v_reuseFailAlloc_4408_, 3, v_postponed_4382_);
lean_ctor_set(v_reuseFailAlloc_4408_, 4, v_diag_4383_);
v___x_4404_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4405_ = lean_st_ref_set(v___y_4376_, v___x_4404_);
v___x_4406_ = lean_box(0);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4412_, lean_object* v_val_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4412_, v_val_4413_, v___y_4414_);
lean_dec(v___y_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4421_, lean_object* v_mv_u2082_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4431_; 
lean_inc(v_mv_u2081_4421_);
v___x_4431_ = l_Lean_MVarId_getDecl(v_mv_u2081_4421_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4433_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref(v___x_4431_);
lean_inc(v_mv_u2082_4422_);
v___x_4433_ = l_Lean_MVarId_getDecl(v_mv_u2082_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v_lctx_4435_; lean_object* v_type_4436_; lean_object* v_lctx_4437_; lean_object* v_type_4438_; uint8_t v___x_4439_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4433_);
v_lctx_4435_ = lean_ctor_get(v_a_4432_, 1);
lean_inc_ref(v_lctx_4435_);
v_type_4436_ = lean_ctor_get(v_a_4432_, 2);
lean_inc_ref(v_type_4436_);
lean_dec(v_a_4432_);
v_lctx_4437_ = lean_ctor_get(v_a_4434_, 1);
lean_inc_ref(v_lctx_4437_);
v_type_4438_ = lean_ctor_get(v_a_4434_, 2);
lean_inc_ref(v_type_4438_);
lean_dec(v_a_4434_);
v___x_4439_ = lean_expr_eqv(v_type_4436_, v_type_4438_);
lean_dec_ref(v_type_4438_);
lean_dec_ref(v_type_4436_);
if (v___x_4439_ == 0)
{
lean_dec_ref(v_lctx_4437_);
lean_dec_ref(v_lctx_4435_);
lean_dec(v_mv_u2082_4422_);
lean_dec(v_mv_u2081_4421_);
goto v___jp_4428_;
}
else
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4441_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4435_, v_lctx_4437_, v___x_4440_);
if (v___x_4441_ == 0)
{
uint8_t v___x_4442_; 
v___x_4442_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4437_, v_lctx_4435_, v___x_4440_);
lean_dec_ref(v_lctx_4435_);
lean_dec_ref(v_lctx_4437_);
if (v___x_4442_ == 0)
{
lean_dec(v_mv_u2082_4422_);
lean_dec(v_mv_u2081_4421_);
goto v___jp_4428_;
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4454_; 
v___x_4443_ = l_Lean_Expr_mvar___override(v_mv_u2082_4422_);
v___x_4444_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4421_, v___x_4443_, v___y_4424_);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; 
v_unused_4455_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4455_);
v___x_4446_ = v___x_4444_;
v_isShared_4447_ = v_isSharedCheck_4454_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v___x_4444_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4454_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4448_ = lean_box(v___x_4441_);
v___x_4449_ = lean_box(v___x_4439_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4448_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 0, v___x_4450_);
v___x_4452_ = v___x_4446_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4468_; 
lean_dec_ref(v_lctx_4437_);
lean_dec_ref(v_lctx_4435_);
v___x_4456_ = l_Lean_Expr_mvar___override(v_mv_u2081_4421_);
v___x_4457_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4422_, v___x_4456_, v___y_4424_);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v___x_4457_, 0);
lean_dec(v_unused_4469_);
v___x_4459_ = v___x_4457_;
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
else
{
lean_dec(v___x_4457_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
uint8_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4461_ = 0;
v___x_4462_ = lean_box(v___x_4439_);
v___x_4463_ = lean_box(v___x_4461_);
v___x_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4462_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4464_);
v___x_4466_ = v___x_4459_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_a_4432_);
lean_dec(v_mv_u2082_4422_);
lean_dec(v_mv_u2081_4421_);
v_a_4470_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4433_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4433_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec(v_mv_u2082_4422_);
lean_dec(v_mv_u2081_4421_);
v_a_4478_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4431_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4431_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
v___jp_4428_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4486_, lean_object* v_mv_u2082_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4486_, v_mv_u2082_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4494_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4508_, lean_object* v_removed_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_b_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___y_4519_; uint8_t v___x_4542_; 
v___x_4542_ = lean_nat_dec_lt(v_a_4511_, v_upperBound_4508_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
lean_dec(v_a_4511_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_b_4512_);
return v___x_4543_;
}
else
{
uint8_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
v___x_4544_ = 0;
v___x_4545_ = lean_box(v___x_4544_);
v___x_4546_ = lean_array_get(v___x_4545_, v_removed_4509_, v_a_4511_);
lean_dec(v___x_4545_);
v___x_4547_ = lean_unbox(v___x_4546_);
lean_dec(v___x_4546_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___f_4551_; 
v___x_4548_ = lean_array_fget_borrowed(v_a_4510_, v_a_4511_);
lean_inc(v___x_4548_);
v___x_4549_ = lean_array_push(v_b_4512_, v___x_4548_);
v___x_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
v___f_4551_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4551_, 0, v___x_4550_);
v___y_4519_ = v___f_4551_;
goto v___jp_4518_;
}
else
{
lean_object* v___x_4552_; lean_object* v___f_4553_; 
v___x_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_b_4512_);
v___f_4553_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4553_, 0, v___x_4552_);
v___y_4519_ = v___f_4553_;
goto v___jp_4518_;
}
}
v___jp_4518_:
{
lean_object* v___x_4520_; 
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
lean_inc(v___y_4514_);
lean_inc_ref(v___y_4513_);
v___x_4520_ = lean_apply_5(v___y_4519_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, lean_box(0));
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4533_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4533_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4533_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
if (lean_obj_tag(v_a_4521_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; 
lean_dec(v_a_4511_);
v_a_4525_ = lean_ctor_get(v_a_4521_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v_a_4521_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v_a_4525_);
v___x_4527_ = v___x_4523_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_del_object(v___x_4523_);
v_a_4529_ = lean_ctor_get(v_a_4521_, 0);
lean_inc(v_a_4529_);
lean_dec_ref(v_a_4521_);
v___x_4530_ = lean_unsigned_to_nat(1u);
v___x_4531_ = lean_nat_add(v_a_4511_, v___x_4530_);
lean_dec(v_a_4511_);
v_a_4511_ = v___x_4531_;
v_b_4512_ = v_a_4529_;
goto _start;
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec(v_a_4511_);
v_a_4534_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4520_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4520_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4554_, lean_object* v_removed_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4554_, v_removed_4555_, v_a_4556_, v_a_4557_, v_b_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v_a_4556_);
lean_dec_ref(v_removed_4555_);
lean_dec(v_upperBound_4554_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4565_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4579_, lean_object* v___x_4580_, lean_object* v___x_4581_, lean_object* v___x_4582_, lean_object* v_a_4583_, uint8_t v___x_4584_, lean_object* v_snd_4585_, lean_object* v_fst_4586_, lean_object* v_next_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_apply_7(v_f_4579_, v___x_4580_, v___x_4581_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, lean_box(0));
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4629_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4596_ = v___x_4593_;
v_isShared_4597_ = v_isSharedCheck_4629_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4593_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4629_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v_fst_4598_; lean_object* v_snd_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4628_; 
v_fst_4598_ = lean_ctor_get(v_a_4594_, 0);
v_snd_4599_ = lean_ctor_get(v_a_4594_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_a_4594_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4601_ = v_a_4594_;
v_isShared_4602_ = v_isSharedCheck_4628_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_snd_4599_);
lean_inc(v_fst_4598_);
lean_dec(v_a_4594_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4628_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v_removed_4604_; lean_object* v_numRemoved_4605_; uint8_t v___x_4624_; 
v___x_4624_ = lean_unbox(v_fst_4598_);
lean_dec(v_fst_4598_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = lean_nat_add(v_snd_4585_, v___x_4582_);
lean_dec(v_snd_4585_);
v___x_4626_ = lean_box(v___x_4584_);
v___x_4627_ = lean_array_set(v_fst_4586_, v_next_4587_, v___x_4626_);
v_removed_4604_ = v___x_4627_;
v_numRemoved_4605_ = v___x_4625_;
goto v___jp_4603_;
}
else
{
v_removed_4604_ = v_fst_4586_;
v_numRemoved_4605_ = v_snd_4585_;
goto v___jp_4603_;
}
v___jp_4603_:
{
uint8_t v___x_4606_; 
v___x_4606_ = lean_unbox(v_snd_4599_);
lean_dec(v_snd_4599_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4607_ = lean_nat_add(v_numRemoved_4605_, v___x_4582_);
lean_dec(v_numRemoved_4605_);
v___x_4608_ = lean_box(v___x_4584_);
v___x_4609_ = lean_array_set(v_removed_4604_, v_a_4583_, v___x_4608_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 1, v___x_4607_);
lean_ctor_set(v___x_4601_, 0, v___x_4609_);
v___x_4611_ = v___x_4601_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v___x_4607_);
v___x_4611_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; lean_object* v___x_4614_; 
v___x_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4612_);
v___x_4614_ = v___x_4596_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
else
{
lean_object* v___x_4618_; 
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 1, v_numRemoved_4605_);
lean_ctor_set(v___x_4601_, 0, v_removed_4604_);
v___x_4618_ = v___x_4601_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_removed_4604_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_numRemoved_4605_);
v___x_4618_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4619_);
v___x_4621_ = v___x_4596_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec(v_fst_4586_);
lean_dec(v_snd_4585_);
v_a_4630_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4593_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4593_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
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
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4638_, lean_object* v___x_4639_, lean_object* v___x_4640_, lean_object* v___x_4641_, lean_object* v_a_4642_, lean_object* v___x_4643_, lean_object* v_snd_4644_, lean_object* v_fst_4645_, lean_object* v_next_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
uint8_t v___x_4754__boxed_4652_; lean_object* v_res_4653_; 
v___x_4754__boxed_4652_ = lean_unbox(v___x_4643_);
v_res_4653_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4638_, v___x_4639_, v___x_4640_, v___x_4641_, v_a_4642_, v___x_4754__boxed_4652_, v_snd_4644_, v_fst_4645_, v_next_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v_next_4646_);
lean_dec(v_a_4642_);
lean_dec(v___x_4641_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4654_, lean_object* v_a_4655_, lean_object* v_next_4656_, lean_object* v_f_4657_, lean_object* v_a_4658_, lean_object* v_b_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
uint8_t v___x_4665_; 
v___x_4665_ = lean_nat_dec_lt(v_a_4658_, v_upperBound_4654_);
if (v___x_4665_ == 0)
{
lean_object* v___x_4666_; 
lean_dec(v_a_4658_);
lean_dec_ref(v_f_4657_);
lean_dec(v_next_4656_);
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_b_4659_);
return v___x_4666_;
}
else
{
lean_object* v_fst_4667_; lean_object* v_snd_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4715_; 
v_fst_4667_ = lean_ctor_get(v_b_4659_, 0);
v_snd_4668_ = lean_ctor_get(v_b_4659_, 1);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_b_4659_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4670_ = v_b_4659_;
v_isShared_4671_ = v_isSharedCheck_4715_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_snd_4668_);
lean_inc(v_fst_4667_);
lean_dec(v_b_4659_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4715_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v___y_4674_; uint8_t v___y_4697_; uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; 
v___x_4672_ = lean_unsigned_to_nat(1u);
v___x_4707_ = 0;
v___x_4708_ = lean_box(v___x_4707_);
v___x_4709_ = lean_array_get(v___x_4708_, v_fst_4667_, v_next_4656_);
lean_dec(v___x_4708_);
v___x_4710_ = lean_unbox(v___x_4709_);
if (v___x_4710_ == 0)
{
lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
lean_dec(v___x_4709_);
v___x_4711_ = lean_box(v___x_4707_);
v___x_4712_ = lean_array_get(v___x_4711_, v_fst_4667_, v_a_4658_);
lean_dec(v___x_4711_);
v___x_4713_ = lean_unbox(v___x_4712_);
lean_dec(v___x_4712_);
v___y_4697_ = v___x_4713_;
goto v___jp_4696_;
}
else
{
uint8_t v___x_4714_; 
v___x_4714_ = lean_unbox(v___x_4709_);
lean_dec(v___x_4709_);
v___y_4697_ = v___x_4714_;
goto v___jp_4696_;
}
v___jp_4673_:
{
lean_object* v___x_4675_; 
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
v___x_4675_ = lean_apply_5(v___y_4674_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4687_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4687_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4687_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
if (lean_obj_tag(v_a_4676_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; 
lean_dec(v_a_4658_);
lean_dec_ref(v_f_4657_);
lean_dec(v_next_4656_);
v_a_4680_ = lean_ctor_get(v_a_4676_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v_a_4676_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v_a_4680_);
v___x_4682_ = v___x_4678_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4685_; 
lean_del_object(v___x_4678_);
v_a_4684_ = lean_ctor_get(v_a_4676_, 0);
lean_inc(v_a_4684_);
lean_dec_ref(v_a_4676_);
v___x_4685_ = lean_nat_add(v_a_4658_, v___x_4672_);
lean_dec(v_a_4658_);
v_a_4658_ = v___x_4685_;
v_b_4659_ = v_a_4684_;
goto _start;
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_dec(v_a_4658_);
lean_dec_ref(v_f_4657_);
lean_dec(v_next_4656_);
v_a_4688_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4675_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4675_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
v___jp_4696_:
{
if (v___y_4697_ == 0)
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___f_4701_; 
lean_del_object(v___x_4670_);
v___x_4698_ = lean_array_fget_borrowed(v_a_4655_, v_next_4656_);
v___x_4699_ = lean_array_fget_borrowed(v_a_4655_, v_a_4658_);
v___x_4700_ = lean_box(v___x_4665_);
lean_inc(v_next_4656_);
lean_inc(v_a_4658_);
lean_inc(v___x_4699_);
lean_inc(v___x_4698_);
lean_inc_ref(v_f_4657_);
v___f_4701_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4701_, 0, v_f_4657_);
lean_closure_set(v___f_4701_, 1, v___x_4698_);
lean_closure_set(v___f_4701_, 2, v___x_4699_);
lean_closure_set(v___f_4701_, 3, v___x_4672_);
lean_closure_set(v___f_4701_, 4, v_a_4658_);
lean_closure_set(v___f_4701_, 5, v___x_4700_);
lean_closure_set(v___f_4701_, 6, v_snd_4668_);
lean_closure_set(v___f_4701_, 7, v_fst_4667_);
lean_closure_set(v___f_4701_, 8, v_next_4656_);
v___y_4674_ = v___f_4701_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4703_; 
if (v_isShared_4671_ == 0)
{
v___x_4703_ = v___x_4670_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_fst_4667_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_snd_4668_);
v___x_4703_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; lean_object* v___f_4705_; 
v___x_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
v___f_4705_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4705_, 0, v___x_4704_);
v___y_4674_ = v___f_4705_;
goto v___jp_4673_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4716_, lean_object* v_a_4717_, lean_object* v_next_4718_, lean_object* v_f_4719_, lean_object* v_a_4720_, lean_object* v_b_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4716_, v_a_4717_, v_next_4718_, v_f_4719_, v_a_4720_, v_b_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec_ref(v_a_4717_);
lean_dec(v_upperBound_4716_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4728_, lean_object* v___x_4729_, lean_object* v_a_4730_, lean_object* v_f_4731_, lean_object* v_a_4732_, lean_object* v_b_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v___x_4739_; 
v___x_4739_ = lean_nat_dec_lt(v_a_4732_, v_upperBound_4728_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; 
lean_dec(v_a_4732_);
lean_dec_ref(v_f_4731_);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v_b_4733_);
return v___x_4740_;
}
else
{
lean_object* v_fst_4741_; lean_object* v_snd_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4763_; 
v_fst_4741_ = lean_ctor_get(v_b_4733_, 0);
v_snd_4742_ = lean_ctor_get(v_b_4733_, 1);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_b_4733_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4744_ = v_b_4733_;
v_isShared_4745_ = v_isSharedCheck_4763_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_snd_4742_);
lean_inc(v_fst_4741_);
lean_dec(v_b_4733_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4763_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4746_ = lean_unsigned_to_nat(1u);
v___x_4747_ = lean_nat_add(v_a_4732_, v___x_4746_);
if (v_isShared_4745_ == 0)
{
v___x_4749_ = v___x_4744_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_fst_4741_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_snd_4742_);
v___x_4749_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; 
lean_inc(v___x_4747_);
lean_inc_ref(v_f_4731_);
v___x_4750_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4729_, v_a_4730_, v_a_4732_, v_f_4731_, v___x_4747_, v___x_4749_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v_fst_4752_; lean_object* v_snd_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4761_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
lean_inc(v_a_4751_);
lean_dec_ref(v___x_4750_);
v_fst_4752_ = lean_ctor_get(v_a_4751_, 0);
v_snd_4753_ = lean_ctor_get(v_a_4751_, 1);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_a_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4755_ = v_a_4751_;
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_snd_4753_);
lean_inc(v_fst_4752_);
lean_dec(v_a_4751_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_fst_4752_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_snd_4753_);
v___x_4758_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
v_a_4732_ = v___x_4747_;
v_b_4733_ = v___x_4758_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4747_);
lean_dec_ref(v_f_4731_);
return v___x_4750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4764_, lean_object* v___x_4765_, lean_object* v_a_4766_, lean_object* v_f_4767_, lean_object* v_a_4768_, lean_object* v_b_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4764_, v___x_4765_, v_a_4766_, v_f_4767_, v_a_4768_, v_b_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec_ref(v_a_4766_);
lean_dec(v___x_4765_);
lean_dec(v_upperBound_4764_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4776_, lean_object* v_f_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v___x_4783_; uint8_t v___x_4784_; lean_object* v___x_4785_; lean_object* v_removed_4786_; lean_object* v_numRemoved_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4783_ = lean_array_get_size(v_a_4776_);
v___x_4784_ = 0;
v___x_4785_ = lean_box(v___x_4784_);
v_removed_4786_ = lean_mk_array(v___x_4783_, v___x_4785_);
v_numRemoved_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4788_, 0, v_removed_4786_);
lean_ctor_set(v___x_4788_, 1, v_numRemoved_4787_);
v___x_4789_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4783_, v___x_4783_, v_a_4776_, v_f_4777_, v_numRemoved_4787_, v___x_4788_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v_fst_4791_; lean_object* v_snd_4792_; lean_object* v_a_x27_4793_; lean_object* v___x_4794_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4789_);
v_fst_4791_ = lean_ctor_get(v_a_4790_, 0);
lean_inc(v_fst_4791_);
v_snd_4792_ = lean_ctor_get(v_a_4790_, 1);
lean_inc(v_snd_4792_);
lean_dec(v_a_4790_);
v_a_x27_4793_ = lean_mk_empty_array_with_capacity(v_snd_4792_);
lean_dec(v_snd_4792_);
v___x_4794_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4783_, v_fst_4791_, v_a_4776_, v_numRemoved_4787_, v_a_x27_4793_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v_fst_4791_);
return v___x_4794_;
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v_a_4795_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4789_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4789_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4803_, lean_object* v_f_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4803_, v_f_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec_ref(v_a_4803_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_){
_start:
{
lean_object* v___f_4818_; lean_object* v___x_4819_; 
v___f_4818_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4819_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4812_, v___f_4818_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec_ref(v_a_4821_);
lean_dec_ref(v_mvars_4820_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4827_, lean_object* v_val_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4827_, v_val_4828_, v___y_4830_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4835_, lean_object* v_val_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4835_, v_val_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4843_, lean_object* v_a_4844_, lean_object* v_f_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4844_, v_f_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4852_, lean_object* v_a_4853_, lean_object* v_f_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4852_, v_a_4853_, v_f_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec_ref(v_a_4853_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4861_, lean_object* v_x_4862_, lean_object* v_x_4863_, lean_object* v_x_4864_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4862_, v_x_4863_, v_x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4866_, lean_object* v_00_u03b1_4867_, lean_object* v_a_4868_, lean_object* v_next_4869_, lean_object* v_f_4870_, lean_object* v_inst_4871_, lean_object* v_R_4872_, lean_object* v_a_4873_, lean_object* v_b_4874_, lean_object* v_c_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4866_, v_a_4868_, v_next_4869_, v_f_4870_, v_a_4873_, v_b_4874_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4882_, lean_object* v_00_u03b1_4883_, lean_object* v_a_4884_, lean_object* v_next_4885_, lean_object* v_f_4886_, lean_object* v_inst_4887_, lean_object* v_R_4888_, lean_object* v_a_4889_, lean_object* v_b_4890_, lean_object* v_c_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4882_, v_00_u03b1_4883_, v_a_4884_, v_next_4885_, v_f_4886_, v_inst_4887_, v_R_4888_, v_a_4889_, v_b_4890_, v_c_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec_ref(v_a_4884_);
lean_dec(v_upperBound_4882_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4898_, lean_object* v_upperBound_4899_, lean_object* v_removed_4900_, lean_object* v_a_4901_, lean_object* v_inst_4902_, lean_object* v_R_4903_, lean_object* v_a_4904_, lean_object* v_b_4905_, lean_object* v_c_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4899_, v_removed_4900_, v_a_4901_, v_a_4904_, v_b_4905_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4913_, lean_object* v_upperBound_4914_, lean_object* v_removed_4915_, lean_object* v_a_4916_, lean_object* v_inst_4917_, lean_object* v_R_4918_, lean_object* v_a_4919_, lean_object* v_b_4920_, lean_object* v_c_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4913_, v_upperBound_4914_, v_removed_4915_, v_a_4916_, v_inst_4917_, v_R_4918_, v_a_4919_, v_b_4920_, v_c_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec_ref(v_a_4916_);
lean_dec_ref(v_removed_4915_);
lean_dec(v_upperBound_4914_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4928_, lean_object* v___x_4929_, lean_object* v_00_u03b1_4930_, lean_object* v_a_4931_, lean_object* v_f_4932_, lean_object* v_inst_4933_, lean_object* v_R_4934_, lean_object* v_a_4935_, lean_object* v_b_4936_, lean_object* v_c_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4928_, v___x_4929_, v_a_4931_, v_f_4932_, v_a_4935_, v_b_4936_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4944_, lean_object* v___x_4945_, lean_object* v_00_u03b1_4946_, lean_object* v_a_4947_, lean_object* v_f_4948_, lean_object* v_inst_4949_, lean_object* v_R_4950_, lean_object* v_a_4951_, lean_object* v_b_4952_, lean_object* v_c_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4944_, v___x_4945_, v_00_u03b1_4946_, v_a_4947_, v_f_4948_, v_inst_4949_, v_R_4950_, v_a_4951_, v_b_4952_, v_c_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v_a_4947_);
lean_dec(v___x_4945_);
lean_dec(v_upperBound_4944_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4960_, lean_object* v_x_4961_, size_t v_x_4962_, size_t v_x_4963_, lean_object* v_x_4964_, lean_object* v_x_4965_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4961_, v_x_4962_, v_x_4963_, v_x_4964_, v_x_4965_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4967_, lean_object* v_x_4968_, lean_object* v_x_4969_, lean_object* v_x_4970_, lean_object* v_x_4971_, lean_object* v_x_4972_){
_start:
{
size_t v_x_5214__boxed_4973_; size_t v_x_5215__boxed_4974_; lean_object* v_res_4975_; 
v_x_5214__boxed_4973_ = lean_unbox_usize(v_x_4969_);
lean_dec(v_x_4969_);
v_x_5215__boxed_4974_ = lean_unbox_usize(v_x_4970_);
lean_dec(v_x_4970_);
v_res_4975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4967_, v_x_4968_, v_x_5214__boxed_4973_, v_x_5215__boxed_4974_, v_x_4971_, v_x_4972_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4976_, lean_object* v_n_4977_, lean_object* v_k_4978_, lean_object* v_v_4979_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4977_, v_k_4978_, v_v_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4981_, size_t v_depth_4982_, lean_object* v_keys_4983_, lean_object* v_vals_4984_, lean_object* v_heq_4985_, lean_object* v_i_4986_, lean_object* v_entries_4987_){
_start:
{
lean_object* v___x_4988_; 
v___x_4988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4982_, v_keys_4983_, v_vals_4984_, v_i_4986_, v_entries_4987_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4989_, lean_object* v_depth_4990_, lean_object* v_keys_4991_, lean_object* v_vals_4992_, lean_object* v_heq_4993_, lean_object* v_i_4994_, lean_object* v_entries_4995_){
_start:
{
size_t v_depth_boxed_4996_; lean_object* v_res_4997_; 
v_depth_boxed_4996_ = lean_unbox_usize(v_depth_4990_);
lean_dec(v_depth_4990_);
v_res_4997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4989_, v_depth_boxed_4996_, v_keys_4991_, v_vals_4992_, v_heq_4993_, v_i_4994_, v_entries_4995_);
lean_dec_ref(v_vals_4992_);
lean_dec_ref(v_keys_4991_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4998_, lean_object* v_x_4999_, lean_object* v_x_5000_, lean_object* v_x_5001_, lean_object* v_x_5002_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4999_, v_x_5000_, v_x_5001_, v_x_5002_);
return v___x_5003_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5006_ = l_Lean_stringToMessageData(v___x_5005_);
return v___x_5006_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5009_ = l_Lean_stringToMessageData(v___x_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5010_, lean_object* v_as_5011_, size_t v_sz_5012_, size_t v_i_5013_, lean_object* v_b_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_a_5021_; uint8_t v___x_5025_; 
v___x_5025_ = lean_usize_dec_lt(v_i_5013_, v_sz_5012_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v_b_5014_);
return v___x_5026_;
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5028_; 
v_a_5027_ = lean_array_uget_borrowed(v_as_5011_, v_i_5013_);
lean_inc(v_a_5027_);
v___x_5028_ = l_Lean_MVarId_getType(v_a_5027_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___x_5028_);
if (lean_obj_tag(v_a_5029_) == 10)
{
lean_object* v_expr_5047_; 
v_expr_5047_ = lean_ctor_get(v_a_5029_, 1);
if (lean_obj_tag(v_expr_5047_) == 5)
{
lean_object* v_arg_5048_; lean_object* v___x_5049_; 
lean_inc_ref(v_expr_5047_);
lean_dec_ref(v_a_5029_);
v_arg_5048_ = lean_ctor_get(v_expr_5047_, 1);
lean_inc_ref_n(v_arg_5048_, 2);
lean_dec_ref(v_expr_5047_);
v___x_5049_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5010_, v_arg_5048_);
if (lean_obj_tag(v___x_5049_) == 1)
{
lean_object* v_val_5050_; lean_object* v_fst_5051_; lean_object* v___x_5052_; uint8_t v___x_5053_; 
lean_dec_ref(v_arg_5048_);
v_val_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_val_5050_);
lean_dec_ref(v___x_5049_);
v_fst_5051_ = lean_ctor_get(v_val_5050_, 0);
lean_inc(v_fst_5051_);
lean_dec(v_val_5050_);
v___x_5052_ = lean_array_get_size(v_b_5014_);
v___x_5053_ = lean_nat_dec_lt(v_fst_5051_, v___x_5052_);
if (v___x_5053_ == 0)
{
lean_dec(v_fst_5051_);
v_a_5021_ = v_b_5014_;
goto v___jp_5020_;
}
else
{
lean_object* v_v_5054_; lean_object* v___x_5055_; lean_object* v_xs_x27_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v_v_5054_ = lean_array_fget(v_b_5014_, v_fst_5051_);
v___x_5055_ = lean_box(0);
v_xs_x27_5056_ = lean_array_fset(v_b_5014_, v_fst_5051_, v___x_5055_);
lean_inc(v_a_5027_);
v___x_5057_ = lean_array_push(v_v_5054_, v_a_5027_);
v___x_5058_ = lean_array_fset(v_xs_x27_5056_, v_fst_5051_, v___x_5057_);
lean_dec(v_fst_5051_);
v_a_5021_ = v___x_5058_;
goto v___jp_5020_;
}
}
else
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_dec(v___x_5049_);
v___x_5059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5060_ = l_Lean_indentExpr(v_arg_5048_);
v___x_5061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5059_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5061_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_dec_ref(v___x_5062_);
v_a_5021_ = v_b_5014_;
goto v___jp_5020_;
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec_ref(v_b_5014_);
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_5062_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
}
else
{
v___y_5031_ = v___y_5015_;
v___y_5032_ = v___y_5016_;
v___y_5033_ = v___y_5017_;
v___y_5034_ = v___y_5018_;
goto v___jp_5030_;
}
}
else
{
v___y_5031_ = v___y_5015_;
v___y_5032_ = v___y_5016_;
v___y_5033_ = v___y_5017_;
v___y_5034_ = v___y_5018_;
goto v___jp_5030_;
}
v___jp_5030_:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5036_ = l_Lean_indentExpr(v_a_5029_);
v___x_5037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5037_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_dec_ref(v___x_5038_);
v_a_5021_ = v_b_5014_;
goto v___jp_5020_;
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec_ref(v_b_5014_);
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5038_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5038_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec_ref(v_b_5014_);
v_a_5071_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5028_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5028_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
v___jp_5020_:
{
size_t v___x_5022_; size_t v___x_5023_; 
v___x_5022_ = ((size_t)1ULL);
v___x_5023_ = lean_usize_add(v_i_5013_, v___x_5022_);
v_i_5013_ = v___x_5023_;
v_b_5014_ = v_a_5021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5079_, lean_object* v_as_5080_, lean_object* v_sz_5081_, lean_object* v_i_5082_, lean_object* v_b_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
size_t v_sz_boxed_5089_; size_t v_i_boxed_5090_; lean_object* v_res_5091_; 
v_sz_boxed_5089_ = lean_unbox_usize(v_sz_5081_);
lean_dec(v_sz_5081_);
v_i_boxed_5090_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_res_5091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5079_, v_as_5080_, v_sz_boxed_5089_, v_i_boxed_5090_, v_b_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec_ref(v_as_5080_);
lean_dec_ref(v_argsPacker_5079_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5092_, lean_object* v_numFuncs_5093_, lean_object* v_goals_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_){
_start:
{
lean_object* v___x_5100_; lean_object* v_r_5101_; size_t v_sz_5102_; size_t v___x_5103_; lean_object* v___x_5104_; 
v___x_5100_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5101_ = lean_mk_array(v_numFuncs_5093_, v___x_5100_);
v_sz_5102_ = lean_array_size(v_goals_5094_);
v___x_5103_ = ((size_t)0ULL);
v___x_5104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5092_, v_goals_5094_, v_sz_5102_, v___x_5103_, v_r_5101_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5105_, lean_object* v_numFuncs_5106_, lean_object* v_goals_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5105_, v_numFuncs_5106_, v_goals_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec_ref(v_goals_5107_);
lean_dec_ref(v_argsPacker_5105_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v___x_5117_; lean_object* v_infoState_5118_; uint8_t v_enabled_5119_; 
v___x_5117_ = lean_st_ref_get(v___y_5115_);
v_infoState_5118_ = lean_ctor_get(v___x_5117_, 7);
lean_inc_ref(v_infoState_5118_);
lean_dec(v___x_5117_);
v_enabled_5119_ = lean_ctor_get_uint8(v_infoState_5118_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5118_);
if (v_enabled_5119_ == 0)
{
lean_object* v___x_5120_; lean_object* v___x_5121_; 
lean_dec_ref(v_t_5114_);
v___x_5120_ = lean_box(0);
v___x_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5120_);
return v___x_5121_;
}
else
{
lean_object* v___x_5122_; lean_object* v_infoState_5123_; lean_object* v_env_5124_; lean_object* v_nextMacroScope_5125_; lean_object* v_ngen_5126_; lean_object* v_auxDeclNGen_5127_; lean_object* v_traceState_5128_; lean_object* v_cache_5129_; lean_object* v_messages_5130_; lean_object* v_snapshotTasks_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5153_; 
v___x_5122_ = lean_st_ref_take(v___y_5115_);
v_infoState_5123_ = lean_ctor_get(v___x_5122_, 7);
v_env_5124_ = lean_ctor_get(v___x_5122_, 0);
v_nextMacroScope_5125_ = lean_ctor_get(v___x_5122_, 1);
v_ngen_5126_ = lean_ctor_get(v___x_5122_, 2);
v_auxDeclNGen_5127_ = lean_ctor_get(v___x_5122_, 3);
v_traceState_5128_ = lean_ctor_get(v___x_5122_, 4);
v_cache_5129_ = lean_ctor_get(v___x_5122_, 5);
v_messages_5130_ = lean_ctor_get(v___x_5122_, 6);
v_snapshotTasks_5131_ = lean_ctor_get(v___x_5122_, 8);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5133_ = v___x_5122_;
v_isShared_5134_ = v_isSharedCheck_5153_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_snapshotTasks_5131_);
lean_inc(v_infoState_5123_);
lean_inc(v_messages_5130_);
lean_inc(v_cache_5129_);
lean_inc(v_traceState_5128_);
lean_inc(v_auxDeclNGen_5127_);
lean_inc(v_ngen_5126_);
lean_inc(v_nextMacroScope_5125_);
lean_inc(v_env_5124_);
lean_dec(v___x_5122_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5153_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
uint8_t v_enabled_5135_; lean_object* v_assignment_5136_; lean_object* v_lazyAssignment_5137_; lean_object* v_trees_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5152_; 
v_enabled_5135_ = lean_ctor_get_uint8(v_infoState_5123_, sizeof(void*)*3);
v_assignment_5136_ = lean_ctor_get(v_infoState_5123_, 0);
v_lazyAssignment_5137_ = lean_ctor_get(v_infoState_5123_, 1);
v_trees_5138_ = lean_ctor_get(v_infoState_5123_, 2);
v_isSharedCheck_5152_ = !lean_is_exclusive(v_infoState_5123_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5140_ = v_infoState_5123_;
v_isShared_5141_ = v_isSharedCheck_5152_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_trees_5138_);
lean_inc(v_lazyAssignment_5137_);
lean_inc(v_assignment_5136_);
lean_dec(v_infoState_5123_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5152_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5142_; lean_object* v___x_5144_; 
v___x_5142_ = l_Lean_PersistentArray_push___redArg(v_trees_5138_, v_t_5114_);
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 2, v___x_5142_);
v___x_5144_ = v___x_5140_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_assignment_5136_);
lean_ctor_set(v_reuseFailAlloc_5151_, 1, v_lazyAssignment_5137_);
lean_ctor_set(v_reuseFailAlloc_5151_, 2, v___x_5142_);
lean_ctor_set_uint8(v_reuseFailAlloc_5151_, sizeof(void*)*3, v_enabled_5135_);
v___x_5144_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5146_; 
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 7, v___x_5144_);
v___x_5146_ = v___x_5133_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_env_5124_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_nextMacroScope_5125_);
lean_ctor_set(v_reuseFailAlloc_5150_, 2, v_ngen_5126_);
lean_ctor_set(v_reuseFailAlloc_5150_, 3, v_auxDeclNGen_5127_);
lean_ctor_set(v_reuseFailAlloc_5150_, 4, v_traceState_5128_);
lean_ctor_set(v_reuseFailAlloc_5150_, 5, v_cache_5129_);
lean_ctor_set(v_reuseFailAlloc_5150_, 6, v_messages_5130_);
lean_ctor_set(v_reuseFailAlloc_5150_, 7, v___x_5144_);
lean_ctor_set(v_reuseFailAlloc_5150_, 8, v_snapshotTasks_5131_);
v___x_5146_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5147_ = lean_st_ref_set(v___y_5115_, v___x_5146_);
v___x_5148_ = lean_box(0);
v___x_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5149_, 0, v___x_5148_);
return v___x_5149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5154_, v___y_5155_);
lean_dec(v___y_5155_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5158_, v___y_5164_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5176_, lean_object* v___y_5177_){
_start:
{
uint8_t v___x_5179_; 
v___x_5179_ = l_Lean_Expr_hasMVar(v_e_5176_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; 
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v_e_5176_);
return v___x_5180_;
}
else
{
lean_object* v___x_5181_; lean_object* v_mctx_5182_; lean_object* v___x_5183_; lean_object* v_fst_5184_; lean_object* v_snd_5185_; lean_object* v___x_5186_; lean_object* v_cache_5187_; lean_object* v_zetaDeltaFVarIds_5188_; lean_object* v_postponed_5189_; lean_object* v_diag_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5199_; 
v___x_5181_ = lean_st_ref_get(v___y_5177_);
v_mctx_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc_ref(v_mctx_5182_);
lean_dec(v___x_5181_);
v___x_5183_ = l_Lean_instantiateMVarsCore(v_mctx_5182_, v_e_5176_);
v_fst_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_fst_5184_);
v_snd_5185_ = lean_ctor_get(v___x_5183_, 1);
lean_inc(v_snd_5185_);
lean_dec_ref(v___x_5183_);
v___x_5186_ = lean_st_ref_take(v___y_5177_);
v_cache_5187_ = lean_ctor_get(v___x_5186_, 1);
v_zetaDeltaFVarIds_5188_ = lean_ctor_get(v___x_5186_, 2);
v_postponed_5189_ = lean_ctor_get(v___x_5186_, 3);
v_diag_5190_ = lean_ctor_get(v___x_5186_, 4);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5199_ == 0)
{
lean_object* v_unused_5200_; 
v_unused_5200_ = lean_ctor_get(v___x_5186_, 0);
lean_dec(v_unused_5200_);
v___x_5192_ = v___x_5186_;
v_isShared_5193_ = v_isSharedCheck_5199_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_diag_5190_);
lean_inc(v_postponed_5189_);
lean_inc(v_zetaDeltaFVarIds_5188_);
lean_inc(v_cache_5187_);
lean_dec(v___x_5186_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5199_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
lean_ctor_set(v___x_5192_, 0, v_snd_5185_);
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_snd_5185_);
lean_ctor_set(v_reuseFailAlloc_5198_, 1, v_cache_5187_);
lean_ctor_set(v_reuseFailAlloc_5198_, 2, v_zetaDeltaFVarIds_5188_);
lean_ctor_set(v_reuseFailAlloc_5198_, 3, v_postponed_5189_);
lean_ctor_set(v_reuseFailAlloc_5198_, 4, v_diag_5190_);
v___x_5195_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = lean_st_ref_set(v___y_5177_, v___x_5195_);
v___x_5197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5197_, 0, v_fst_5184_);
return v___x_5197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5201_, v___y_5202_);
lean_dec(v___y_5202_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5205_, v___y_5207_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5219_, size_t v_i_5220_, size_t v_stop_5221_, lean_object* v_b_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
uint8_t v___x_5230_; 
v___x_5230_ = lean_usize_dec_eq(v_i_5220_, v_stop_5221_);
if (v___x_5230_ == 0)
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
v___x_5231_ = lean_array_uget_borrowed(v_as_5219_, v_i_5220_);
lean_inc(v___x_5231_);
v___x_5232_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
v___x_5233_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5232_, v___y_5228_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; size_t v___x_5235_; size_t v___x_5236_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_a_5234_);
lean_dec_ref(v___x_5233_);
v___x_5235_ = ((size_t)1ULL);
v___x_5236_ = lean_usize_add(v_i_5220_, v___x_5235_);
v_i_5220_ = v___x_5236_;
v_b_5222_ = v_a_5234_;
goto _start;
}
else
{
return v___x_5233_;
}
}
else
{
lean_object* v___x_5238_; 
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v_b_5222_);
return v___x_5238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5239_, lean_object* v_i_5240_, lean_object* v_stop_5241_, lean_object* v_b_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
size_t v_i_boxed_5250_; size_t v_stop_boxed_5251_; lean_object* v_res_5252_; 
v_i_boxed_5250_ = lean_unbox_usize(v_i_5240_);
lean_dec(v_i_5240_);
v_stop_boxed_5251_ = lean_unbox_usize(v_stop_5241_);
lean_dec(v_stop_5241_);
v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5239_, v_i_boxed_5250_, v_stop_boxed_5251_, v_b_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec_ref(v_as_5239_);
return v_res_5252_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5253_ = lean_unsigned_to_nat(32u);
v___x_5254_ = lean_mk_empty_array_with_capacity(v___x_5253_);
v___x_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5254_);
return v___x_5255_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5256_ = ((size_t)5ULL);
v___x_5257_ = lean_unsigned_to_nat(0u);
v___x_5258_ = lean_unsigned_to_nat(32u);
v___x_5259_ = lean_mk_empty_array_with_capacity(v___x_5258_);
v___x_5260_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5261_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v___x_5259_);
lean_ctor_set(v___x_5261_, 2, v___x_5257_);
lean_ctor_set(v___x_5261_, 3, v___x_5257_);
lean_ctor_set_usize(v___x_5261_, 4, v___x_5256_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5262_){
_start:
{
lean_object* v___x_5264_; lean_object* v_infoState_5265_; lean_object* v_trees_5266_; lean_object* v___x_5267_; lean_object* v_infoState_5268_; lean_object* v_env_5269_; lean_object* v_nextMacroScope_5270_; lean_object* v_ngen_5271_; lean_object* v_auxDeclNGen_5272_; lean_object* v_traceState_5273_; lean_object* v_cache_5274_; lean_object* v_messages_5275_; lean_object* v_snapshotTasks_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5297_; 
v___x_5264_ = lean_st_ref_get(v___y_5262_);
v_infoState_5265_ = lean_ctor_get(v___x_5264_, 7);
lean_inc_ref(v_infoState_5265_);
lean_dec(v___x_5264_);
v_trees_5266_ = lean_ctor_get(v_infoState_5265_, 2);
lean_inc_ref(v_trees_5266_);
lean_dec_ref(v_infoState_5265_);
v___x_5267_ = lean_st_ref_take(v___y_5262_);
v_infoState_5268_ = lean_ctor_get(v___x_5267_, 7);
v_env_5269_ = lean_ctor_get(v___x_5267_, 0);
v_nextMacroScope_5270_ = lean_ctor_get(v___x_5267_, 1);
v_ngen_5271_ = lean_ctor_get(v___x_5267_, 2);
v_auxDeclNGen_5272_ = lean_ctor_get(v___x_5267_, 3);
v_traceState_5273_ = lean_ctor_get(v___x_5267_, 4);
v_cache_5274_ = lean_ctor_get(v___x_5267_, 5);
v_messages_5275_ = lean_ctor_get(v___x_5267_, 6);
v_snapshotTasks_5276_ = lean_ctor_get(v___x_5267_, 8);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5267_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5278_ = v___x_5267_;
v_isShared_5279_ = v_isSharedCheck_5297_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_snapshotTasks_5276_);
lean_inc(v_infoState_5268_);
lean_inc(v_messages_5275_);
lean_inc(v_cache_5274_);
lean_inc(v_traceState_5273_);
lean_inc(v_auxDeclNGen_5272_);
lean_inc(v_ngen_5271_);
lean_inc(v_nextMacroScope_5270_);
lean_inc(v_env_5269_);
lean_dec(v___x_5267_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5297_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
uint8_t v_enabled_5280_; lean_object* v_assignment_5281_; lean_object* v_lazyAssignment_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5295_; 
v_enabled_5280_ = lean_ctor_get_uint8(v_infoState_5268_, sizeof(void*)*3);
v_assignment_5281_ = lean_ctor_get(v_infoState_5268_, 0);
v_lazyAssignment_5282_ = lean_ctor_get(v_infoState_5268_, 1);
v_isSharedCheck_5295_ = !lean_is_exclusive(v_infoState_5268_);
if (v_isSharedCheck_5295_ == 0)
{
lean_object* v_unused_5296_; 
v_unused_5296_ = lean_ctor_get(v_infoState_5268_, 2);
lean_dec(v_unused_5296_);
v___x_5284_ = v_infoState_5268_;
v_isShared_5285_ = v_isSharedCheck_5295_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_lazyAssignment_5282_);
lean_inc(v_assignment_5281_);
lean_dec(v_infoState_5268_);
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
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_env_5269_);
lean_ctor_set(v_reuseFailAlloc_5293_, 1, v_nextMacroScope_5270_);
lean_ctor_set(v_reuseFailAlloc_5293_, 2, v_ngen_5271_);
lean_ctor_set(v_reuseFailAlloc_5293_, 3, v_auxDeclNGen_5272_);
lean_ctor_set(v_reuseFailAlloc_5293_, 4, v_traceState_5273_);
lean_ctor_set(v_reuseFailAlloc_5293_, 5, v_cache_5274_);
lean_ctor_set(v_reuseFailAlloc_5293_, 6, v_messages_5275_);
lean_ctor_set(v_reuseFailAlloc_5293_, 7, v___x_5288_);
lean_ctor_set(v_reuseFailAlloc_5293_, 8, v_snapshotTasks_5276_);
v___x_5290_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5291_ = lean_st_ref_set(v___y_5262_, v___x_5290_);
v___x_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5292_, 0, v_trees_5266_);
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
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5355_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5319_ = v___x_5316_;
v_isShared_5320_ = v_isSharedCheck_5355_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5355_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v_infoState_5322_; lean_object* v_env_5323_; lean_object* v_nextMacroScope_5324_; lean_object* v_ngen_5325_; lean_object* v_auxDeclNGen_5326_; lean_object* v_traceState_5327_; lean_object* v_cache_5328_; lean_object* v_messages_5329_; lean_object* v_snapshotTasks_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5354_; 
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
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5332_ = v___x_5321_;
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
else
{
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
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
uint8_t v_enabled_5334_; lean_object* v_assignment_5335_; lean_object* v_lazyAssignment_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5352_; 
v_enabled_5334_ = lean_ctor_get_uint8(v_infoState_5322_, sizeof(void*)*3);
v_assignment_5335_ = lean_ctor_get(v_infoState_5322_, 0);
v_lazyAssignment_5336_ = lean_ctor_get(v_infoState_5322_, 1);
v_isSharedCheck_5352_ = !lean_is_exclusive(v_infoState_5322_);
if (v_isSharedCheck_5352_ == 0)
{
lean_object* v_unused_5353_; 
v_unused_5353_ = lean_ctor_get(v_infoState_5322_, 2);
lean_dec(v_unused_5353_);
v___x_5338_ = v_infoState_5322_;
v_isShared_5339_ = v_isSharedCheck_5352_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_lazyAssignment_5336_);
lean_inc(v_assignment_5335_);
lean_dec(v_infoState_5322_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5352_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; lean_object* v___x_5342_; 
v___x_5340_ = l_Lean_PersistentArray_push___redArg(v_a_5310_, v_a_5317_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 2, v___x_5340_);
v___x_5342_ = v___x_5338_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_assignment_5335_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_lazyAssignment_5336_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v___x_5340_);
lean_ctor_set_uint8(v_reuseFailAlloc_5351_, sizeof(void*)*3, v_enabled_5334_);
v___x_5342_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5344_; 
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 7, v___x_5342_);
v___x_5344_ = v___x_5332_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_env_5323_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v_nextMacroScope_5324_);
lean_ctor_set(v_reuseFailAlloc_5350_, 2, v_ngen_5325_);
lean_ctor_set(v_reuseFailAlloc_5350_, 3, v_auxDeclNGen_5326_);
lean_ctor_set(v_reuseFailAlloc_5350_, 4, v_traceState_5327_);
lean_ctor_set(v_reuseFailAlloc_5350_, 5, v_cache_5328_);
lean_ctor_set(v_reuseFailAlloc_5350_, 6, v_messages_5329_);
lean_ctor_set(v_reuseFailAlloc_5350_, 7, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5350_, 8, v_snapshotTasks_5330_);
v___x_5344_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5345_ = lean_st_ref_set(v___y_5301_, v___x_5344_);
v___x_5346_ = lean_box(0);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5346_);
v___x_5348_ = v___x_5319_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
lean_dec_ref(v_a_5310_);
v_a_5356_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5316_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5316_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5364_, lean_object* v_mkInfoTree_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v_a_5373_, lean_object* v_a_x3f_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5364_, v_mkInfoTree_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v_a_5373_, v_a_x3f_5374_);
lean_dec(v_a_x3f_5374_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
lean_dec(v___y_5364_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5377_, lean_object* v_mkInfoTree_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v___x_5388_; lean_object* v_infoState_5389_; uint8_t v_enabled_5390_; 
v___x_5388_ = lean_st_ref_get(v___y_5386_);
v_infoState_5389_ = lean_ctor_get(v___x_5388_, 7);
lean_inc_ref(v_infoState_5389_);
lean_dec(v___x_5388_);
v_enabled_5390_ = lean_ctor_get_uint8(v_infoState_5389_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5389_);
if (v_enabled_5390_ == 0)
{
lean_object* v___x_5391_; 
lean_dec_ref(v_mkInfoTree_5378_);
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
lean_inc(v___y_5384_);
lean_inc_ref(v___y_5383_);
lean_inc(v___y_5382_);
lean_inc_ref(v___y_5381_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
v___x_5391_ = lean_apply_9(v_x_5377_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, lean_box(0));
return v___x_5391_;
}
else
{
lean_object* v___x_5392_; lean_object* v_a_5393_; lean_object* v_r_5394_; 
v___x_5392_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5386_);
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_a_5393_);
lean_dec_ref(v___x_5392_);
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
lean_inc(v___y_5384_);
lean_inc_ref(v___y_5383_);
lean_inc(v___y_5382_);
lean_inc_ref(v___y_5381_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
v_r_5394_ = lean_apply_9(v_x_5377_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, lean_box(0));
if (lean_obj_tag(v_r_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5419_; 
v_a_5395_ = lean_ctor_get(v_r_5394_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v_r_5394_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5397_ = v_r_5394_;
v_isShared_5398_ = v_isSharedCheck_5419_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v_r_5394_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5419_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
lean_inc(v_a_5395_);
if (v_isShared_5398_ == 0)
{
lean_ctor_set_tag(v___x_5397_, 1);
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; 
v___x_5401_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5386_, v_mkInfoTree_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v_a_5393_, v___x_5400_);
lean_dec_ref(v___x_5400_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5408_ == 0)
{
lean_object* v_unused_5409_; 
v_unused_5409_ = lean_ctor_get(v___x_5401_, 0);
lean_dec(v_unused_5409_);
v___x_5403_ = v___x_5401_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_dec(v___x_5401_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 0, v_a_5395_);
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5395_);
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
lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5417_; 
lean_dec(v_a_5395_);
v_a_5410_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5412_ = v___x_5401_;
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5401_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5415_; 
if (v_isShared_5413_ == 0)
{
v___x_5415_ = v___x_5412_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
v_a_5420_ = lean_ctor_get(v_r_5394_, 0);
lean_inc(v_a_5420_);
lean_dec_ref(v_r_5394_);
v___x_5421_ = lean_box(0);
v___x_5422_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5386_, v_mkInfoTree_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v_a_5393_, v___x_5421_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5429_; 
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; 
v_unused_5430_ = lean_ctor_get(v___x_5422_, 0);
lean_dec(v_unused_5430_);
v___x_5424_ = v___x_5422_;
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
else
{
lean_dec(v___x_5422_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
lean_ctor_set_tag(v___x_5424_, 1);
lean_ctor_set(v___x_5424_, 0, v_a_5420_);
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5420_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
return v___x_5427_;
}
}
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
lean_dec(v_a_5420_);
v_a_5431_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5422_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5422_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5439_, lean_object* v_mkInfoTree_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5439_, v_mkInfoTree_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5451_, lean_object* v_trees_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
lean_object* v___x_5462_; 
lean_inc(v___y_5460_);
lean_inc_ref(v___y_5459_);
lean_inc(v___y_5458_);
lean_inc_ref(v___y_5457_);
lean_inc(v___y_5456_);
lean_inc_ref(v___y_5455_);
lean_inc(v___y_5454_);
lean_inc_ref(v___y_5453_);
v___x_5462_ = lean_apply_9(v_a_5451_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, lean_box(0));
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5471_; 
v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5462_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5465_ = v___x_5462_;
v_isShared_5466_ = v_isSharedCheck_5471_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5462_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5471_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___x_5467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5467_, 0, v_a_5463_);
lean_ctor_set(v___x_5467_, 1, v_trees_5452_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 0, v___x_5467_);
v___x_5469_ = v___x_5465_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5467_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
else
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
lean_dec_ref(v_trees_5452_);
v_a_5472_ = lean_ctor_get(v___x_5462_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5462_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___x_5462_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5462_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5480_, lean_object* v_trees_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_){
_start:
{
lean_object* v_res_5491_; 
v_res_5491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5480_, v_trees_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec(v___y_5485_);
lean_dec_ref(v___y_5484_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5492_, lean_object* v_ref_5493_, lean_object* v_tactic_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v___x_5504_; 
v___x_5504_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5492_, v___y_5496_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v___x_5505_; 
lean_dec_ref(v___x_5504_);
v___x_5505_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v___x_5506_; 
lean_dec_ref(v___x_5505_);
v___x_5506_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5493_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v_a_5507_; lean_object* v___f_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
lean_inc(v_a_5507_);
lean_dec_ref(v___x_5506_);
v___f_5508_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5508_, 0, v_a_5507_);
v___x_5509_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5509_, 0, v_tactic_5494_);
v___x_5510_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5509_, v___f_5508_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
return v___x_5510_;
}
else
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
lean_dec(v_tactic_5494_);
v_a_5511_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5506_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5506_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
else
{
lean_dec(v_tactic_5494_);
lean_dec(v_ref_5493_);
return v___x_5505_;
}
}
else
{
lean_dec(v_tactic_5494_);
lean_dec(v_ref_5493_);
return v___x_5504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5519_, lean_object* v_ref_5520_, lean_object* v_tactic_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5519_, v_ref_5520_, v_tactic_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
lean_dec(v___y_5529_);
lean_dec_ref(v___y_5528_);
lean_dec(v___y_5527_);
lean_dec_ref(v___y_5526_);
lean_dec(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
return v_res_5531_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5532_ = lean_box(1);
v___x_5533_ = l_Lean_MessageData_ofFormat(v___x_5532_);
return v___x_5533_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5537_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5538_ = l_Lean_MessageData_ofFormat(v___x_5537_);
return v___x_5538_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5539_, lean_object* v_x_5540_){
_start:
{
if (lean_obj_tag(v_x_5540_) == 0)
{
return v_x_5539_;
}
else
{
lean_object* v_head_5541_; lean_object* v_tail_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5564_; 
v_head_5541_ = lean_ctor_get(v_x_5540_, 0);
v_tail_5542_ = lean_ctor_get(v_x_5540_, 1);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_x_5540_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5544_ = v_x_5540_;
v_isShared_5545_ = v_isSharedCheck_5564_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_tail_5542_);
lean_inc(v_head_5541_);
lean_dec(v_x_5540_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5564_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v_before_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5562_; 
v_before_5546_ = lean_ctor_get(v_head_5541_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v_head_5541_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; 
v_unused_5563_ = lean_ctor_get(v_head_5541_, 1);
lean_dec(v_unused_5563_);
v___x_5548_ = v_head_5541_;
v_isShared_5549_ = v_isSharedCheck_5562_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_before_5546_);
lean_dec(v_head_5541_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5562_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5550_; lean_object* v___x_5552_; 
v___x_5550_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5549_ == 0)
{
lean_ctor_set_tag(v___x_5548_, 7);
lean_ctor_set(v___x_5548_, 1, v___x_5550_);
lean_ctor_set(v___x_5548_, 0, v_x_5539_);
v___x_5552_ = v___x_5548_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_x_5539_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
lean_object* v___x_5553_; lean_object* v___x_5555_; 
v___x_5553_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5545_ == 0)
{
lean_ctor_set_tag(v___x_5544_, 7);
lean_ctor_set(v___x_5544_, 1, v___x_5553_);
lean_ctor_set(v___x_5544_, 0, v___x_5552_);
v___x_5555_ = v___x_5544_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5556_ = l_Lean_MessageData_ofSyntax(v_before_5546_);
v___x_5557_ = l_Lean_indentD(v___x_5556_);
v___x_5558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5555_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v_x_5539_ = v___x_5558_;
v_x_5540_ = v_tail_5542_;
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
lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5568_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5569_ = l_Lean_MessageData_ofFormat(v___x_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5570_, lean_object* v_macroStack_5571_, lean_object* v___y_5572_){
_start:
{
lean_object* v_options_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v_options_5574_ = lean_ctor_get(v___y_5572_, 2);
v___x_5575_ = l_Lean_Elab_pp_macroStack;
v___x_5576_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5574_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; 
lean_dec(v_macroStack_5571_);
v___x_5577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5577_, 0, v_msgData_5570_);
return v___x_5577_;
}
else
{
if (lean_obj_tag(v_macroStack_5571_) == 0)
{
lean_object* v___x_5578_; 
v___x_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5578_, 0, v_msgData_5570_);
return v___x_5578_;
}
else
{
lean_object* v_head_5579_; lean_object* v_after_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5595_; 
v_head_5579_ = lean_ctor_get(v_macroStack_5571_, 0);
lean_inc(v_head_5579_);
v_after_5580_ = lean_ctor_get(v_head_5579_, 1);
v_isSharedCheck_5595_ = !lean_is_exclusive(v_head_5579_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v_head_5579_, 0);
lean_dec(v_unused_5596_);
v___x_5582_ = v_head_5579_;
v_isShared_5583_ = v_isSharedCheck_5595_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_after_5580_);
lean_dec(v_head_5579_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5595_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5584_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5583_ == 0)
{
lean_ctor_set_tag(v___x_5582_, 7);
lean_ctor_set(v___x_5582_, 1, v___x_5584_);
lean_ctor_set(v___x_5582_, 0, v_msgData_5570_);
v___x_5586_ = v___x_5582_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_msgData_5570_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v___x_5584_);
v___x_5586_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v_msgData_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5587_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = l_Lean_MessageData_ofSyntax(v_after_5580_);
v___x_5590_ = l_Lean_indentD(v___x_5589_);
v_msgData_5591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5591_, 0, v___x_5588_);
lean_ctor_set(v_msgData_5591_, 1, v___x_5590_);
v___x_5592_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5591_, v_macroStack_5571_);
v___x_5593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5593_, 0, v___x_5592_);
return v___x_5593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5597_, lean_object* v_macroStack_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_){
_start:
{
lean_object* v_res_5601_; 
v_res_5601_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5597_, v_macroStack_5598_, v___y_5599_);
lean_dec_ref(v___y_5599_);
return v_res_5601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_){
_start:
{
lean_object* v_ref_5610_; lean_object* v___x_5611_; lean_object* v_a_5612_; lean_object* v_macroStack_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5624_; 
v_ref_5610_ = lean_ctor_get(v___y_5607_, 5);
v___x_5611_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5602_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
lean_inc(v_a_5612_);
lean_dec_ref(v___x_5611_);
v_macroStack_5613_ = lean_ctor_get(v___y_5603_, 1);
lean_inc_n(v_macroStack_5613_, 2);
v___x_5614_ = l_Lean_Elab_getBetterRef(v_ref_5610_, v_macroStack_5613_);
v___x_5615_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5612_, v_macroStack_5613_, v___y_5607_);
v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5618_ = v___x_5615_;
v_isShared_5619_ = v_isSharedCheck_5624_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5615_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5624_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5620_; lean_object* v___x_5622_; 
v___x_5620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5614_);
lean_ctor_set(v___x_5620_, 1, v_a_5616_);
if (v_isShared_5619_ == 0)
{
lean_ctor_set_tag(v___x_5618_, 1);
lean_ctor_set(v___x_5618_, 0, v___x_5620_);
v___x_5622_ = v___x_5618_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
return v_res_5633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5635_; lean_object* v___x_5636_; 
v___x_5635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5636_ = l_Lean_stringToMessageData(v___x_5635_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5637_, size_t v_sz_5638_, size_t v_i_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
lean_object* v_a_5649_; uint8_t v___x_5653_; 
v___x_5653_ = lean_usize_dec_lt(v_i_5639_, v_sz_5638_);
if (v___x_5653_ == 0)
{
lean_object* v___x_5654_; 
v___x_5654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5654_, 0, v_b_5640_);
return v___x_5654_;
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5656_; 
v_a_5655_ = lean_array_uget_borrowed(v_as_5637_, v_i_5639_);
lean_inc(v_a_5655_);
v___x_5656_ = l_Lean_MVarId_getType(v_a_5655_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5658_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref(v___x_5656_);
lean_inc(v_a_5655_);
v___x_5658_ = l_Lean_MVarId_getType(v_a_5655_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
lean_inc(v_a_5659_);
lean_dec_ref(v___x_5658_);
v___x_5660_ = lean_box(0);
v___x_5661_ = l_Lean_getRecAppSyntax_x3f(v_a_5659_);
lean_dec(v_a_5659_);
if (lean_obj_tag(v___x_5661_) == 1)
{
lean_object* v_val_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; 
v_val_5662_ = lean_ctor_get(v___x_5661_, 0);
lean_inc(v_val_5662_);
lean_dec_ref(v___x_5661_);
v___x_5663_ = l_Lean_Expr_mdataExpr_x21(v_a_5657_);
lean_dec(v_a_5657_);
lean_inc(v_a_5655_);
v___x_5664_ = l_Lean_MVarId_setType___redArg(v_a_5655_, v___x_5663_, v___y_5644_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_fileName_5665_; lean_object* v_fileMap_5666_; lean_object* v_options_5667_; lean_object* v_currRecDepth_5668_; lean_object* v_maxRecDepth_5669_; lean_object* v_ref_5670_; lean_object* v_currNamespace_5671_; lean_object* v_openDecls_5672_; lean_object* v_initHeartbeats_5673_; lean_object* v_maxHeartbeats_5674_; lean_object* v_quotContext_5675_; lean_object* v_currMacroScope_5676_; uint8_t v_diag_5677_; lean_object* v_cancelTk_x3f_5678_; uint8_t v_suppressElabErrors_5679_; lean_object* v_inheritedTraceOptions_5680_; lean_object* v_ref_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; 
lean_dec_ref(v___x_5664_);
v_fileName_5665_ = lean_ctor_get(v___y_5645_, 0);
v_fileMap_5666_ = lean_ctor_get(v___y_5645_, 1);
v_options_5667_ = lean_ctor_get(v___y_5645_, 2);
v_currRecDepth_5668_ = lean_ctor_get(v___y_5645_, 3);
v_maxRecDepth_5669_ = lean_ctor_get(v___y_5645_, 4);
v_ref_5670_ = lean_ctor_get(v___y_5645_, 5);
v_currNamespace_5671_ = lean_ctor_get(v___y_5645_, 6);
v_openDecls_5672_ = lean_ctor_get(v___y_5645_, 7);
v_initHeartbeats_5673_ = lean_ctor_get(v___y_5645_, 8);
v_maxHeartbeats_5674_ = lean_ctor_get(v___y_5645_, 9);
v_quotContext_5675_ = lean_ctor_get(v___y_5645_, 10);
v_currMacroScope_5676_ = lean_ctor_get(v___y_5645_, 11);
v_diag_5677_ = lean_ctor_get_uint8(v___y_5645_, sizeof(void*)*14);
v_cancelTk_x3f_5678_ = lean_ctor_get(v___y_5645_, 12);
v_suppressElabErrors_5679_ = lean_ctor_get_uint8(v___y_5645_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5680_ = lean_ctor_get(v___y_5645_, 13);
v_ref_5681_ = l_Lean_replaceRef(v_val_5662_, v_ref_5670_);
lean_dec(v_val_5662_);
lean_inc_ref(v_inheritedTraceOptions_5680_);
lean_inc(v_cancelTk_x3f_5678_);
lean_inc(v_currMacroScope_5676_);
lean_inc(v_quotContext_5675_);
lean_inc(v_maxHeartbeats_5674_);
lean_inc(v_initHeartbeats_5673_);
lean_inc(v_openDecls_5672_);
lean_inc(v_currNamespace_5671_);
lean_inc(v_maxRecDepth_5669_);
lean_inc(v_currRecDepth_5668_);
lean_inc_ref(v_options_5667_);
lean_inc_ref(v_fileMap_5666_);
lean_inc_ref(v_fileName_5665_);
v___x_5682_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5682_, 0, v_fileName_5665_);
lean_ctor_set(v___x_5682_, 1, v_fileMap_5666_);
lean_ctor_set(v___x_5682_, 2, v_options_5667_);
lean_ctor_set(v___x_5682_, 3, v_currRecDepth_5668_);
lean_ctor_set(v___x_5682_, 4, v_maxRecDepth_5669_);
lean_ctor_set(v___x_5682_, 5, v_ref_5681_);
lean_ctor_set(v___x_5682_, 6, v_currNamespace_5671_);
lean_ctor_set(v___x_5682_, 7, v_openDecls_5672_);
lean_ctor_set(v___x_5682_, 8, v_initHeartbeats_5673_);
lean_ctor_set(v___x_5682_, 9, v_maxHeartbeats_5674_);
lean_ctor_set(v___x_5682_, 10, v_quotContext_5675_);
lean_ctor_set(v___x_5682_, 11, v_currMacroScope_5676_);
lean_ctor_set(v___x_5682_, 12, v_cancelTk_x3f_5678_);
lean_ctor_set(v___x_5682_, 13, v_inheritedTraceOptions_5680_);
lean_ctor_set_uint8(v___x_5682_, sizeof(void*)*14, v_diag_5677_);
lean_ctor_set_uint8(v___x_5682_, sizeof(void*)*14 + 1, v_suppressElabErrors_5679_);
lean_inc(v_a_5655_);
v___x_5683_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5655_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___x_5682_, v___y_5646_);
lean_dec_ref(v___x_5682_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_dec_ref(v___x_5683_);
v_a_5649_ = v___x_5660_;
goto v___jp_5648_;
}
else
{
return v___x_5683_;
}
}
else
{
lean_dec(v_val_5662_);
return v___x_5664_;
}
}
else
{
lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
lean_dec(v___x_5661_);
v___x_5684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5685_ = l_Lean_indentExpr(v_a_5657_);
v___x_5686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5686_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
if (lean_obj_tag(v___x_5687_) == 0)
{
lean_dec_ref(v___x_5687_);
v_a_5649_ = v___x_5660_;
goto v___jp_5648_;
}
else
{
return v___x_5687_;
}
}
}
else
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5695_; 
lean_dec(v_a_5657_);
v_a_5688_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5690_ = v___x_5658_;
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v___x_5658_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
v_a_5696_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___x_5656_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5656_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
v___jp_5648_:
{
size_t v___x_5650_; size_t v___x_5651_; 
v___x_5650_ = ((size_t)1ULL);
v___x_5651_ = lean_usize_add(v_i_5639_, v___x_5650_);
v_i_5639_ = v___x_5651_;
v_b_5640_ = v_a_5649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5704_, lean_object* v_sz_5705_, lean_object* v_i_5706_, lean_object* v_b_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
size_t v_sz_boxed_5715_; size_t v_i_boxed_5716_; lean_object* v_res_5717_; 
v_sz_boxed_5715_ = lean_unbox_usize(v_sz_5705_);
lean_dec(v_sz_5705_);
v_i_boxed_5716_ = lean_unbox_usize(v_i_5706_);
lean_dec(v_i_5706_);
v_res_5717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5704_, v_sz_boxed_5715_, v_i_boxed_5716_, v_b_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
lean_dec(v___y_5713_);
lean_dec_ref(v___y_5712_);
lean_dec(v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec_ref(v_as_5704_);
return v_res_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5718_, size_t v_i_5719_, size_t v_stop_5720_, lean_object* v_b_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
uint8_t v___x_5727_; 
v___x_5727_ = lean_usize_dec_eq(v_i_5719_, v_stop_5720_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; lean_object* v___x_5729_; 
v___x_5728_ = lean_array_uget_borrowed(v_as_5718_, v_i_5719_);
lean_inc(v___x_5728_);
v___x_5729_ = l_Lean_MVarId_getType(v___x_5728_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
lean_dec_ref(v___x_5729_);
v___x_5731_ = l_Lean_Expr_mdataExpr_x21(v_a_5730_);
lean_dec(v_a_5730_);
lean_inc(v___x_5728_);
v___x_5732_ = l_Lean_MVarId_setType___redArg(v___x_5728_, v___x_5731_, v___y_5723_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; size_t v___x_5734_; size_t v___x_5735_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref(v___x_5732_);
v___x_5734_ = ((size_t)1ULL);
v___x_5735_ = lean_usize_add(v_i_5719_, v___x_5734_);
v_i_5719_ = v___x_5735_;
v_b_5721_ = v_a_5733_;
goto _start;
}
else
{
return v___x_5732_;
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
v_a_5737_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5729_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5729_);
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
else
{
lean_object* v___x_5745_; 
v___x_5745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5745_, 0, v_b_5721_);
return v___x_5745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5746_, lean_object* v_i_5747_, lean_object* v_stop_5748_, lean_object* v_b_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
size_t v_i_boxed_5755_; size_t v_stop_boxed_5756_; lean_object* v_res_5757_; 
v_i_boxed_5755_ = lean_unbox_usize(v_i_5747_);
lean_dec(v_i_5747_);
v_stop_boxed_5756_ = lean_unbox_usize(v_stop_5748_);
lean_dec(v_stop_5748_);
v_res_5757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5746_, v_i_boxed_5755_, v_stop_boxed_5756_, v_b_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
lean_dec_ref(v_as_5746_);
return v_res_5757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5758_, lean_object* v___x_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_){
_start:
{
if (lean_obj_tag(v___x_5758_) == 0)
{
lean_object* v___x_5767_; size_t v_sz_5768_; size_t v___x_5769_; lean_object* v___x_5770_; 
v___x_5767_ = lean_box(0);
v_sz_5768_ = lean_array_size(v___x_5759_);
v___x_5769_ = ((size_t)0ULL);
v___x_5770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5759_, v_sz_5768_, v___x_5769_, v___x_5767_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
lean_dec_ref(v___x_5759_);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5777_; 
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5770_);
if (v_isSharedCheck_5777_ == 0)
{
lean_object* v_unused_5778_; 
v_unused_5778_ = lean_ctor_get(v___x_5770_, 0);
lean_dec(v_unused_5778_);
v___x_5772_ = v___x_5770_;
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
else
{
lean_dec(v___x_5770_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5775_; 
if (v_isShared_5773_ == 0)
{
lean_ctor_set(v___x_5772_, 0, v___x_5767_);
v___x_5775_ = v___x_5772_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v___x_5767_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
else
{
return v___x_5770_;
}
}
else
{
lean_object* v_val_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5858_; 
v_val_5779_ = lean_ctor_get(v___x_5758_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5758_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5781_ = v___x_5758_;
v_isShared_5782_ = v_isSharedCheck_5858_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_val_5779_);
lean_dec(v___x_5758_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5858_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v_ref_5783_; lean_object* v_tactic_5784_; lean_object* v_fileName_5785_; lean_object* v_fileMap_5786_; lean_object* v_options_5787_; lean_object* v_currRecDepth_5788_; lean_object* v_maxRecDepth_5789_; lean_object* v_ref_5790_; lean_object* v_currNamespace_5791_; lean_object* v_openDecls_5792_; lean_object* v_initHeartbeats_5793_; lean_object* v_maxHeartbeats_5794_; lean_object* v_quotContext_5795_; lean_object* v_currMacroScope_5796_; uint8_t v_diag_5797_; lean_object* v_cancelTk_x3f_5798_; uint8_t v_suppressElabErrors_5799_; lean_object* v_inheritedTraceOptions_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v_ref_5803_; lean_object* v___x_5804_; lean_object* v___y_5831_; lean_object* v___y_5848_; uint8_t v___x_5849_; 
v_ref_5783_ = lean_ctor_get(v_val_5779_, 0);
lean_inc(v_ref_5783_);
v_tactic_5784_ = lean_ctor_get(v_val_5779_, 1);
lean_inc(v_tactic_5784_);
lean_dec(v_val_5779_);
v_fileName_5785_ = lean_ctor_get(v___y_5764_, 0);
v_fileMap_5786_ = lean_ctor_get(v___y_5764_, 1);
v_options_5787_ = lean_ctor_get(v___y_5764_, 2);
v_currRecDepth_5788_ = lean_ctor_get(v___y_5764_, 3);
v_maxRecDepth_5789_ = lean_ctor_get(v___y_5764_, 4);
v_ref_5790_ = lean_ctor_get(v___y_5764_, 5);
v_currNamespace_5791_ = lean_ctor_get(v___y_5764_, 6);
v_openDecls_5792_ = lean_ctor_get(v___y_5764_, 7);
v_initHeartbeats_5793_ = lean_ctor_get(v___y_5764_, 8);
v_maxHeartbeats_5794_ = lean_ctor_get(v___y_5764_, 9);
v_quotContext_5795_ = lean_ctor_get(v___y_5764_, 10);
v_currMacroScope_5796_ = lean_ctor_get(v___y_5764_, 11);
v_diag_5797_ = lean_ctor_get_uint8(v___y_5764_, sizeof(void*)*14);
v_cancelTk_x3f_5798_ = lean_ctor_get(v___y_5764_, 12);
v_suppressElabErrors_5799_ = lean_ctor_get_uint8(v___y_5764_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5800_ = lean_ctor_get(v___y_5764_, 13);
v___x_5801_ = lean_unsigned_to_nat(0u);
v___x_5802_ = lean_array_get_size(v___x_5759_);
v_ref_5803_ = l_Lean_replaceRef(v_ref_5783_, v_ref_5790_);
lean_inc_ref(v_inheritedTraceOptions_5800_);
lean_inc(v_cancelTk_x3f_5798_);
lean_inc(v_currMacroScope_5796_);
lean_inc(v_quotContext_5795_);
lean_inc(v_maxHeartbeats_5794_);
lean_inc(v_initHeartbeats_5793_);
lean_inc(v_openDecls_5792_);
lean_inc(v_currNamespace_5791_);
lean_inc(v_maxRecDepth_5789_);
lean_inc(v_currRecDepth_5788_);
lean_inc_ref(v_options_5787_);
lean_inc_ref(v_fileMap_5786_);
lean_inc_ref(v_fileName_5785_);
v___x_5804_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5804_, 0, v_fileName_5785_);
lean_ctor_set(v___x_5804_, 1, v_fileMap_5786_);
lean_ctor_set(v___x_5804_, 2, v_options_5787_);
lean_ctor_set(v___x_5804_, 3, v_currRecDepth_5788_);
lean_ctor_set(v___x_5804_, 4, v_maxRecDepth_5789_);
lean_ctor_set(v___x_5804_, 5, v_ref_5803_);
lean_ctor_set(v___x_5804_, 6, v_currNamespace_5791_);
lean_ctor_set(v___x_5804_, 7, v_openDecls_5792_);
lean_ctor_set(v___x_5804_, 8, v_initHeartbeats_5793_);
lean_ctor_set(v___x_5804_, 9, v_maxHeartbeats_5794_);
lean_ctor_set(v___x_5804_, 10, v_quotContext_5795_);
lean_ctor_set(v___x_5804_, 11, v_currMacroScope_5796_);
lean_ctor_set(v___x_5804_, 12, v_cancelTk_x3f_5798_);
lean_ctor_set(v___x_5804_, 13, v_inheritedTraceOptions_5800_);
lean_ctor_set_uint8(v___x_5804_, sizeof(void*)*14, v_diag_5797_);
lean_ctor_set_uint8(v___x_5804_, sizeof(void*)*14 + 1, v_suppressElabErrors_5799_);
v___x_5849_ = lean_nat_dec_lt(v___x_5801_, v___x_5802_);
if (v___x_5849_ == 0)
{
goto v___jp_5832_;
}
else
{
lean_object* v___x_5850_; uint8_t v___x_5851_; 
v___x_5850_ = lean_box(0);
v___x_5851_ = lean_nat_dec_le(v___x_5802_, v___x_5802_);
if (v___x_5851_ == 0)
{
if (v___x_5849_ == 0)
{
goto v___jp_5832_;
}
else
{
size_t v___x_5852_; size_t v___x_5853_; lean_object* v___x_5854_; 
v___x_5852_ = ((size_t)0ULL);
v___x_5853_ = lean_usize_of_nat(v___x_5802_);
v___x_5854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5759_, v___x_5852_, v___x_5853_, v___x_5850_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
v___y_5848_ = v___x_5854_;
goto v___jp_5847_;
}
}
else
{
size_t v___x_5855_; size_t v___x_5856_; lean_object* v___x_5857_; 
v___x_5855_ = ((size_t)0ULL);
v___x_5856_ = lean_usize_of_nat(v___x_5802_);
v___x_5857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5759_, v___x_5855_, v___x_5856_, v___x_5850_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
v___y_5848_ = v___x_5857_;
goto v___jp_5847_;
}
}
v___jp_5805_:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___f_5809_; lean_object* v___x_5810_; 
v___x_5806_ = lean_box(0);
v___x_5807_ = lean_array_get(v___x_5806_, v___x_5759_, v___x_5801_);
v___x_5808_ = lean_array_to_list(v___x_5759_);
v___f_5809_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5809_, 0, v___x_5808_);
lean_closure_set(v___f_5809_, 1, v_ref_5783_);
lean_closure_set(v___f_5809_, 2, v_tactic_5784_);
v___x_5810_ = l_Lean_Elab_Tactic_run(v___x_5807_, v___f_5809_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5821_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5821_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5821_ == 0)
{
v___x_5813_ = v___x_5810_;
v_isShared_5814_ = v_isSharedCheck_5821_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5810_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5821_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
uint8_t v___x_5815_; 
v___x_5815_ = l_List_isEmpty___redArg(v_a_5811_);
if (v___x_5815_ == 0)
{
lean_object* v___x_5816_; 
lean_del_object(v___x_5813_);
v___x_5816_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5811_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
lean_dec_ref(v___x_5804_);
return v___x_5816_;
}
else
{
lean_object* v___x_5817_; lean_object* v___x_5819_; 
lean_dec(v_a_5811_);
lean_dec_ref(v___x_5804_);
v___x_5817_ = lean_box(0);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 0, v___x_5817_);
v___x_5819_ = v___x_5813_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5817_);
v___x_5819_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
return v___x_5819_;
}
}
}
}
else
{
lean_object* v_a_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5829_; 
lean_dec_ref(v___x_5804_);
v_a_5822_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5824_ = v___x_5810_;
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_a_5822_);
lean_dec(v___x_5810_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5827_; 
if (v_isShared_5825_ == 0)
{
v___x_5827_ = v___x_5824_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
v___x_5827_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
return v___x_5827_;
}
}
}
}
v___jp_5830_:
{
if (lean_obj_tag(v___y_5831_) == 0)
{
lean_dec_ref(v___y_5831_);
goto v___jp_5805_;
}
else
{
lean_dec_ref(v___x_5804_);
lean_dec(v_tactic_5784_);
lean_dec(v_ref_5783_);
lean_dec_ref(v___x_5759_);
return v___y_5831_;
}
}
v___jp_5832_:
{
uint8_t v___x_5833_; 
v___x_5833_ = lean_nat_dec_eq(v___x_5802_, v___x_5801_);
if (v___x_5833_ == 0)
{
uint8_t v___x_5834_; 
lean_del_object(v___x_5781_);
v___x_5834_ = lean_nat_dec_lt(v___x_5801_, v___x_5802_);
if (v___x_5834_ == 0)
{
goto v___jp_5805_;
}
else
{
lean_object* v___x_5835_; uint8_t v___x_5836_; 
v___x_5835_ = lean_box(0);
v___x_5836_ = lean_nat_dec_le(v___x_5802_, v___x_5802_);
if (v___x_5836_ == 0)
{
if (v___x_5834_ == 0)
{
goto v___jp_5805_;
}
else
{
size_t v___x_5837_; size_t v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = ((size_t)0ULL);
v___x_5838_ = lean_usize_of_nat(v___x_5802_);
v___x_5839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5759_, v___x_5837_, v___x_5838_, v___x_5835_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
v___y_5831_ = v___x_5839_;
goto v___jp_5830_;
}
}
else
{
size_t v___x_5840_; size_t v___x_5841_; lean_object* v___x_5842_; 
v___x_5840_ = ((size_t)0ULL);
v___x_5841_ = lean_usize_of_nat(v___x_5802_);
v___x_5842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5759_, v___x_5840_, v___x_5841_, v___x_5835_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___x_5804_, v___y_5765_);
v___y_5831_ = v___x_5842_;
goto v___jp_5830_;
}
}
}
else
{
lean_object* v___x_5843_; lean_object* v___x_5845_; 
lean_dec_ref(v___x_5804_);
lean_dec(v_tactic_5784_);
lean_dec(v_ref_5783_);
lean_dec_ref(v___x_5759_);
v___x_5843_ = lean_box(0);
if (v_isShared_5782_ == 0)
{
lean_ctor_set_tag(v___x_5781_, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5843_);
v___x_5845_ = v___x_5781_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5843_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
v___jp_5847_:
{
if (lean_obj_tag(v___y_5848_) == 0)
{
lean_dec_ref(v___y_5848_);
goto v___jp_5832_;
}
else
{
lean_dec_ref(v___x_5804_);
lean_dec(v_tactic_5784_);
lean_dec(v_ref_5783_);
lean_del_object(v___x_5781_);
lean_dec_ref(v___x_5759_);
return v___y_5848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5859_, lean_object* v___x_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_){
_start:
{
lean_object* v_res_5868_; 
v_res_5868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5859_, v___x_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec_ref(v___y_5861_);
return v_res_5868_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5869_){
_start:
{
uint8_t v___x_5870_; 
v___x_5870_ = 0;
return v___x_5870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5871_){
_start:
{
uint8_t v_res_5872_; lean_object* v_r_5873_; 
v_res_5872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5871_);
lean_dec(v_x_5871_);
v_r_5873_ = lean_box(v_res_5872_);
return v_r_5873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5880_, size_t v_sz_5881_, size_t v_i_5882_, lean_object* v_b_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_){
_start:
{
uint8_t v___x_5889_; 
v___x_5889_ = lean_usize_dec_lt(v_i_5882_, v_sz_5881_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5890_; 
v___x_5890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5890_, 0, v_b_5883_);
return v___x_5890_;
}
else
{
lean_object* v_snd_5891_; lean_object* v_fst_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5963_; 
v_snd_5891_ = lean_ctor_get(v_b_5883_, 1);
v_fst_5892_ = lean_ctor_get(v_b_5883_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v_b_5883_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5894_ = v_b_5883_;
v_isShared_5895_ = v_isSharedCheck_5963_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_snd_5891_);
lean_inc(v_fst_5892_);
lean_dec(v_b_5883_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5963_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v_array_5896_; lean_object* v_start_5897_; lean_object* v_stop_5898_; uint8_t v___x_5899_; 
v_array_5896_ = lean_ctor_get(v_snd_5891_, 0);
v_start_5897_ = lean_ctor_get(v_snd_5891_, 1);
v_stop_5898_ = lean_ctor_get(v_snd_5891_, 2);
v___x_5899_ = lean_nat_dec_lt(v_start_5897_, v_stop_5898_);
if (v___x_5899_ == 0)
{
lean_object* v___x_5901_; 
if (v_isShared_5895_ == 0)
{
v___x_5901_ = v___x_5894_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_fst_5892_);
lean_ctor_set(v_reuseFailAlloc_5903_, 1, v_snd_5891_);
v___x_5901_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
lean_object* v___x_5902_; 
v___x_5902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
return v___x_5902_;
}
}
else
{
lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5959_; 
lean_inc(v_stop_5898_);
lean_inc(v_start_5897_);
lean_inc_ref(v_array_5896_);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_snd_5891_);
if (v_isSharedCheck_5959_ == 0)
{
lean_object* v_unused_5960_; lean_object* v_unused_5961_; lean_object* v_unused_5962_; 
v_unused_5960_ = lean_ctor_get(v_snd_5891_, 2);
lean_dec(v_unused_5960_);
v_unused_5961_ = lean_ctor_get(v_snd_5891_, 1);
lean_dec(v_unused_5961_);
v_unused_5962_ = lean_ctor_get(v_snd_5891_, 0);
lean_dec(v_unused_5962_);
v___x_5905_ = v_snd_5891_;
v_isShared_5906_ = v_isSharedCheck_5959_;
goto v_resetjp_5904_;
}
else
{
lean_dec(v_snd_5891_);
v___x_5905_ = lean_box(0);
v_isShared_5906_ = v_isSharedCheck_5959_;
goto v_resetjp_5904_;
}
v_resetjp_5904_:
{
lean_object* v_array_5907_; lean_object* v_start_5908_; lean_object* v_stop_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5914_; 
v_array_5907_ = lean_ctor_get(v_fst_5892_, 0);
v_start_5908_ = lean_ctor_get(v_fst_5892_, 1);
v_stop_5909_ = lean_ctor_get(v_fst_5892_, 2);
v___x_5910_ = lean_array_fget(v_array_5896_, v_start_5897_);
v___x_5911_ = lean_unsigned_to_nat(1u);
v___x_5912_ = lean_nat_add(v_start_5897_, v___x_5911_);
lean_dec(v_start_5897_);
if (v_isShared_5906_ == 0)
{
lean_ctor_set(v___x_5905_, 1, v___x_5912_);
v___x_5914_ = v___x_5905_;
goto v_reusejp_5913_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_array_5896_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v___x_5912_);
lean_ctor_set(v_reuseFailAlloc_5958_, 2, v_stop_5898_);
v___x_5914_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
uint8_t v___x_5915_; 
v___x_5915_ = lean_nat_dec_lt(v_start_5908_, v_stop_5909_);
if (v___x_5915_ == 0)
{
lean_object* v___x_5917_; 
lean_dec(v___x_5910_);
if (v_isShared_5895_ == 0)
{
lean_ctor_set(v___x_5894_, 1, v___x_5914_);
v___x_5917_ = v___x_5894_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_fst_5892_);
lean_ctor_set(v_reuseFailAlloc_5919_, 1, v___x_5914_);
v___x_5917_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
lean_object* v___x_5918_; 
v___x_5918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
return v___x_5918_;
}
}
else
{
lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5954_; 
lean_inc(v_stop_5909_);
lean_inc(v_start_5908_);
lean_inc_ref(v_array_5907_);
v_isSharedCheck_5954_ = !lean_is_exclusive(v_fst_5892_);
if (v_isSharedCheck_5954_ == 0)
{
lean_object* v_unused_5955_; lean_object* v_unused_5956_; lean_object* v_unused_5957_; 
v_unused_5955_ = lean_ctor_get(v_fst_5892_, 2);
lean_dec(v_unused_5955_);
v_unused_5956_ = lean_ctor_get(v_fst_5892_, 1);
lean_dec(v_unused_5956_);
v_unused_5957_ = lean_ctor_get(v_fst_5892_, 0);
lean_dec(v_unused_5957_);
v___x_5921_ = v_fst_5892_;
v_isShared_5922_ = v_isSharedCheck_5954_;
goto v_resetjp_5920_;
}
else
{
lean_dec(v_fst_5892_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5954_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___f_5923_; lean_object* v_a_5924_; lean_object* v___x_5925_; lean_object* v___y_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; uint8_t v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___f_5923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5924_ = lean_array_uget_borrowed(v_as_5880_, v_i_5882_);
v___x_5925_ = lean_array_fget_borrowed(v_array_5907_, v_start_5908_);
lean_inc(v___x_5925_);
v___y_5926_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5926_, 0, v___x_5910_);
lean_closure_set(v___y_5926_, 1, v___x_5925_);
lean_inc(v_a_5924_);
v___x_5927_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5927_, 0, lean_box(0));
lean_closure_set(v___x_5927_, 1, v_a_5924_);
lean_closure_set(v___x_5927_, 2, v___y_5926_);
v___x_5928_ = lean_box(0);
v___x_5929_ = lean_box(0);
v___x_5930_ = lean_box(1);
v___x_5931_ = 0;
v___x_5932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5933_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5933_, 0, v___x_5928_);
lean_ctor_set(v___x_5933_, 1, v___x_5929_);
lean_ctor_set(v___x_5933_, 2, v___x_5928_);
lean_ctor_set(v___x_5933_, 3, v___f_5923_);
lean_ctor_set(v___x_5933_, 4, v___x_5930_);
lean_ctor_set(v___x_5933_, 5, v___x_5930_);
lean_ctor_set(v___x_5933_, 6, v___x_5928_);
lean_ctor_set(v___x_5933_, 7, v___x_5932_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8, v___x_5915_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 1, v___x_5915_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 2, v___x_5915_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 3, v___x_5915_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 4, v___x_5931_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 5, v___x_5931_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 6, v___x_5931_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 7, v___x_5931_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 8, v___x_5915_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 9, v___x_5931_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*8 + 10, v___x_5915_);
v___x_5934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5935_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5927_, v___x_5933_, v___x_5934_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
if (lean_obj_tag(v___x_5935_) == 0)
{
lean_object* v___x_5936_; lean_object* v___x_5938_; 
lean_dec_ref(v___x_5935_);
v___x_5936_ = lean_nat_add(v_start_5908_, v___x_5911_);
lean_dec(v_start_5908_);
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 1, v___x_5936_);
v___x_5938_ = v___x_5921_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_array_5907_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v___x_5936_);
lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_stop_5909_);
v___x_5938_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
lean_object* v___x_5940_; 
if (v_isShared_5895_ == 0)
{
lean_ctor_set(v___x_5894_, 1, v___x_5914_);
lean_ctor_set(v___x_5894_, 0, v___x_5938_);
v___x_5940_ = v___x_5894_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5938_);
lean_ctor_set(v_reuseFailAlloc_5944_, 1, v___x_5914_);
v___x_5940_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
size_t v___x_5941_; size_t v___x_5942_; 
v___x_5941_ = ((size_t)1ULL);
v___x_5942_ = lean_usize_add(v_i_5882_, v___x_5941_);
v_i_5882_ = v___x_5942_;
v_b_5883_ = v___x_5940_;
goto _start;
}
}
}
else
{
lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_del_object(v___x_5921_);
lean_dec_ref(v___x_5914_);
lean_dec(v_stop_5909_);
lean_dec(v_start_5908_);
lean_dec_ref(v_array_5907_);
lean_del_object(v___x_5894_);
v_a_5946_ = lean_ctor_get(v___x_5935_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5935_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5948_ = v___x_5935_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v___x_5935_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5964_, lean_object* v_sz_5965_, lean_object* v_i_5966_, lean_object* v_b_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
size_t v_sz_boxed_5973_; size_t v_i_boxed_5974_; lean_object* v_res_5975_; 
v_sz_boxed_5973_ = lean_unbox_usize(v_sz_5965_);
lean_dec(v_sz_5965_);
v_i_boxed_5974_ = lean_unbox_usize(v_i_5966_);
lean_dec(v_i_5966_);
v_res_5975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5964_, v_sz_boxed_5973_, v_i_boxed_5974_, v_b_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_);
lean_dec(v___y_5971_);
lean_dec_ref(v___y_5970_);
lean_dec(v___y_5969_);
lean_dec_ref(v___y_5968_);
lean_dec_ref(v_as_5964_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5976_, lean_object* v_decrTactics_5977_, lean_object* v_argsPacker_5978_, lean_object* v_funNames_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_){
_start:
{
lean_object* v___x_5985_; 
lean_inc_ref(v_value_5976_);
v___x_5985_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5976_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
if (lean_obj_tag(v___x_5985_) == 0)
{
lean_object* v_a_5986_; lean_object* v___x_5987_; 
v_a_5986_ = lean_ctor_get(v___x_5985_, 0);
lean_inc(v_a_5986_);
lean_dec_ref(v___x_5985_);
v___x_5987_ = l_Lean_Elab_WF_assignSubsumed(v_a_5986_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
lean_dec(v_a_5986_);
if (lean_obj_tag(v___x_5987_) == 0)
{
lean_object* v_a_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v_a_5988_ = lean_ctor_get(v___x_5987_, 0);
lean_inc(v_a_5988_);
lean_dec_ref(v___x_5987_);
v___x_5989_ = lean_array_get_size(v_decrTactics_5977_);
v___x_5990_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5978_, v___x_5989_, v_a_5988_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
lean_dec(v_a_5988_);
if (lean_obj_tag(v___x_5990_) == 0)
{
lean_object* v_a_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; size_t v_sz_5997_; size_t v___x_5998_; lean_object* v___x_5999_; 
v_a_5991_ = lean_ctor_get(v___x_5990_, 0);
lean_inc(v_a_5991_);
lean_dec_ref(v___x_5990_);
v___x_5992_ = lean_unsigned_to_nat(0u);
v___x_5993_ = lean_array_get_size(v_a_5991_);
v___x_5994_ = l_Array_toSubarray___redArg(v_a_5991_, v___x_5992_, v___x_5993_);
v___x_5995_ = l_Array_toSubarray___redArg(v_decrTactics_5977_, v___x_5992_, v___x_5989_);
v___x_5996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5994_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v_sz_5997_ = lean_array_size(v_funNames_5979_);
v___x_5998_ = ((size_t)0ULL);
v___x_5999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5979_, v_sz_5997_, v___x_5998_, v___x_5996_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
if (lean_obj_tag(v___x_5999_) == 0)
{
lean_object* v___x_6000_; 
lean_dec_ref(v___x_5999_);
v___x_6000_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5976_, v___y_5981_);
return v___x_6000_;
}
else
{
lean_object* v_a_6001_; lean_object* v___x_6003_; uint8_t v_isShared_6004_; uint8_t v_isSharedCheck_6008_; 
lean_dec_ref(v_value_5976_);
v_a_6001_ = lean_ctor_get(v___x_5999_, 0);
v_isSharedCheck_6008_ = !lean_is_exclusive(v___x_5999_);
if (v_isSharedCheck_6008_ == 0)
{
v___x_6003_ = v___x_5999_;
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
else
{
lean_inc(v_a_6001_);
lean_dec(v___x_5999_);
v___x_6003_ = lean_box(0);
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
v_resetjp_6002_:
{
lean_object* v___x_6006_; 
if (v_isShared_6004_ == 0)
{
v___x_6006_ = v___x_6003_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6001_);
v___x_6006_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
return v___x_6006_;
}
}
}
}
else
{
lean_object* v_a_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6016_; 
lean_dec_ref(v_decrTactics_5977_);
lean_dec_ref(v_value_5976_);
v_a_6009_ = lean_ctor_get(v___x_5990_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v___x_5990_);
if (v_isSharedCheck_6016_ == 0)
{
v___x_6011_ = v___x_5990_;
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_a_6009_);
lean_dec(v___x_5990_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6014_; 
if (v_isShared_6012_ == 0)
{
v___x_6014_ = v___x_6011_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6009_);
v___x_6014_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
return v___x_6014_;
}
}
}
}
else
{
lean_object* v_a_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6024_; 
lean_dec_ref(v_decrTactics_5977_);
lean_dec_ref(v_value_5976_);
v_a_6017_ = lean_ctor_get(v___x_5987_, 0);
v_isSharedCheck_6024_ = !lean_is_exclusive(v___x_5987_);
if (v_isSharedCheck_6024_ == 0)
{
v___x_6019_ = v___x_5987_;
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_a_6017_);
lean_dec(v___x_5987_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___x_6022_; 
if (v_isShared_6020_ == 0)
{
v___x_6022_ = v___x_6019_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6017_);
v___x_6022_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
return v___x_6022_;
}
}
}
}
else
{
lean_object* v_a_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6032_; 
lean_dec_ref(v_decrTactics_5977_);
lean_dec_ref(v_value_5976_);
v_a_6025_ = lean_ctor_get(v___x_5985_, 0);
v_isSharedCheck_6032_ = !lean_is_exclusive(v___x_5985_);
if (v_isSharedCheck_6032_ == 0)
{
v___x_6027_ = v___x_5985_;
v_isShared_6028_ = v_isSharedCheck_6032_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_a_6025_);
lean_dec(v___x_5985_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6032_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6030_; 
if (v_isShared_6028_ == 0)
{
v___x_6030_ = v___x_6027_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_a_6025_);
v___x_6030_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
return v___x_6030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6033_, lean_object* v_decrTactics_6034_, lean_object* v_argsPacker_6035_, lean_object* v_funNames_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v_res_6042_; 
v_res_6042_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6033_, v_decrTactics_6034_, v_argsPacker_6035_, v_funNames_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
lean_dec(v___y_6040_);
lean_dec_ref(v___y_6039_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
lean_dec_ref(v_funNames_6036_);
lean_dec_ref(v_argsPacker_6035_);
return v_res_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6043_, uint8_t v_isExporting_6044_, lean_object* v___x_6045_, lean_object* v___y_6046_, lean_object* v___x_6047_, lean_object* v_a_x3f_6048_){
_start:
{
lean_object* v___x_6050_; lean_object* v_env_6051_; lean_object* v_nextMacroScope_6052_; lean_object* v_ngen_6053_; lean_object* v_auxDeclNGen_6054_; lean_object* v_traceState_6055_; lean_object* v_messages_6056_; lean_object* v_infoState_6057_; lean_object* v_snapshotTasks_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6083_; 
v___x_6050_ = lean_st_ref_take(v___y_6043_);
v_env_6051_ = lean_ctor_get(v___x_6050_, 0);
v_nextMacroScope_6052_ = lean_ctor_get(v___x_6050_, 1);
v_ngen_6053_ = lean_ctor_get(v___x_6050_, 2);
v_auxDeclNGen_6054_ = lean_ctor_get(v___x_6050_, 3);
v_traceState_6055_ = lean_ctor_get(v___x_6050_, 4);
v_messages_6056_ = lean_ctor_get(v___x_6050_, 6);
v_infoState_6057_ = lean_ctor_get(v___x_6050_, 7);
v_snapshotTasks_6058_ = lean_ctor_get(v___x_6050_, 8);
v_isSharedCheck_6083_ = !lean_is_exclusive(v___x_6050_);
if (v_isSharedCheck_6083_ == 0)
{
lean_object* v_unused_6084_; 
v_unused_6084_ = lean_ctor_get(v___x_6050_, 5);
lean_dec(v_unused_6084_);
v___x_6060_ = v___x_6050_;
v_isShared_6061_ = v_isSharedCheck_6083_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_snapshotTasks_6058_);
lean_inc(v_infoState_6057_);
lean_inc(v_messages_6056_);
lean_inc(v_traceState_6055_);
lean_inc(v_auxDeclNGen_6054_);
lean_inc(v_ngen_6053_);
lean_inc(v_nextMacroScope_6052_);
lean_inc(v_env_6051_);
lean_dec(v___x_6050_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6083_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6062_; lean_object* v___x_6064_; 
v___x_6062_ = l_Lean_Environment_setExporting(v_env_6051_, v_isExporting_6044_);
if (v_isShared_6061_ == 0)
{
lean_ctor_set(v___x_6060_, 5, v___x_6045_);
lean_ctor_set(v___x_6060_, 0, v___x_6062_);
v___x_6064_ = v___x_6060_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v___x_6062_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v_nextMacroScope_6052_);
lean_ctor_set(v_reuseFailAlloc_6082_, 2, v_ngen_6053_);
lean_ctor_set(v_reuseFailAlloc_6082_, 3, v_auxDeclNGen_6054_);
lean_ctor_set(v_reuseFailAlloc_6082_, 4, v_traceState_6055_);
lean_ctor_set(v_reuseFailAlloc_6082_, 5, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6082_, 6, v_messages_6056_);
lean_ctor_set(v_reuseFailAlloc_6082_, 7, v_infoState_6057_);
lean_ctor_set(v_reuseFailAlloc_6082_, 8, v_snapshotTasks_6058_);
v___x_6064_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v_mctx_6067_; lean_object* v_zetaDeltaFVarIds_6068_; lean_object* v_postponed_6069_; lean_object* v_diag_6070_; lean_object* v___x_6072_; uint8_t v_isShared_6073_; uint8_t v_isSharedCheck_6080_; 
v___x_6065_ = lean_st_ref_set(v___y_6043_, v___x_6064_);
v___x_6066_ = lean_st_ref_take(v___y_6046_);
v_mctx_6067_ = lean_ctor_get(v___x_6066_, 0);
v_zetaDeltaFVarIds_6068_ = lean_ctor_get(v___x_6066_, 2);
v_postponed_6069_ = lean_ctor_get(v___x_6066_, 3);
v_diag_6070_ = lean_ctor_get(v___x_6066_, 4);
v_isSharedCheck_6080_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; 
v_unused_6081_ = lean_ctor_get(v___x_6066_, 1);
lean_dec(v_unused_6081_);
v___x_6072_ = v___x_6066_;
v_isShared_6073_ = v_isSharedCheck_6080_;
goto v_resetjp_6071_;
}
else
{
lean_inc(v_diag_6070_);
lean_inc(v_postponed_6069_);
lean_inc(v_zetaDeltaFVarIds_6068_);
lean_inc(v_mctx_6067_);
lean_dec(v___x_6066_);
v___x_6072_ = lean_box(0);
v_isShared_6073_ = v_isSharedCheck_6080_;
goto v_resetjp_6071_;
}
v_resetjp_6071_:
{
lean_object* v___x_6075_; 
if (v_isShared_6073_ == 0)
{
lean_ctor_set(v___x_6072_, 1, v___x_6047_);
v___x_6075_ = v___x_6072_;
goto v_reusejp_6074_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_mctx_6067_);
lean_ctor_set(v_reuseFailAlloc_6079_, 1, v___x_6047_);
lean_ctor_set(v_reuseFailAlloc_6079_, 2, v_zetaDeltaFVarIds_6068_);
lean_ctor_set(v_reuseFailAlloc_6079_, 3, v_postponed_6069_);
lean_ctor_set(v_reuseFailAlloc_6079_, 4, v_diag_6070_);
v___x_6075_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6074_;
}
v_reusejp_6074_:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6076_ = lean_st_ref_set(v___y_6046_, v___x_6075_);
v___x_6077_ = lean_box(0);
v___x_6078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
return v___x_6078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6085_, lean_object* v_isExporting_6086_, lean_object* v___x_6087_, lean_object* v___y_6088_, lean_object* v___x_6089_, lean_object* v_a_x3f_6090_, lean_object* v___y_6091_){
_start:
{
uint8_t v_isExporting_boxed_6092_; lean_object* v_res_6093_; 
v_isExporting_boxed_6092_ = lean_unbox(v_isExporting_6086_);
v_res_6093_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6085_, v_isExporting_boxed_6092_, v___x_6087_, v___y_6088_, v___x_6089_, v_a_x3f_6090_);
lean_dec(v_a_x3f_6090_);
lean_dec(v___y_6088_);
lean_dec(v___y_6085_);
return v_res_6093_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6094_; 
v___x_6094_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6094_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
return v___x_6096_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; 
v___x_6097_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
return v___x_6098_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6099_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6100_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
lean_ctor_set(v___x_6100_, 2, v___x_6099_);
lean_ctor_set(v___x_6100_, 3, v___x_6099_);
lean_ctor_set(v___x_6100_, 4, v___x_6099_);
lean_ctor_set(v___x_6100_, 5, v___x_6099_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6101_, uint8_t v_isExporting_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_){
_start:
{
lean_object* v___x_6108_; lean_object* v_env_6109_; uint8_t v_isExporting_6110_; lean_object* v___x_6111_; lean_object* v_env_6112_; lean_object* v_nextMacroScope_6113_; lean_object* v_ngen_6114_; lean_object* v_auxDeclNGen_6115_; lean_object* v_traceState_6116_; lean_object* v_messages_6117_; lean_object* v_infoState_6118_; lean_object* v_snapshotTasks_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6173_; 
v___x_6108_ = lean_st_ref_get(v___y_6106_);
v_env_6109_ = lean_ctor_get(v___x_6108_, 0);
lean_inc_ref(v_env_6109_);
lean_dec(v___x_6108_);
v_isExporting_6110_ = lean_ctor_get_uint8(v_env_6109_, sizeof(void*)*8);
lean_dec_ref(v_env_6109_);
v___x_6111_ = lean_st_ref_take(v___y_6106_);
v_env_6112_ = lean_ctor_get(v___x_6111_, 0);
v_nextMacroScope_6113_ = lean_ctor_get(v___x_6111_, 1);
v_ngen_6114_ = lean_ctor_get(v___x_6111_, 2);
v_auxDeclNGen_6115_ = lean_ctor_get(v___x_6111_, 3);
v_traceState_6116_ = lean_ctor_get(v___x_6111_, 4);
v_messages_6117_ = lean_ctor_get(v___x_6111_, 6);
v_infoState_6118_ = lean_ctor_get(v___x_6111_, 7);
v_snapshotTasks_6119_ = lean_ctor_get(v___x_6111_, 8);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6111_);
if (v_isSharedCheck_6173_ == 0)
{
lean_object* v_unused_6174_; 
v_unused_6174_ = lean_ctor_get(v___x_6111_, 5);
lean_dec(v_unused_6174_);
v___x_6121_ = v___x_6111_;
v_isShared_6122_ = v_isSharedCheck_6173_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_snapshotTasks_6119_);
lean_inc(v_infoState_6118_);
lean_inc(v_messages_6117_);
lean_inc(v_traceState_6116_);
lean_inc(v_auxDeclNGen_6115_);
lean_inc(v_ngen_6114_);
lean_inc(v_nextMacroScope_6113_);
lean_inc(v_env_6112_);
lean_dec(v___x_6111_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6173_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6126_; 
v___x_6123_ = l_Lean_Environment_setExporting(v_env_6112_, v_isExporting_6102_);
v___x_6124_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6122_ == 0)
{
lean_ctor_set(v___x_6121_, 5, v___x_6124_);
lean_ctor_set(v___x_6121_, 0, v___x_6123_);
v___x_6126_ = v___x_6121_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6123_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v_nextMacroScope_6113_);
lean_ctor_set(v_reuseFailAlloc_6172_, 2, v_ngen_6114_);
lean_ctor_set(v_reuseFailAlloc_6172_, 3, v_auxDeclNGen_6115_);
lean_ctor_set(v_reuseFailAlloc_6172_, 4, v_traceState_6116_);
lean_ctor_set(v_reuseFailAlloc_6172_, 5, v___x_6124_);
lean_ctor_set(v_reuseFailAlloc_6172_, 6, v_messages_6117_);
lean_ctor_set(v_reuseFailAlloc_6172_, 7, v_infoState_6118_);
lean_ctor_set(v_reuseFailAlloc_6172_, 8, v_snapshotTasks_6119_);
v___x_6126_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v_mctx_6129_; lean_object* v_zetaDeltaFVarIds_6130_; lean_object* v_postponed_6131_; lean_object* v_diag_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6170_; 
v___x_6127_ = lean_st_ref_set(v___y_6106_, v___x_6126_);
v___x_6128_ = lean_st_ref_take(v___y_6104_);
v_mctx_6129_ = lean_ctor_get(v___x_6128_, 0);
v_zetaDeltaFVarIds_6130_ = lean_ctor_get(v___x_6128_, 2);
v_postponed_6131_ = lean_ctor_get(v___x_6128_, 3);
v_diag_6132_ = lean_ctor_get(v___x_6128_, 4);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6170_ == 0)
{
lean_object* v_unused_6171_; 
v_unused_6171_ = lean_ctor_get(v___x_6128_, 1);
lean_dec(v_unused_6171_);
v___x_6134_ = v___x_6128_;
v_isShared_6135_ = v_isSharedCheck_6170_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_diag_6132_);
lean_inc(v_postponed_6131_);
lean_inc(v_zetaDeltaFVarIds_6130_);
lean_inc(v_mctx_6129_);
lean_dec(v___x_6128_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6170_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6136_; lean_object* v___x_6138_; 
v___x_6136_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6135_ == 0)
{
lean_ctor_set(v___x_6134_, 1, v___x_6136_);
v___x_6138_ = v___x_6134_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_mctx_6129_);
lean_ctor_set(v_reuseFailAlloc_6169_, 1, v___x_6136_);
lean_ctor_set(v_reuseFailAlloc_6169_, 2, v_zetaDeltaFVarIds_6130_);
lean_ctor_set(v_reuseFailAlloc_6169_, 3, v_postponed_6131_);
lean_ctor_set(v_reuseFailAlloc_6169_, 4, v_diag_6132_);
v___x_6138_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
lean_object* v___x_6139_; lean_object* v_r_6140_; 
v___x_6139_ = lean_st_ref_set(v___y_6104_, v___x_6138_);
lean_inc(v___y_6106_);
lean_inc_ref(v___y_6105_);
lean_inc(v___y_6104_);
lean_inc_ref(v___y_6103_);
v_r_6140_ = lean_apply_5(v_x_6101_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, lean_box(0));
if (lean_obj_tag(v_r_6140_) == 0)
{
lean_object* v_a_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6157_; 
v_a_6141_ = lean_ctor_get(v_r_6140_, 0);
v_isSharedCheck_6157_ = !lean_is_exclusive(v_r_6140_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6143_ = v_r_6140_;
v_isShared_6144_ = v_isSharedCheck_6157_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_a_6141_);
lean_dec(v_r_6140_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6157_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
lean_object* v___x_6146_; 
lean_inc(v_a_6141_);
if (v_isShared_6144_ == 0)
{
lean_ctor_set_tag(v___x_6143_, 1);
v___x_6146_ = v___x_6143_;
goto v_reusejp_6145_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6141_);
v___x_6146_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6145_;
}
v_reusejp_6145_:
{
lean_object* v___x_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6154_; 
v___x_6147_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6106_, v_isExporting_6110_, v___x_6124_, v___y_6104_, v___x_6136_, v___x_6146_);
lean_dec_ref(v___x_6146_);
v_isSharedCheck_6154_ = !lean_is_exclusive(v___x_6147_);
if (v_isSharedCheck_6154_ == 0)
{
lean_object* v_unused_6155_; 
v_unused_6155_ = lean_ctor_get(v___x_6147_, 0);
lean_dec(v_unused_6155_);
v___x_6149_ = v___x_6147_;
v_isShared_6150_ = v_isSharedCheck_6154_;
goto v_resetjp_6148_;
}
else
{
lean_dec(v___x_6147_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6154_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6152_; 
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 0, v_a_6141_);
v___x_6152_ = v___x_6149_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6153_; 
v_reuseFailAlloc_6153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6153_, 0, v_a_6141_);
v___x_6152_ = v_reuseFailAlloc_6153_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
return v___x_6152_;
}
}
}
}
}
else
{
lean_object* v_a_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
v_a_6158_ = lean_ctor_get(v_r_6140_, 0);
lean_inc(v_a_6158_);
lean_dec_ref(v_r_6140_);
v___x_6159_ = lean_box(0);
v___x_6160_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6106_, v_isExporting_6110_, v___x_6124_, v___y_6104_, v___x_6136_, v___x_6159_);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6160_);
if (v_isSharedCheck_6167_ == 0)
{
lean_object* v_unused_6168_; 
v_unused_6168_ = lean_ctor_get(v___x_6160_, 0);
lean_dec(v_unused_6168_);
v___x_6162_ = v___x_6160_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_dec(v___x_6160_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
lean_ctor_set_tag(v___x_6162_, 1);
lean_ctor_set(v___x_6162_, 0, v_a_6158_);
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6158_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6175_, lean_object* v_isExporting_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
uint8_t v_isExporting_boxed_6182_; lean_object* v_res_6183_; 
v_isExporting_boxed_6182_ = lean_unbox(v_isExporting_6176_);
v_res_6183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6175_, v_isExporting_boxed_6182_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6184_, uint8_t v_when_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_){
_start:
{
if (v_when_6185_ == 0)
{
lean_object* v___x_6191_; 
lean_inc(v___y_6189_);
lean_inc_ref(v___y_6188_);
lean_inc(v___y_6187_);
lean_inc_ref(v___y_6186_);
v___x_6191_ = lean_apply_5(v_x_6184_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, lean_box(0));
return v___x_6191_;
}
else
{
uint8_t v___x_6192_; lean_object* v___x_6193_; 
v___x_6192_ = 0;
v___x_6193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6184_, v___x_6192_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_);
return v___x_6193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6194_, lean_object* v_when_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_){
_start:
{
uint8_t v_when_boxed_6201_; lean_object* v_res_6202_; 
v_when_boxed_6201_ = lean_unbox(v_when_6195_);
v_res_6202_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6194_, v_when_boxed_6201_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
lean_dec(v___y_6199_);
lean_dec_ref(v___y_6198_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6203_, lean_object* v_argsPacker_6204_, lean_object* v_decrTactics_6205_, lean_object* v_value_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_){
_start:
{
lean_object* v___f_6212_; uint8_t v___x_6213_; lean_object* v___x_6214_; 
v___f_6212_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6212_, 0, v_value_6206_);
lean_closure_set(v___f_6212_, 1, v_decrTactics_6205_);
lean_closure_set(v___f_6212_, 2, v_argsPacker_6204_);
lean_closure_set(v___f_6212_, 3, v_funNames_6203_);
v___x_6213_ = 1;
v___x_6214_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6212_, v___x_6213_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6215_, lean_object* v_argsPacker_6216_, lean_object* v_decrTactics_6217_, lean_object* v_value_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_){
_start:
{
lean_object* v_res_6224_; 
v_res_6224_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6215_, v_argsPacker_6216_, v_decrTactics_6217_, v_value_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_);
lean_dec(v_a_6222_);
lean_dec_ref(v_a_6221_);
lean_dec(v_a_6220_);
lean_dec_ref(v_a_6219_);
return v_res_6224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6225_, lean_object* v_msg_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
lean_object* v___x_6234_; 
v___x_6234_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
return v___x_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6235_, lean_object* v_msg_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_){
_start:
{
lean_object* v_res_6244_; 
v_res_6244_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6235_, v_msg_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_);
lean_dec(v___y_6242_);
lean_dec_ref(v___y_6241_);
lean_dec(v___y_6240_);
lean_dec_ref(v___y_6239_);
lean_dec(v___y_6238_);
lean_dec_ref(v___y_6237_);
return v_res_6244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
lean_object* v___x_6254_; 
v___x_6254_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6252_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_){
_start:
{
lean_object* v_res_6264_; 
v_res_6264_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
lean_dec(v___y_6262_);
lean_dec_ref(v___y_6261_);
lean_dec(v___y_6260_);
lean_dec_ref(v___y_6259_);
lean_dec(v___y_6258_);
lean_dec_ref(v___y_6257_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
return v_res_6264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6265_, lean_object* v_x_6266_, lean_object* v_mkInfoTree_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v___x_6277_; 
v___x_6277_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6266_, v_mkInfoTree_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
return v___x_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6278_, lean_object* v_x_6279_, lean_object* v_mkInfoTree_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_){
_start:
{
lean_object* v_res_6290_; 
v_res_6290_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6278_, v_x_6279_, v_mkInfoTree_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
lean_dec(v___y_6288_);
lean_dec_ref(v___y_6287_);
lean_dec(v___y_6286_);
lean_dec_ref(v___y_6285_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6282_);
lean_dec_ref(v___y_6281_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6291_, size_t v_i_6292_, size_t v_stop_6293_, lean_object* v_b_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6291_, v_i_6292_, v_stop_6293_, v_b_6294_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6303_, lean_object* v_i_6304_, lean_object* v_stop_6305_, lean_object* v_b_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_){
_start:
{
size_t v_i_boxed_6314_; size_t v_stop_boxed_6315_; lean_object* v_res_6316_; 
v_i_boxed_6314_ = lean_unbox_usize(v_i_6304_);
lean_dec(v_i_6304_);
v_stop_boxed_6315_ = lean_unbox_usize(v_stop_6305_);
lean_dec(v_stop_6305_);
v_res_6316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6303_, v_i_boxed_6314_, v_stop_boxed_6315_, v_b_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_, v___y_6311_, v___y_6312_);
lean_dec(v___y_6312_);
lean_dec_ref(v___y_6311_);
lean_dec(v___y_6310_);
lean_dec_ref(v___y_6309_);
lean_dec(v___y_6308_);
lean_dec_ref(v___y_6307_);
lean_dec_ref(v_as_6303_);
return v_res_6316_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6317_, lean_object* v_x_6318_, uint8_t v_isExporting_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6318_, v_isExporting_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6326_, lean_object* v_x_6327_, lean_object* v_isExporting_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_){
_start:
{
uint8_t v_isExporting_boxed_6334_; lean_object* v_res_6335_; 
v_isExporting_boxed_6334_ = lean_unbox(v_isExporting_6328_);
v_res_6335_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6326_, v_x_6327_, v_isExporting_boxed_6334_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_);
lean_dec(v___y_6332_);
lean_dec_ref(v___y_6331_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
return v_res_6335_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6336_, lean_object* v_x_6337_, uint8_t v_when_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_){
_start:
{
lean_object* v___x_6344_; 
v___x_6344_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6337_, v_when_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_);
return v___x_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6345_, lean_object* v_x_6346_, lean_object* v_when_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_){
_start:
{
uint8_t v_when_boxed_6353_; lean_object* v_res_6354_; 
v_when_boxed_6353_ = lean_unbox(v_when_6347_);
v_res_6354_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6345_, v_x_6346_, v_when_boxed_6353_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_);
lean_dec(v___y_6351_);
lean_dec_ref(v___y_6350_);
lean_dec(v___y_6349_);
lean_dec_ref(v___y_6348_);
return v_res_6354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6355_, lean_object* v_macroStack_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_){
_start:
{
lean_object* v___x_6364_; 
v___x_6364_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6355_, v_macroStack_6356_, v___y_6361_);
return v___x_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6365_, lean_object* v_macroStack_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_){
_start:
{
lean_object* v_res_6374_; 
v_res_6374_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6365_, v_macroStack_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_);
lean_dec(v___y_6372_);
lean_dec_ref(v___y_6371_);
lean_dec(v___y_6370_);
lean_dec_ref(v___y_6369_);
lean_dec(v___y_6368_);
lean_dec_ref(v___y_6367_);
return v_res_6374_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6381_ = lean_box(0);
v___x_6382_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6383_ = l_Lean_mkConst(v___x_6382_, v___x_6381_);
return v___x_6383_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6388_ = lean_box(0);
v___x_6389_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6390_ = l_Lean_mkConst(v___x_6389_, v___x_6388_);
return v___x_6390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_){
_start:
{
lean_object* v___x_6397_; 
v___x_6397_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6391_, v_a_6393_);
if (lean_obj_tag(v___x_6397_) == 0)
{
lean_object* v_a_6398_; lean_object* v___x_6400_; uint8_t v_isShared_6401_; uint8_t v_isSharedCheck_6465_; 
v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6397_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6400_ = v___x_6397_;
v_isShared_6401_ = v_isSharedCheck_6465_;
goto v_resetjp_6399_;
}
else
{
lean_inc(v_a_6398_);
lean_dec(v___x_6397_);
v___x_6400_ = lean_box(0);
v_isShared_6401_ = v_isSharedCheck_6465_;
goto v_resetjp_6399_;
}
v_resetjp_6399_:
{
lean_object* v___x_6407_; uint8_t v___x_6408_; 
v___x_6407_ = l_Lean_Expr_cleanupAnnotations(v_a_6398_);
v___x_6408_ = l_Lean_Expr_isApp(v___x_6407_);
if (v___x_6408_ == 0)
{
lean_dec_ref(v___x_6407_);
goto v___jp_6402_;
}
else
{
lean_object* v_arg_6409_; lean_object* v___x_6410_; uint8_t v___x_6411_; 
v_arg_6409_ = lean_ctor_get(v___x_6407_, 1);
lean_inc_ref(v_arg_6409_);
v___x_6410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6407_);
v___x_6411_ = l_Lean_Expr_isApp(v___x_6410_);
if (v___x_6411_ == 0)
{
lean_dec_ref(v___x_6410_);
lean_dec_ref(v_arg_6409_);
goto v___jp_6402_;
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
lean_dec_ref(v_arg_6409_);
goto v___jp_6402_;
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
lean_dec_ref(v_arg_6409_);
goto v___jp_6402_;
}
else
{
lean_object* v___x_6418_; lean_object* v___x_6419_; uint8_t v___x_6420_; 
v___x_6418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6416_);
v___x_6419_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6420_ = l_Lean_Expr_isConstOf(v___x_6418_, v___x_6419_);
lean_dec_ref(v___x_6418_);
if (v___x_6420_ == 0)
{
lean_dec_ref(v_arg_6415_);
lean_dec_ref(v_arg_6412_);
lean_dec_ref(v_arg_6409_);
goto v___jp_6402_;
}
else
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
lean_del_object(v___x_6400_);
v___x_6421_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6422_ = l_Lean_Meta_isExprDefEq(v_arg_6415_, v___x_6421_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_);
if (lean_obj_tag(v___x_6422_) == 0)
{
lean_object* v_a_6423_; lean_object* v___x_6425_; uint8_t v_isShared_6426_; uint8_t v_isSharedCheck_6456_; 
v_a_6423_ = lean_ctor_get(v___x_6422_, 0);
v_isSharedCheck_6456_ = !lean_is_exclusive(v___x_6422_);
if (v_isSharedCheck_6456_ == 0)
{
v___x_6425_ = v___x_6422_;
v_isShared_6426_ = v_isSharedCheck_6456_;
goto v_resetjp_6424_;
}
else
{
lean_inc(v_a_6423_);
lean_dec(v___x_6422_);
v___x_6425_ = lean_box(0);
v_isShared_6426_ = v_isSharedCheck_6456_;
goto v_resetjp_6424_;
}
v_resetjp_6424_:
{
uint8_t v___x_6427_; 
v___x_6427_ = lean_unbox(v_a_6423_);
lean_dec(v_a_6423_);
if (v___x_6427_ == 0)
{
lean_object* v___x_6428_; lean_object* v___x_6430_; 
lean_dec_ref(v_arg_6412_);
lean_dec_ref(v_arg_6409_);
v___x_6428_ = lean_box(0);
if (v_isShared_6426_ == 0)
{
lean_ctor_set(v___x_6425_, 0, v___x_6428_);
v___x_6430_ = v___x_6425_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6431_; 
v_reuseFailAlloc_6431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6431_, 0, v___x_6428_);
v___x_6430_ = v_reuseFailAlloc_6431_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
return v___x_6430_;
}
}
else
{
lean_object* v___x_6432_; lean_object* v___x_6433_; 
lean_del_object(v___x_6425_);
v___x_6432_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6433_ = l_Lean_Meta_isExprDefEq(v_arg_6409_, v___x_6432_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_);
if (lean_obj_tag(v___x_6433_) == 0)
{
lean_object* v_a_6434_; lean_object* v___x_6436_; uint8_t v_isShared_6437_; uint8_t v_isSharedCheck_6447_; 
v_a_6434_ = lean_ctor_get(v___x_6433_, 0);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___x_6433_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6436_ = v___x_6433_;
v_isShared_6437_ = v_isSharedCheck_6447_;
goto v_resetjp_6435_;
}
else
{
lean_inc(v_a_6434_);
lean_dec(v___x_6433_);
v___x_6436_ = lean_box(0);
v_isShared_6437_ = v_isSharedCheck_6447_;
goto v_resetjp_6435_;
}
v_resetjp_6435_:
{
uint8_t v___x_6438_; 
v___x_6438_ = lean_unbox(v_a_6434_);
lean_dec(v_a_6434_);
if (v___x_6438_ == 0)
{
lean_object* v___x_6439_; lean_object* v___x_6441_; 
lean_dec_ref(v_arg_6412_);
v___x_6439_ = lean_box(0);
if (v_isShared_6437_ == 0)
{
lean_ctor_set(v___x_6436_, 0, v___x_6439_);
v___x_6441_ = v___x_6436_;
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
else
{
lean_object* v___x_6443_; lean_object* v___x_6445_; 
v___x_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6443_, 0, v_arg_6412_);
if (v_isShared_6437_ == 0)
{
lean_ctor_set(v___x_6436_, 0, v___x_6443_);
v___x_6445_ = v___x_6436_;
goto v_reusejp_6444_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v___x_6443_);
v___x_6445_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6444_;
}
v_reusejp_6444_:
{
return v___x_6445_;
}
}
}
}
else
{
lean_object* v_a_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6455_; 
lean_dec_ref(v_arg_6412_);
v_a_6448_ = lean_ctor_get(v___x_6433_, 0);
v_isSharedCheck_6455_ = !lean_is_exclusive(v___x_6433_);
if (v_isSharedCheck_6455_ == 0)
{
v___x_6450_ = v___x_6433_;
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_a_6448_);
lean_dec(v___x_6433_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
lean_object* v___x_6453_; 
if (v_isShared_6451_ == 0)
{
v___x_6453_ = v___x_6450_;
goto v_reusejp_6452_;
}
else
{
lean_object* v_reuseFailAlloc_6454_; 
v_reuseFailAlloc_6454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_a_6448_);
v___x_6453_ = v_reuseFailAlloc_6454_;
goto v_reusejp_6452_;
}
v_reusejp_6452_:
{
return v___x_6453_;
}
}
}
}
}
}
else
{
lean_object* v_a_6457_; lean_object* v___x_6459_; uint8_t v_isShared_6460_; uint8_t v_isSharedCheck_6464_; 
lean_dec_ref(v_arg_6412_);
lean_dec_ref(v_arg_6409_);
v_a_6457_ = lean_ctor_get(v___x_6422_, 0);
v_isSharedCheck_6464_ = !lean_is_exclusive(v___x_6422_);
if (v_isSharedCheck_6464_ == 0)
{
v___x_6459_ = v___x_6422_;
v_isShared_6460_ = v_isSharedCheck_6464_;
goto v_resetjp_6458_;
}
else
{
lean_inc(v_a_6457_);
lean_dec(v___x_6422_);
v___x_6459_ = lean_box(0);
v_isShared_6460_ = v_isSharedCheck_6464_;
goto v_resetjp_6458_;
}
v_resetjp_6458_:
{
lean_object* v___x_6462_; 
if (v_isShared_6460_ == 0)
{
v___x_6462_ = v___x_6459_;
goto v_reusejp_6461_;
}
else
{
lean_object* v_reuseFailAlloc_6463_; 
v_reuseFailAlloc_6463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6463_, 0, v_a_6457_);
v___x_6462_ = v_reuseFailAlloc_6463_;
goto v_reusejp_6461_;
}
v_reusejp_6461_:
{
return v___x_6462_;
}
}
}
}
}
}
}
}
v___jp_6402_:
{
lean_object* v___x_6403_; lean_object* v___x_6405_; 
v___x_6403_ = lean_box(0);
if (v_isShared_6401_ == 0)
{
lean_ctor_set(v___x_6400_, 0, v___x_6403_);
v___x_6405_ = v___x_6400_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v___x_6403_);
v___x_6405_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
return v___x_6405_;
}
}
}
}
else
{
lean_object* v_a_6466_; lean_object* v___x_6468_; uint8_t v_isShared_6469_; uint8_t v_isSharedCheck_6473_; 
v_a_6466_ = lean_ctor_get(v___x_6397_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6397_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6468_ = v___x_6397_;
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
else
{
lean_inc(v_a_6466_);
lean_dec(v___x_6397_);
v___x_6468_ = lean_box(0);
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
v_resetjp_6467_:
{
lean_object* v___x_6471_; 
if (v_isShared_6469_ == 0)
{
v___x_6471_ = v___x_6468_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
return v___x_6471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6474_, lean_object* v_a_6475_, lean_object* v_a_6476_, lean_object* v_a_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_){
_start:
{
lean_object* v_res_6480_; 
v_res_6480_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_);
lean_dec(v_a_6478_);
lean_dec_ref(v_a_6477_);
lean_dec(v_a_6476_);
lean_dec_ref(v_a_6475_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6481_, lean_object* v_maxFVars_x3f_6482_, lean_object* v_k_6483_, uint8_t v_cleanupAnnotations_6484_, uint8_t v_whnfType_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_){
_start:
{
lean_object* v___f_6493_; lean_object* v___x_6494_; 
lean_inc(v___y_6487_);
lean_inc_ref(v___y_6486_);
v___f_6493_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6493_, 0, v_k_6483_);
lean_closure_set(v___f_6493_, 1, v___y_6486_);
lean_closure_set(v___f_6493_, 2, v___y_6487_);
v___x_6494_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6481_, v_maxFVars_x3f_6482_, v___f_6493_, v_cleanupAnnotations_6484_, v_whnfType_6485_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
if (lean_obj_tag(v___x_6494_) == 0)
{
return v___x_6494_;
}
else
{
lean_object* v_a_6495_; lean_object* v___x_6497_; uint8_t v_isShared_6498_; uint8_t v_isSharedCheck_6502_; 
v_a_6495_ = lean_ctor_get(v___x_6494_, 0);
v_isSharedCheck_6502_ = !lean_is_exclusive(v___x_6494_);
if (v_isSharedCheck_6502_ == 0)
{
v___x_6497_ = v___x_6494_;
v_isShared_6498_ = v_isSharedCheck_6502_;
goto v_resetjp_6496_;
}
else
{
lean_inc(v_a_6495_);
lean_dec(v___x_6494_);
v___x_6497_ = lean_box(0);
v_isShared_6498_ = v_isSharedCheck_6502_;
goto v_resetjp_6496_;
}
v_resetjp_6496_:
{
lean_object* v___x_6500_; 
if (v_isShared_6498_ == 0)
{
v___x_6500_ = v___x_6497_;
goto v_reusejp_6499_;
}
else
{
lean_object* v_reuseFailAlloc_6501_; 
v_reuseFailAlloc_6501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6501_, 0, v_a_6495_);
v___x_6500_ = v_reuseFailAlloc_6501_;
goto v_reusejp_6499_;
}
v_reusejp_6499_:
{
return v___x_6500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6503_, lean_object* v_maxFVars_x3f_6504_, lean_object* v_k_6505_, lean_object* v_cleanupAnnotations_6506_, lean_object* v_whnfType_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6515_; uint8_t v_whnfType_boxed_6516_; lean_object* v_res_6517_; 
v_cleanupAnnotations_boxed_6515_ = lean_unbox(v_cleanupAnnotations_6506_);
v_whnfType_boxed_6516_ = lean_unbox(v_whnfType_6507_);
v_res_6517_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6503_, v_maxFVars_x3f_6504_, v_k_6505_, v_cleanupAnnotations_boxed_6515_, v_whnfType_boxed_6516_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6512_);
lean_dec(v___y_6511_);
lean_dec_ref(v___y_6510_);
lean_dec(v___y_6509_);
lean_dec_ref(v___y_6508_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6518_, lean_object* v_type_6519_, lean_object* v_maxFVars_x3f_6520_, lean_object* v_k_6521_, uint8_t v_cleanupAnnotations_6522_, uint8_t v_whnfType_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_){
_start:
{
lean_object* v___x_6531_; 
v___x_6531_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6519_, v_maxFVars_x3f_6520_, v_k_6521_, v_cleanupAnnotations_6522_, v_whnfType_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_);
return v___x_6531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6532_, lean_object* v_type_6533_, lean_object* v_maxFVars_x3f_6534_, lean_object* v_k_6535_, lean_object* v_cleanupAnnotations_6536_, lean_object* v_whnfType_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6545_; uint8_t v_whnfType_boxed_6546_; lean_object* v_res_6547_; 
v_cleanupAnnotations_boxed_6545_ = lean_unbox(v_cleanupAnnotations_6536_);
v_whnfType_boxed_6546_ = lean_unbox(v_whnfType_6537_);
v_res_6547_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6532_, v_type_6533_, v_maxFVars_x3f_6534_, v_k_6535_, v_cleanupAnnotations_boxed_6545_, v_whnfType_boxed_6546_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_);
lean_dec(v___y_6543_);
lean_dec_ref(v___y_6542_);
lean_dec(v___y_6541_);
lean_dec_ref(v___y_6540_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
return v_res_6547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6548_, lean_object* v_x_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_){
_start:
{
lean_object* v_keyedConfig_6557_; uint8_t v_trackZetaDelta_6558_; lean_object* v_zetaDeltaSet_6559_; lean_object* v_localInstances_6560_; lean_object* v_defEqCtx_x3f_6561_; lean_object* v_synthPendingDepth_6562_; lean_object* v_canUnfold_x3f_6563_; uint8_t v_univApprox_6564_; uint8_t v_inTypeClassResolution_6565_; uint8_t v_cacheInferType_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; 
v_keyedConfig_6557_ = lean_ctor_get(v___y_6552_, 0);
v_trackZetaDelta_6558_ = lean_ctor_get_uint8(v___y_6552_, sizeof(void*)*7);
v_zetaDeltaSet_6559_ = lean_ctor_get(v___y_6552_, 1);
v_localInstances_6560_ = lean_ctor_get(v___y_6552_, 3);
v_defEqCtx_x3f_6561_ = lean_ctor_get(v___y_6552_, 4);
v_synthPendingDepth_6562_ = lean_ctor_get(v___y_6552_, 5);
v_canUnfold_x3f_6563_ = lean_ctor_get(v___y_6552_, 6);
v_univApprox_6564_ = lean_ctor_get_uint8(v___y_6552_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6565_ = lean_ctor_get_uint8(v___y_6552_, sizeof(void*)*7 + 2);
v_cacheInferType_6566_ = lean_ctor_get_uint8(v___y_6552_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_6563_);
lean_inc(v_synthPendingDepth_6562_);
lean_inc(v_defEqCtx_x3f_6561_);
lean_inc_ref(v_localInstances_6560_);
lean_inc(v_zetaDeltaSet_6559_);
lean_inc_ref(v_keyedConfig_6557_);
v___x_6567_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6567_, 0, v_keyedConfig_6557_);
lean_ctor_set(v___x_6567_, 1, v_zetaDeltaSet_6559_);
lean_ctor_set(v___x_6567_, 2, v_lctx_6548_);
lean_ctor_set(v___x_6567_, 3, v_localInstances_6560_);
lean_ctor_set(v___x_6567_, 4, v_defEqCtx_x3f_6561_);
lean_ctor_set(v___x_6567_, 5, v_synthPendingDepth_6562_);
lean_ctor_set(v___x_6567_, 6, v_canUnfold_x3f_6563_);
lean_ctor_set_uint8(v___x_6567_, sizeof(void*)*7, v_trackZetaDelta_6558_);
lean_ctor_set_uint8(v___x_6567_, sizeof(void*)*7 + 1, v_univApprox_6564_);
lean_ctor_set_uint8(v___x_6567_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6565_);
lean_ctor_set_uint8(v___x_6567_, sizeof(void*)*7 + 3, v_cacheInferType_6566_);
lean_inc(v___y_6555_);
lean_inc_ref(v___y_6554_);
lean_inc(v___y_6553_);
lean_inc(v___y_6551_);
lean_inc_ref(v___y_6550_);
v___x_6568_ = lean_apply_7(v_x_6549_, v___y_6550_, v___y_6551_, v___x_6567_, v___y_6553_, v___y_6554_, v___y_6555_, lean_box(0));
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6576_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6571_ = v___x_6568_;
v_isShared_6572_ = v_isSharedCheck_6576_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v___x_6568_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6576_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v___x_6574_; 
if (v_isShared_6572_ == 0)
{
v___x_6574_ = v___x_6571_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6569_);
v___x_6574_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
return v___x_6574_;
}
}
}
else
{
return v___x_6568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6577_, lean_object* v_x_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_, lean_object* v___y_6584_, lean_object* v___y_6585_){
_start:
{
lean_object* v_res_6586_; 
v_res_6586_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6577_, v_x_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_, v___y_6584_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec(v___y_6580_);
lean_dec_ref(v___y_6579_);
return v_res_6586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6587_, lean_object* v_lctx_6588_, lean_object* v_x_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_){
_start:
{
lean_object* v___x_6597_; 
v___x_6597_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6588_, v_x_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_);
return v___x_6597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6598_, lean_object* v_lctx_6599_, lean_object* v_x_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_){
_start:
{
lean_object* v_res_6608_; 
v_res_6608_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6598_, v_lctx_6599_, v_x_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_);
lean_dec(v___y_6606_);
lean_dec_ref(v___y_6605_);
lean_dec(v___y_6604_);
lean_dec_ref(v___y_6603_);
lean_dec(v___y_6602_);
lean_dec_ref(v___y_6601_);
return v_res_6608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6625_, lean_object* v___x_6626_, lean_object* v_wfRel_6627_, lean_object* v_x_6628_, lean_object* v_type_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_){
_start:
{
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; 
v___x_6637_ = lean_unsigned_to_nat(0u);
v___x_6638_ = lean_array_get_borrowed(v___x_6625_, v_x_6628_, v___x_6637_);
v___x_6639_ = l_Lean_Expr_fvarId_x21(v___x_6638_);
v___x_6640_ = l_Lean_FVarId_getUserName___redArg(v___x_6639_, v___y_6632_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6640_) == 0)
{
lean_object* v_a_6641_; lean_object* v___x_6642_; 
v_a_6641_ = lean_ctor_get(v___x_6640_, 0);
lean_inc(v_a_6641_);
lean_dec_ref(v___x_6640_);
lean_inc(v___y_6635_);
lean_inc_ref(v___y_6634_);
lean_inc(v___y_6633_);
lean_inc_ref(v___y_6632_);
lean_inc(v___x_6638_);
v___x_6642_ = lean_infer_type(v___x_6638_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v___x_6644_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
lean_inc_n(v_a_6643_, 2);
lean_dec_ref(v___x_6642_);
v___x_6644_ = l_Lean_Meta_getLevel(v_a_6643_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6644_) == 0)
{
lean_object* v_a_6645_; lean_object* v___x_6646_; 
v_a_6645_ = lean_ctor_get(v___x_6644_, 0);
lean_inc(v_a_6645_);
lean_dec_ref(v___x_6644_);
lean_inc_ref(v_type_6629_);
v___x_6646_ = l_Lean_Meta_getLevel(v_type_6629_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6646_) == 0)
{
lean_object* v_a_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; uint8_t v___x_6650_; uint8_t v___x_6651_; uint8_t v___x_6652_; lean_object* v___x_6653_; 
v_a_6647_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_a_6647_);
lean_dec_ref(v___x_6646_);
v___x_6648_ = lean_mk_empty_array_with_capacity(v___x_6626_);
lean_inc(v___x_6638_);
lean_inc_ref(v___x_6648_);
v___x_6649_ = lean_array_push(v___x_6648_, v___x_6638_);
v___x_6650_ = 0;
v___x_6651_ = 1;
v___x_6652_ = 1;
v___x_6653_ = l_Lean_Meta_mkLambdaFVars(v___x_6649_, v_type_6629_, v___x_6650_, v___x_6651_, v___x_6650_, v___x_6651_, v___x_6652_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
lean_dec_ref(v___x_6649_);
if (lean_obj_tag(v___x_6653_) == 0)
{
lean_object* v_a_6654_; lean_object* v___x_6655_; 
v_a_6654_ = lean_ctor_get(v___x_6653_, 0);
lean_inc(v_a_6654_);
lean_dec_ref(v___x_6653_);
lean_inc_ref(v_wfRel_6627_);
v___x_6655_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6627_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6655_) == 0)
{
lean_object* v_a_6656_; lean_object* v___x_6658_; uint8_t v_isShared_6659_; uint8_t v_isSharedCheck_6700_; 
v_a_6656_ = lean_ctor_get(v___x_6655_, 0);
v_isSharedCheck_6700_ = !lean_is_exclusive(v___x_6655_);
if (v_isSharedCheck_6700_ == 0)
{
v___x_6658_ = v___x_6655_;
v_isShared_6659_ = v_isSharedCheck_6700_;
goto v_resetjp_6657_;
}
else
{
lean_inc(v_a_6656_);
lean_dec(v___x_6655_);
v___x_6658_ = lean_box(0);
v_isShared_6659_ = v_isSharedCheck_6700_;
goto v_resetjp_6657_;
}
v_resetjp_6657_:
{
if (lean_obj_tag(v_a_6656_) == 1)
{
lean_object* v_val_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6669_; 
lean_dec_ref(v___x_6648_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_val_6660_ = lean_ctor_get(v_a_6656_, 0);
lean_inc(v_val_6660_);
lean_dec_ref(v_a_6656_);
v___x_6661_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6662_ = lean_box(0);
v___x_6663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6663_, 0, v_a_6647_);
lean_ctor_set(v___x_6663_, 1, v___x_6662_);
v___x_6664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6664_, 0, v_a_6645_);
lean_ctor_set(v___x_6664_, 1, v___x_6663_);
v___x_6665_ = l_Lean_mkConst(v___x_6661_, v___x_6664_);
v___x_6666_ = l_Lean_mkApp3(v___x_6665_, v_a_6643_, v_a_6654_, v_val_6660_);
v___x_6667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6667_, 0, v___x_6666_);
lean_ctor_set(v___x_6667_, 1, v_a_6641_);
if (v_isShared_6659_ == 0)
{
lean_ctor_set(v___x_6658_, 0, v___x_6667_);
v___x_6669_ = v___x_6658_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___x_6667_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
else
{
lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; 
lean_del_object(v___x_6658_);
lean_dec(v_a_6656_);
v___x_6671_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6627_);
v___x_6672_ = l_Lean_mkProj(v___x_6671_, v___x_6637_, v_wfRel_6627_);
v___x_6673_ = l_Lean_mkProj(v___x_6671_, v___x_6626_, v_wfRel_6627_);
v___x_6674_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6675_ = lean_array_push(v___x_6648_, v___x_6673_);
v___x_6676_ = l_Lean_Meta_mkAppM(v___x_6674_, v___x_6675_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
if (lean_obj_tag(v___x_6676_) == 0)
{
lean_object* v_a_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6691_; 
v_a_6677_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6691_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6691_ == 0)
{
v___x_6679_ = v___x_6676_;
v_isShared_6680_ = v_isSharedCheck_6691_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_a_6677_);
lean_dec(v___x_6676_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6691_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6689_; 
v___x_6681_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6682_ = lean_box(0);
v___x_6683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6683_, 0, v_a_6647_);
lean_ctor_set(v___x_6683_, 1, v___x_6682_);
v___x_6684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6684_, 0, v_a_6645_);
lean_ctor_set(v___x_6684_, 1, v___x_6683_);
v___x_6685_ = l_Lean_mkConst(v___x_6681_, v___x_6684_);
v___x_6686_ = l_Lean_mkApp4(v___x_6685_, v_a_6643_, v_a_6654_, v___x_6672_, v_a_6677_);
v___x_6687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6687_, 0, v___x_6686_);
lean_ctor_set(v___x_6687_, 1, v_a_6641_);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6687_);
v___x_6689_ = v___x_6679_;
goto v_reusejp_6688_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v___x_6687_);
v___x_6689_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6688_;
}
v_reusejp_6688_:
{
return v___x_6689_;
}
}
}
else
{
lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6699_; 
lean_dec_ref(v___x_6672_);
lean_dec(v_a_6654_);
lean_dec(v_a_6647_);
lean_dec(v_a_6645_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
v_a_6692_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6699_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6699_ == 0)
{
v___x_6694_ = v___x_6676_;
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_dec(v___x_6676_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v___x_6697_; 
if (v_isShared_6695_ == 0)
{
v___x_6697_ = v___x_6694_;
goto v_reusejp_6696_;
}
else
{
lean_object* v_reuseFailAlloc_6698_; 
v_reuseFailAlloc_6698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6698_, 0, v_a_6692_);
v___x_6697_ = v_reuseFailAlloc_6698_;
goto v_reusejp_6696_;
}
v_reusejp_6696_:
{
return v___x_6697_;
}
}
}
}
}
}
else
{
lean_object* v_a_6701_; lean_object* v___x_6703_; uint8_t v_isShared_6704_; uint8_t v_isSharedCheck_6708_; 
lean_dec(v_a_6654_);
lean_dec_ref(v___x_6648_);
lean_dec(v_a_6647_);
lean_dec(v_a_6645_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6701_ = lean_ctor_get(v___x_6655_, 0);
v_isSharedCheck_6708_ = !lean_is_exclusive(v___x_6655_);
if (v_isSharedCheck_6708_ == 0)
{
v___x_6703_ = v___x_6655_;
v_isShared_6704_ = v_isSharedCheck_6708_;
goto v_resetjp_6702_;
}
else
{
lean_inc(v_a_6701_);
lean_dec(v___x_6655_);
v___x_6703_ = lean_box(0);
v_isShared_6704_ = v_isSharedCheck_6708_;
goto v_resetjp_6702_;
}
v_resetjp_6702_:
{
lean_object* v___x_6706_; 
if (v_isShared_6704_ == 0)
{
v___x_6706_ = v___x_6703_;
goto v_reusejp_6705_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v_a_6701_);
v___x_6706_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6705_;
}
v_reusejp_6705_:
{
return v___x_6706_;
}
}
}
}
else
{
lean_object* v_a_6709_; lean_object* v___x_6711_; uint8_t v_isShared_6712_; uint8_t v_isSharedCheck_6716_; 
lean_dec_ref(v___x_6648_);
lean_dec(v_a_6647_);
lean_dec(v_a_6645_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6709_ = lean_ctor_get(v___x_6653_, 0);
v_isSharedCheck_6716_ = !lean_is_exclusive(v___x_6653_);
if (v_isSharedCheck_6716_ == 0)
{
v___x_6711_ = v___x_6653_;
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
else
{
lean_inc(v_a_6709_);
lean_dec(v___x_6653_);
v___x_6711_ = lean_box(0);
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
v_resetjp_6710_:
{
lean_object* v___x_6714_; 
if (v_isShared_6712_ == 0)
{
v___x_6714_ = v___x_6711_;
goto v_reusejp_6713_;
}
else
{
lean_object* v_reuseFailAlloc_6715_; 
v_reuseFailAlloc_6715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_a_6709_);
v___x_6714_ = v_reuseFailAlloc_6715_;
goto v_reusejp_6713_;
}
v_reusejp_6713_:
{
return v___x_6714_;
}
}
}
}
else
{
lean_object* v_a_6717_; lean_object* v___x_6719_; uint8_t v_isShared_6720_; uint8_t v_isSharedCheck_6724_; 
lean_dec(v_a_6645_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec_ref(v_type_6629_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6717_ = lean_ctor_get(v___x_6646_, 0);
v_isSharedCheck_6724_ = !lean_is_exclusive(v___x_6646_);
if (v_isSharedCheck_6724_ == 0)
{
v___x_6719_ = v___x_6646_;
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_a_6717_);
lean_dec(v___x_6646_);
v___x_6719_ = lean_box(0);
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
v_resetjp_6718_:
{
lean_object* v___x_6722_; 
if (v_isShared_6720_ == 0)
{
v___x_6722_ = v___x_6719_;
goto v_reusejp_6721_;
}
else
{
lean_object* v_reuseFailAlloc_6723_; 
v_reuseFailAlloc_6723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6723_, 0, v_a_6717_);
v___x_6722_ = v_reuseFailAlloc_6723_;
goto v_reusejp_6721_;
}
v_reusejp_6721_:
{
return v___x_6722_;
}
}
}
}
else
{
lean_object* v_a_6725_; lean_object* v___x_6727_; uint8_t v_isShared_6728_; uint8_t v_isSharedCheck_6732_; 
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec_ref(v_type_6629_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6725_ = lean_ctor_get(v___x_6644_, 0);
v_isSharedCheck_6732_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6732_ == 0)
{
v___x_6727_ = v___x_6644_;
v_isShared_6728_ = v_isSharedCheck_6732_;
goto v_resetjp_6726_;
}
else
{
lean_inc(v_a_6725_);
lean_dec(v___x_6644_);
v___x_6727_ = lean_box(0);
v_isShared_6728_ = v_isSharedCheck_6732_;
goto v_resetjp_6726_;
}
v_resetjp_6726_:
{
lean_object* v___x_6730_; 
if (v_isShared_6728_ == 0)
{
v___x_6730_ = v___x_6727_;
goto v_reusejp_6729_;
}
else
{
lean_object* v_reuseFailAlloc_6731_; 
v_reuseFailAlloc_6731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_a_6725_);
v___x_6730_ = v_reuseFailAlloc_6731_;
goto v_reusejp_6729_;
}
v_reusejp_6729_:
{
return v___x_6730_;
}
}
}
}
else
{
lean_object* v_a_6733_; lean_object* v___x_6735_; uint8_t v_isShared_6736_; uint8_t v_isSharedCheck_6740_; 
lean_dec(v_a_6641_);
lean_dec_ref(v_type_6629_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6733_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6740_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6740_ == 0)
{
v___x_6735_ = v___x_6642_;
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
else
{
lean_inc(v_a_6733_);
lean_dec(v___x_6642_);
v___x_6735_ = lean_box(0);
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
v_resetjp_6734_:
{
lean_object* v___x_6738_; 
if (v_isShared_6736_ == 0)
{
v___x_6738_ = v___x_6735_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_a_6733_);
v___x_6738_ = v_reuseFailAlloc_6739_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
return v___x_6738_;
}
}
}
}
else
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6748_; 
lean_dec_ref(v_type_6629_);
lean_dec_ref(v_wfRel_6627_);
lean_dec(v___x_6626_);
v_a_6741_ = lean_ctor_get(v___x_6640_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v___x_6640_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6743_ = v___x_6640_;
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v___x_6640_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___x_6746_; 
if (v_isShared_6744_ == 0)
{
v___x_6746_ = v___x_6743_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6741_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6749_, lean_object* v___x_6750_, lean_object* v_wfRel_6751_, lean_object* v_x_6752_, lean_object* v_type_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_){
_start:
{
lean_object* v_res_6761_; 
v_res_6761_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6749_, v___x_6750_, v_wfRel_6751_, v_x_6752_, v_type_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_);
lean_dec(v___y_6759_);
lean_dec_ref(v___y_6758_);
lean_dec(v___y_6757_);
lean_dec_ref(v___y_6756_);
lean_dec(v___y_6755_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v_x_6752_);
lean_dec_ref(v___x_6749_);
return v_res_6761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6762_, lean_object* v_declName_6763_, lean_object* v_x_6764_, lean_object* v_F_6765_, lean_object* v_val_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_){
_start:
{
lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; 
v___x_6774_ = lean_array_get_size(v_prefixArgs_6762_);
v___x_6775_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6775_, 0, v_declName_6763_);
lean_closure_set(v___x_6775_, 1, v___x_6774_);
v___x_6776_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6764_, v_F_6765_, v_val_6766_, v___x_6775_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
return v___x_6776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6777_, lean_object* v_declName_6778_, lean_object* v_x_6779_, lean_object* v_F_6780_, lean_object* v_val_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_){
_start:
{
lean_object* v_res_6789_; 
v_res_6789_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6777_, v_declName_6778_, v_x_6779_, v_F_6780_, v_val_6781_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_, v___y_6787_);
lean_dec(v___y_6787_);
lean_dec_ref(v___y_6786_);
lean_dec(v___y_6785_);
lean_dec_ref(v___y_6784_);
lean_dec(v___y_6783_);
lean_dec_ref(v___y_6782_);
lean_dec_ref(v_prefixArgs_6777_);
return v_res_6789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6790_, lean_object* v___x_6791_, lean_object* v___x_6792_, lean_object* v___f_6793_, lean_object* v_funNames_6794_, lean_object* v_argsPacker_6795_, lean_object* v_decrTactics_6796_, uint8_t v___x_6797_, lean_object* v_fst_6798_, lean_object* v_prefixArgs_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_){
_start:
{
lean_object* v___x_6807_; 
lean_inc_ref(v___x_6791_);
lean_inc_ref(v___x_6790_);
v___x_6807_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6790_, v___x_6791_, v___x_6792_, v___f_6793_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_);
if (lean_obj_tag(v___x_6807_) == 0)
{
lean_object* v_a_6808_; lean_object* v___x_6809_; 
v_a_6808_ = lean_ctor_get(v___x_6807_, 0);
lean_inc(v_a_6808_);
lean_dec_ref(v___x_6807_);
v___x_6809_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6794_, v_argsPacker_6795_, v_decrTactics_6796_, v_a_6808_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_);
if (lean_obj_tag(v___x_6809_) == 0)
{
lean_object* v_a_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; uint8_t v___x_6815_; uint8_t v___x_6816_; lean_object* v___x_6817_; 
v_a_6810_ = lean_ctor_get(v___x_6809_, 0);
lean_inc(v_a_6810_);
lean_dec_ref(v___x_6809_);
v___x_6811_ = lean_unsigned_to_nat(2u);
v___x_6812_ = lean_mk_empty_array_with_capacity(v___x_6811_);
v___x_6813_ = lean_array_push(v___x_6812_, v___x_6790_);
v___x_6814_ = lean_array_push(v___x_6813_, v___x_6791_);
v___x_6815_ = 1;
v___x_6816_ = 1;
v___x_6817_ = l_Lean_Meta_mkLambdaFVars(v___x_6814_, v_a_6810_, v___x_6797_, v___x_6815_, v___x_6797_, v___x_6815_, v___x_6816_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_);
lean_dec_ref(v___x_6814_);
if (lean_obj_tag(v___x_6817_) == 0)
{
lean_object* v_a_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; 
v_a_6818_ = lean_ctor_get(v___x_6817_, 0);
lean_inc(v_a_6818_);
lean_dec_ref(v___x_6817_);
v___x_6819_ = l_Lean_Expr_app___override(v_fst_6798_, v_a_6818_);
v___x_6820_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6799_, v___x_6819_, v___x_6797_, v___x_6815_, v___x_6797_, v___x_6815_, v___x_6816_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_);
return v___x_6820_;
}
else
{
lean_dec_ref(v_fst_6798_);
return v___x_6817_;
}
}
else
{
lean_dec_ref(v_fst_6798_);
lean_dec_ref(v___x_6791_);
lean_dec_ref(v___x_6790_);
return v___x_6809_;
}
}
else
{
lean_dec_ref(v_fst_6798_);
lean_dec_ref(v_decrTactics_6796_);
lean_dec_ref(v_argsPacker_6795_);
lean_dec_ref(v_funNames_6794_);
lean_dec_ref(v___x_6791_);
lean_dec_ref(v___x_6790_);
return v___x_6807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6821_ = _args[0];
lean_object* v___x_6822_ = _args[1];
lean_object* v___x_6823_ = _args[2];
lean_object* v___f_6824_ = _args[3];
lean_object* v_funNames_6825_ = _args[4];
lean_object* v_argsPacker_6826_ = _args[5];
lean_object* v_decrTactics_6827_ = _args[6];
lean_object* v___x_6828_ = _args[7];
lean_object* v_fst_6829_ = _args[8];
lean_object* v_prefixArgs_6830_ = _args[9];
lean_object* v___y_6831_ = _args[10];
lean_object* v___y_6832_ = _args[11];
lean_object* v___y_6833_ = _args[12];
lean_object* v___y_6834_ = _args[13];
lean_object* v___y_6835_ = _args[14];
lean_object* v___y_6836_ = _args[15];
lean_object* v___y_6837_ = _args[16];
_start:
{
uint8_t v___x_5940__boxed_6838_; lean_object* v_res_6839_; 
v___x_5940__boxed_6838_ = lean_unbox(v___x_6828_);
v_res_6839_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6821_, v___x_6822_, v___x_6823_, v___f_6824_, v_funNames_6825_, v_argsPacker_6826_, v_decrTactics_6827_, v___x_5940__boxed_6838_, v_fst_6829_, v_prefixArgs_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_);
lean_dec(v___y_6836_);
lean_dec_ref(v___y_6835_);
lean_dec(v___y_6834_);
lean_dec_ref(v___y_6833_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec_ref(v_prefixArgs_6830_);
return v_res_6839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6840_, lean_object* v_snd_6841_, lean_object* v___x_6842_, lean_object* v_prefixArgs_6843_, lean_object* v_value_6844_, lean_object* v___f_6845_, lean_object* v_funNames_6846_, lean_object* v_argsPacker_6847_, lean_object* v_decrTactics_6848_, uint8_t v___x_6849_, lean_object* v_fst_6850_, lean_object* v_xs_6851_, lean_object* v_x_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_){
_start:
{
lean_object* v_lctx_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; lean_object* v___x_6867_; lean_object* v___x_6868_; lean_object* v___f_6869_; lean_object* v___x_6870_; 
v_lctx_6860_ = lean_ctor_get(v___y_6855_, 2);
v___x_6861_ = lean_unsigned_to_nat(0u);
v___x_6862_ = lean_array_get_borrowed(v___x_6840_, v_xs_6851_, v___x_6861_);
v___x_6863_ = l_Lean_Expr_fvarId_x21(v___x_6862_);
lean_inc_ref(v_lctx_6860_);
v___x_6864_ = l_Lean_LocalContext_setUserName(v_lctx_6860_, v___x_6863_, v_snd_6841_);
v___x_6865_ = lean_array_get_borrowed(v___x_6840_, v_xs_6851_, v___x_6842_);
lean_inc_n(v___x_6862_, 2);
lean_inc_ref(v_prefixArgs_6843_);
v___x_6866_ = lean_array_push(v_prefixArgs_6843_, v___x_6862_);
v___x_6867_ = l_Lean_Expr_beta(v_value_6844_, v___x_6866_);
v___x_6868_ = lean_box(v___x_6849_);
lean_inc(v___x_6865_);
v___f_6869_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6869_, 0, v___x_6862_);
lean_closure_set(v___f_6869_, 1, v___x_6865_);
lean_closure_set(v___f_6869_, 2, v___x_6867_);
lean_closure_set(v___f_6869_, 3, v___f_6845_);
lean_closure_set(v___f_6869_, 4, v_funNames_6846_);
lean_closure_set(v___f_6869_, 5, v_argsPacker_6847_);
lean_closure_set(v___f_6869_, 6, v_decrTactics_6848_);
lean_closure_set(v___f_6869_, 7, v___x_6868_);
lean_closure_set(v___f_6869_, 8, v_fst_6850_);
lean_closure_set(v___f_6869_, 9, v_prefixArgs_6843_);
v___x_6870_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6864_, v___f_6869_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_);
return v___x_6870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6871_ = _args[0];
lean_object* v_snd_6872_ = _args[1];
lean_object* v___x_6873_ = _args[2];
lean_object* v_prefixArgs_6874_ = _args[3];
lean_object* v_value_6875_ = _args[4];
lean_object* v___f_6876_ = _args[5];
lean_object* v_funNames_6877_ = _args[6];
lean_object* v_argsPacker_6878_ = _args[7];
lean_object* v_decrTactics_6879_ = _args[8];
lean_object* v___x_6880_ = _args[9];
lean_object* v_fst_6881_ = _args[10];
lean_object* v_xs_6882_ = _args[11];
lean_object* v_x_6883_ = _args[12];
lean_object* v___y_6884_ = _args[13];
lean_object* v___y_6885_ = _args[14];
lean_object* v___y_6886_ = _args[15];
lean_object* v___y_6887_ = _args[16];
lean_object* v___y_6888_ = _args[17];
lean_object* v___y_6889_ = _args[18];
lean_object* v___y_6890_ = _args[19];
_start:
{
uint8_t v___x_6010__boxed_6891_; lean_object* v_res_6892_; 
v___x_6010__boxed_6891_ = lean_unbox(v___x_6880_);
v_res_6892_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6871_, v_snd_6872_, v___x_6873_, v_prefixArgs_6874_, v_value_6875_, v___f_6876_, v_funNames_6877_, v_argsPacker_6878_, v_decrTactics_6879_, v___x_6010__boxed_6891_, v_fst_6881_, v_xs_6882_, v_x_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_);
lean_dec(v___y_6889_);
lean_dec_ref(v___y_6888_);
lean_dec(v___y_6887_);
lean_dec_ref(v___y_6886_);
lean_dec(v___y_6885_);
lean_dec_ref(v___y_6884_);
lean_dec_ref(v_x_6883_);
lean_dec_ref(v_xs_6882_);
lean_dec(v___x_6873_);
lean_dec_ref(v___x_6871_);
return v_res_6892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6897_, lean_object* v_prefixArgs_6898_, lean_object* v_argsPacker_6899_, lean_object* v_wfRel_6900_, lean_object* v_funNames_6901_, lean_object* v_decrTactics_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_){
_start:
{
lean_object* v_declName_6910_; lean_object* v_type_6911_; lean_object* v_value_6912_; lean_object* v___x_6913_; 
v_declName_6910_ = lean_ctor_get(v_preDef_6897_, 3);
lean_inc(v_declName_6910_);
v_type_6911_ = lean_ctor_get(v_preDef_6897_, 6);
lean_inc_ref(v_type_6911_);
v_value_6912_ = lean_ctor_get(v_preDef_6897_, 7);
lean_inc_ref(v_value_6912_);
lean_dec_ref(v_preDef_6897_);
v___x_6913_ = l_Lean_Meta_instantiateForall(v_type_6911_, v_prefixArgs_6898_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_);
if (lean_obj_tag(v___x_6913_) == 0)
{
lean_object* v_a_6914_; lean_object* v___x_6915_; lean_object* v___x_6916_; lean_object* v___f_6917_; lean_object* v___x_6918_; uint8_t v___x_6919_; lean_object* v___x_6920_; 
v_a_6914_ = lean_ctor_get(v___x_6913_, 0);
lean_inc(v_a_6914_);
lean_dec_ref(v___x_6913_);
v___x_6915_ = l_Lean_instInhabitedExpr;
v___x_6916_ = lean_unsigned_to_nat(1u);
v___f_6917_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6917_, 0, v___x_6915_);
lean_closure_set(v___f_6917_, 1, v___x_6916_);
lean_closure_set(v___f_6917_, 2, v_wfRel_6900_);
v___x_6918_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6919_ = 0;
v___x_6920_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6914_, v___x_6918_, v___f_6917_, v___x_6919_, v___x_6919_, v_a_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v_a_6921_; lean_object* v_fst_6922_; lean_object* v_snd_6923_; lean_object* v___x_6924_; 
v_a_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_a_6921_);
lean_dec_ref(v___x_6920_);
v_fst_6922_ = lean_ctor_get(v_a_6921_, 0);
lean_inc_n(v_fst_6922_, 2);
v_snd_6923_ = lean_ctor_get(v_a_6921_, 1);
lean_inc(v_snd_6923_);
lean_dec(v_a_6921_);
lean_inc(v_a_6908_);
lean_inc_ref(v_a_6907_);
lean_inc(v_a_6906_);
lean_inc_ref(v_a_6905_);
v___x_6924_ = lean_infer_type(v_fst_6922_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_);
if (lean_obj_tag(v___x_6924_) == 0)
{
lean_object* v_a_6925_; lean_object* v___x_6926_; 
v_a_6925_ = lean_ctor_get(v___x_6924_, 0);
lean_inc(v_a_6925_);
lean_dec_ref(v___x_6924_);
lean_inc(v_a_6908_);
lean_inc_ref(v_a_6907_);
lean_inc(v_a_6906_);
lean_inc_ref(v_a_6905_);
v___x_6926_ = lean_whnf(v_a_6925_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_);
if (lean_obj_tag(v___x_6926_) == 0)
{
lean_object* v_a_6927_; lean_object* v___f_6928_; lean_object* v___x_6929_; lean_object* v___f_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; lean_object* v___x_6933_; 
v_a_6927_ = lean_ctor_get(v___x_6926_, 0);
lean_inc(v_a_6927_);
lean_dec_ref(v___x_6926_);
lean_inc_ref(v_prefixArgs_6898_);
v___f_6928_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6928_, 0, v_prefixArgs_6898_);
lean_closure_set(v___f_6928_, 1, v_declName_6910_);
v___x_6929_ = lean_box(v___x_6919_);
v___f_6930_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6930_, 0, v___x_6915_);
lean_closure_set(v___f_6930_, 1, v_snd_6923_);
lean_closure_set(v___f_6930_, 2, v___x_6916_);
lean_closure_set(v___f_6930_, 3, v_prefixArgs_6898_);
lean_closure_set(v___f_6930_, 4, v_value_6912_);
lean_closure_set(v___f_6930_, 5, v___f_6928_);
lean_closure_set(v___f_6930_, 6, v_funNames_6901_);
lean_closure_set(v___f_6930_, 7, v_argsPacker_6899_);
lean_closure_set(v___f_6930_, 8, v_decrTactics_6902_);
lean_closure_set(v___f_6930_, 9, v___x_6929_);
lean_closure_set(v___f_6930_, 10, v_fst_6922_);
v___x_6931_ = l_Lean_Expr_bindingDomain_x21(v_a_6927_);
lean_dec(v_a_6927_);
v___x_6932_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6933_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6931_, v___x_6932_, v___f_6930_, v___x_6919_, v___x_6919_, v_a_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_);
return v___x_6933_;
}
else
{
lean_dec(v_snd_6923_);
lean_dec(v_fst_6922_);
lean_dec_ref(v_value_6912_);
lean_dec(v_declName_6910_);
lean_dec_ref(v_decrTactics_6902_);
lean_dec_ref(v_funNames_6901_);
lean_dec_ref(v_argsPacker_6899_);
lean_dec_ref(v_prefixArgs_6898_);
return v___x_6926_;
}
}
else
{
lean_dec(v_snd_6923_);
lean_dec(v_fst_6922_);
lean_dec_ref(v_value_6912_);
lean_dec(v_declName_6910_);
lean_dec_ref(v_decrTactics_6902_);
lean_dec_ref(v_funNames_6901_);
lean_dec_ref(v_argsPacker_6899_);
lean_dec_ref(v_prefixArgs_6898_);
return v___x_6924_;
}
}
else
{
lean_object* v_a_6934_; lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6941_; 
lean_dec_ref(v_value_6912_);
lean_dec(v_declName_6910_);
lean_dec_ref(v_decrTactics_6902_);
lean_dec_ref(v_funNames_6901_);
lean_dec_ref(v_argsPacker_6899_);
lean_dec_ref(v_prefixArgs_6898_);
v_a_6934_ = lean_ctor_get(v___x_6920_, 0);
v_isSharedCheck_6941_ = !lean_is_exclusive(v___x_6920_);
if (v_isSharedCheck_6941_ == 0)
{
v___x_6936_ = v___x_6920_;
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
else
{
lean_inc(v_a_6934_);
lean_dec(v___x_6920_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v___x_6939_; 
if (v_isShared_6937_ == 0)
{
v___x_6939_ = v___x_6936_;
goto v_reusejp_6938_;
}
else
{
lean_object* v_reuseFailAlloc_6940_; 
v_reuseFailAlloc_6940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6940_, 0, v_a_6934_);
v___x_6939_ = v_reuseFailAlloc_6940_;
goto v_reusejp_6938_;
}
v_reusejp_6938_:
{
return v___x_6939_;
}
}
}
}
else
{
lean_dec_ref(v_value_6912_);
lean_dec(v_declName_6910_);
lean_dec_ref(v_decrTactics_6902_);
lean_dec_ref(v_funNames_6901_);
lean_dec_ref(v_wfRel_6900_);
lean_dec_ref(v_argsPacker_6899_);
lean_dec_ref(v_prefixArgs_6898_);
return v___x_6913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6942_, lean_object* v_prefixArgs_6943_, lean_object* v_argsPacker_6944_, lean_object* v_wfRel_6945_, lean_object* v_funNames_6946_, lean_object* v_decrTactics_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_, lean_object* v_a_6950_, lean_object* v_a_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_, lean_object* v_a_6954_){
_start:
{
lean_object* v_res_6955_; 
v_res_6955_ = l_Lean_Elab_WF_mkFix(v_preDef_6942_, v_prefixArgs_6943_, v_argsPacker_6944_, v_wfRel_6945_, v_funNames_6946_, v_decrTactics_6947_, v_a_6948_, v_a_6949_, v_a_6950_, v_a_6951_, v_a_6952_, v_a_6953_);
lean_dec(v_a_6953_);
lean_dec_ref(v_a_6952_);
lean_dec(v_a_6951_);
lean_dec_ref(v_a_6950_);
lean_dec(v_a_6949_);
lean_dec_ref(v_a_6948_);
return v_res_6955_;
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
