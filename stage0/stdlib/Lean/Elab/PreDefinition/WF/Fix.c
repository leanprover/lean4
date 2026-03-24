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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
lean_dec_ref(v_a_76_);
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
lean_dec_ref(v_a_76_);
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
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object* v_decreasingProp_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
lean_inc_ref(v_a_116_);
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
lean_inc_ref(v_a_260_);
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
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_359_);
lean_inc(v___y_358_);
v___x_367_ = lean_apply_9(v_k_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, lean_box(0));
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0___boxed(lean_object* v_k_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___lam__0(v_k_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_k_379_, uint8_t v_allowLevelAssignments_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___f_390_; lean_object* v___x_391_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc(v___y_381_);
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
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec(v___y_402_);
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
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
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
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
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
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
lean_inc(v___y_577_);
v___x_587_ = lean_apply_10(v_k_576_, v_b_581_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed(lean_object* v_k_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(v_k_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v_b_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v___y_589_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(lean_object* v_name_600_, uint8_t v_bi_601_, lean_object* v_type_602_, lean_object* v_k_603_, uint8_t v_kind_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_615_; 
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc(v___y_605_);
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
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec(v___y_629_);
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
lean_object* v_fileName_794_; lean_object* v_fileMap_795_; lean_object* v_options_796_; lean_object* v_currRecDepth_797_; lean_object* v_maxRecDepth_798_; lean_object* v_ref_799_; lean_object* v_currNamespace_800_; lean_object* v_openDecls_801_; lean_object* v_initHeartbeats_802_; lean_object* v_maxHeartbeats_803_; lean_object* v_quotContext_804_; lean_object* v_currMacroScope_805_; uint8_t v_diag_806_; lean_object* v_cancelTk_x3f_807_; uint8_t v_suppressElabErrors_808_; lean_object* v_inheritedTraceOptions_809_; lean_object* v_ref_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
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
v_ref_810_ = l_Lean_replaceRef(v_ref_783_, v_ref_799_);
lean_inc_ref(v_inheritedTraceOptions_809_);
lean_inc(v_cancelTk_x3f_807_);
lean_inc(v_currMacroScope_805_);
lean_inc(v_quotContext_804_);
lean_inc(v_maxHeartbeats_803_);
lean_inc(v_initHeartbeats_802_);
lean_inc(v_openDecls_801_);
lean_inc(v_currNamespace_800_);
lean_inc(v_maxRecDepth_798_);
lean_inc(v_currRecDepth_797_);
lean_inc_ref(v_options_796_);
lean_inc_ref(v_fileMap_795_);
lean_inc_ref(v_fileName_794_);
v___x_811_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_811_, 0, v_fileName_794_);
lean_ctor_set(v___x_811_, 1, v_fileMap_795_);
lean_ctor_set(v___x_811_, 2, v_options_796_);
lean_ctor_set(v___x_811_, 3, v_currRecDepth_797_);
lean_ctor_set(v___x_811_, 4, v_maxRecDepth_798_);
lean_ctor_set(v___x_811_, 5, v_ref_810_);
lean_ctor_set(v___x_811_, 6, v_currNamespace_800_);
lean_ctor_set(v___x_811_, 7, v_openDecls_801_);
lean_ctor_set(v___x_811_, 8, v_initHeartbeats_802_);
lean_ctor_set(v___x_811_, 9, v_maxHeartbeats_803_);
lean_ctor_set(v___x_811_, 10, v_quotContext_804_);
lean_ctor_set(v___x_811_, 11, v_currMacroScope_805_);
lean_ctor_set(v___x_811_, 12, v_cancelTk_x3f_807_);
lean_ctor_set(v___x_811_, 13, v_inheritedTraceOptions_809_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14, v_diag_806_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 1, v_suppressElabErrors_808_);
v___x_812_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_msg_784_, v___y_789_, v___y_790_, v___x_811_, v___y_792_);
lean_dec_ref(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg___boxed(lean_object* v_ref_813_, lean_object* v_msg_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_813_, v_msg_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v___y_815_);
lean_dec(v_ref_813_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(lean_object* v_ref_825_, lean_object* v_msg_826_, lean_object* v_declHint_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; 
v___x_837_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31(v_msg_826_, v_declHint_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_825_, v_a_838_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg___boxed(lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v_declHint_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_840_, v_msg_841_, v_declHint_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec(v_ref_840_);
return v_res_852_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__0));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__2));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(lean_object* v_ref_859_, lean_object* v_constName_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_870_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__1);
v___x_871_ = 0;
lean_inc(v_constName_860_);
v___x_872_ = l_Lean_MessageData_ofConstName(v_constName_860_, v___x_871_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___closed__3);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_859_, v___x_875_, v_constName_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg___boxed(lean_object* v_ref_877_, lean_object* v_constName_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_877_, v_constName_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v_ref_877_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(lean_object* v_constName_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_ref_899_; lean_object* v___x_900_; 
v_ref_899_ = lean_ctor_get(v___y_896_, 5);
v___x_900_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_899_, v_constName_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg___boxed(lean_object* v_constName_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec(v___y_902_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(lean_object* v_constName_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; lean_object* v_env_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = lean_st_ref_get(v___y_920_);
v_env_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_env_923_);
lean_dec(v___x_922_);
v___x_924_ = 0;
lean_inc(v_constName_912_);
v___x_925_ = l_Lean_Environment_find_x3f(v_env_923_, v_constName_912_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_926_;
}
else
{
lean_object* v_val_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_constName_912_);
v_val_927_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_val_927_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 0);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_val_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___boxed(lean_object* v_constName_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_constName_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(lean_object* v_declName_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_env_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_env_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_950_);
lean_dec(v___x_949_);
v___x_951_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_950_, v_declName_946_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg___boxed(lean_object* v_declName_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0(void){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_instMonadEIO(lean_box(0));
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_toApplicative_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1069_; 
v___x_974_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__0);
v___x_975_ = l_StateRefT_x27_instMonad___redArg(v___x_974_);
v_toApplicative_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v___x_975_, 1);
lean_dec(v_unused_1070_);
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1069_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_toApplicative_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1069_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_toFunctor_980_; lean_object* v_toSeq_981_; lean_object* v_toSeqLeft_982_; lean_object* v_toSeqRight_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1067_; 
v_toFunctor_980_ = lean_ctor_get(v_toApplicative_976_, 0);
v_toSeq_981_ = lean_ctor_get(v_toApplicative_976_, 2);
v_toSeqLeft_982_ = lean_ctor_get(v_toApplicative_976_, 3);
v_toSeqRight_983_ = lean_ctor_get(v_toApplicative_976_, 4);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_toApplicative_976_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_toApplicative_976_, 1);
lean_dec(v_unused_1068_);
v___x_985_ = v_toApplicative_976_;
v_isShared_986_ = v_isSharedCheck_1067_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_toSeqRight_983_);
lean_inc(v_toSeqLeft_982_);
lean_inc(v_toSeq_981_);
lean_inc(v_toFunctor_980_);
lean_dec(v_toApplicative_976_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1067_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___x_996_; 
v___f_987_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__1));
v___f_988_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__2));
lean_inc_ref(v_toFunctor_980_);
v___f_989_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_989_, 0, v_toFunctor_980_);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_990_, 0, v_toFunctor_980_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___f_989_);
lean_ctor_set(v___x_991_, 1, v___f_990_);
v___f_992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_992_, 0, v_toSeqRight_983_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_993_, 0, v_toSeqLeft_982_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_994_, 0, v_toSeq_981_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 4, v___f_992_);
lean_ctor_set(v___x_985_, 3, v___f_993_);
lean_ctor_set(v___x_985_, 2, v___f_994_);
lean_ctor_set(v___x_985_, 1, v___f_987_);
lean_ctor_set(v___x_985_, 0, v___x_991_);
v___x_996_ = v___x_985_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___f_987_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___f_994_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v___f_992_);
v___x_996_ = v_reuseFailAlloc_1066_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___f_988_);
lean_ctor_set(v___x_978_, 0, v___x_996_);
v___x_998_ = v___x_978_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___f_988_);
v___x_998_ = v_reuseFailAlloc_1065_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v_toApplicative_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1063_; 
v___x_999_ = l_StateRefT_x27_instMonad___redArg(v___x_998_);
v_toApplicative_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_999_, 1);
lean_dec(v_unused_1064_);
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1063_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_toApplicative_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1063_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_toFunctor_1004_; lean_object* v_toSeq_1005_; lean_object* v_toSeqLeft_1006_; lean_object* v_toSeqRight_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1061_; 
v_toFunctor_1004_ = lean_ctor_get(v_toApplicative_1000_, 0);
v_toSeq_1005_ = lean_ctor_get(v_toApplicative_1000_, 2);
v_toSeqLeft_1006_ = lean_ctor_get(v_toApplicative_1000_, 3);
v_toSeqRight_1007_ = lean_ctor_get(v_toApplicative_1000_, 4);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_toApplicative_1000_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_toApplicative_1000_, 1);
lean_dec(v_unused_1062_);
v___x_1009_ = v_toApplicative_1000_;
v_isShared_1010_ = v_isSharedCheck_1061_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_toSeqRight_1007_);
lean_inc(v_toSeqLeft_1006_);
lean_inc(v_toSeq_1005_);
lean_inc(v_toFunctor_1004_);
lean_dec(v_toApplicative_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1061_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1020_; 
v___f_1011_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__3));
v___f_1012_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__4));
lean_inc_ref(v_toFunctor_1004_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toFunctor_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1004_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___f_1013_);
lean_ctor_set(v___x_1015_, 1, v___f_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toSeqRight_1007_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqLeft_1006_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeq_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___f_1016_);
lean_ctor_set(v___x_1009_, 3, v___f_1017_);
lean_ctor_set(v___x_1009_, 2, v___f_1018_);
lean_ctor_set(v___x_1009_, 1, v___f_1011_);
lean_ctor_set(v___x_1009_, 0, v___x_1015_);
v___x_1020_ = v___x_1009_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___f_1011_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___f_1016_);
v___x_1020_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___f_1012_);
lean_ctor_set(v___x_1002_, 0, v___x_1020_);
v___x_1022_ = v___x_1002_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_1012_);
v___x_1022_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v_toApplicative_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1057_; 
v___x_1023_ = l_StateRefT_x27_instMonad___redArg(v___x_1022_);
v_toApplicative_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1023_, 1);
lean_dec(v_unused_1058_);
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1057_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_toApplicative_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1057_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_toFunctor_1028_; lean_object* v_toSeq_1029_; lean_object* v_toSeqLeft_1030_; lean_object* v_toSeqRight_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1055_; 
v_toFunctor_1028_ = lean_ctor_get(v_toApplicative_1024_, 0);
v_toSeq_1029_ = lean_ctor_get(v_toApplicative_1024_, 2);
v_toSeqLeft_1030_ = lean_ctor_get(v_toApplicative_1024_, 3);
v_toSeqRight_1031_ = lean_ctor_get(v_toApplicative_1024_, 4);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_toApplicative_1024_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_toApplicative_1024_, 1);
lean_dec(v_unused_1056_);
v___x_1033_ = v_toApplicative_1024_;
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_toSeqRight_1031_);
lean_inc(v_toSeqLeft_1030_);
lean_inc(v_toSeq_1029_);
lean_inc(v_toFunctor_1028_);
lean_dec(v_toApplicative_1024_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1044_; 
v___f_1035_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__5));
v___f_1036_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___closed__6));
lean_inc_ref(v_toFunctor_1028_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toFunctor_1028_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toFunctor_1028_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___f_1037_);
lean_ctor_set(v___x_1039_, 1, v___f_1038_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeqRight_1031_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeqLeft_1030_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeq_1029_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___f_1040_);
lean_ctor_set(v___x_1033_, 3, v___f_1041_);
lean_ctor_set(v___x_1033_, 2, v___f_1042_);
lean_ctor_set(v___x_1033_, 1, v___f_1035_);
lean_ctor_set(v___x_1033_, 0, v___x_1039_);
v___x_1044_ = v___x_1033_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___f_1035_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v___f_1040_);
v___x_1044_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___f_1036_);
lean_ctor_set(v___x_1026_, 0, v___x_1044_);
v___x_1046_ = v___x_1026_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___f_1036_);
v___x_1046_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_58639__overap_1051_; lean_object* v___x_1052_; 
v___x_1047_ = l_StateRefT_x27_instMonad___redArg(v___x_1046_);
v___x_1048_ = l_StateRefT_x27_instMonad___redArg(v___x_1047_);
v___x_1049_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1050_ = l_instInhabitedOfMonad___redArg(v___x_1048_, v___x_1049_);
v___x_58639__overap_1051_ = lean_panic_fn(v___x_1050_, v_msg_964_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc(v___y_965_);
v___x_1052_ = lean_apply_9(v___x_58639__overap_1051_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, lean_box(0));
return v___x_1052_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___boxed(lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(v_msg_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1081_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__2));
v___x_1086_ = lean_unsigned_to_nat(53u);
v___x_1087_ = lean_unsigned_to_nat(62u);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__1));
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__0));
v___x_1090_ = l_mkPanicMessageWithDecl(v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_, v___x_1085_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_bs_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_bs_1093_);
return v___x_1104_;
}
else
{
lean_object* v_v_1105_; lean_object* v___x_1106_; 
v_v_1105_ = lean_array_uget_borrowed(v_bs_1093_, v_i_1092_);
lean_inc(v_v_1105_);
v___x_1106_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_v_1105_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; lean_object* v_bs_x27_1109_; lean_object* v_a_1111_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v_bs_x27_1109_ = lean_array_uset(v_bs_1093_, v_i_1092_, v___x_1108_);
if (lean_obj_tag(v_a_1107_) == 6)
{
lean_object* v_val_1116_; lean_object* v_numFields_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; 
v_val_1116_ = lean_ctor_get(v_a_1107_, 0);
lean_inc_ref(v_val_1116_);
lean_dec_ref(v_a_1107_);
v_numFields_1117_ = lean_ctor_get(v_val_1116_, 4);
lean_inc(v_numFields_1117_);
lean_dec_ref(v_val_1116_);
v___x_1118_ = 0;
v___x_1119_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1119_, 0, v_numFields_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1108_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*2, v___x_1118_);
v_a_1111_ = v___x_1119_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_a_1107_);
v___x_1120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___closed__3);
v___x_1121_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(v___x_1120_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v_a_1111_ = v_a_1122_;
goto v___jp_1110_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_bs_x27_1109_);
v_a_1123_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
v___jp_1110_:
{
size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_add(v_i_1092_, v___x_1112_);
v___x_1114_ = lean_array_uset(v_bs_x27_1109_, v_i_1092_, v_a_1111_);
v_i_1092_ = v___x_1113_;
v_bs_1093_ = v___x_1114_;
goto _start;
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_bs_1093_);
v_a_1131_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1106_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1106_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22___boxed(lean_object* v_sz_1139_, lean_object* v_i_1140_, lean_object* v_bs_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
size_t v_sz_boxed_1151_; size_t v_i_boxed_1152_; lean_object* v_res_1153_; 
v_sz_boxed_1151_ = lean_unbox_usize(v_sz_1139_);
lean_dec(v_sz_1139_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1140_);
lean_dec(v_i_1140_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(v_sz_boxed_1151_, v_i_boxed_1152_, v_bs_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
return v_res_1153_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0(void){
_start:
{
lean_object* v___x_1154_; lean_object* v_dummy_1155_; 
v___x_1154_ = lean_box(0);
v_dummy_1155_ = l_Lean_Expr_sort___override(v___x_1154_);
return v_dummy_1155_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_unsigned_to_nat(16u);
v___x_1158_ = lean_mk_array(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_e_1164_, uint8_t v_alsoCasesOn_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = l_Lean_Expr_isApp(v_e_1164_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_e_1164_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Expr_getAppFn(v_e_1164_);
if (lean_obj_tag(v___x_1181_) == 4)
{
lean_object* v_declName_1182_; lean_object* v_us_1183_; lean_object* v___x_1184_; lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1339_; 
v_declName_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_declName_1182_);
v_us_1183_ = lean_ctor_get(v___x_1181_, 1);
lean_inc(v_us_1183_);
lean_dec_ref(v___x_1181_);
lean_inc(v_declName_1182_);
v___x_1184_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_1182_, v___y_1173_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1339_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1339_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
if (lean_obj_tag(v_a_1185_) == 1)
{
lean_object* v_val_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1231_; 
v_val_1189_ = lean_ctor_get(v_a_1185_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1191_ = v_a_1185_;
v_isShared_1192_ = v_isSharedCheck_1231_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_val_1189_);
lean_dec(v_a_1185_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1231_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_dummy_1193_; lean_object* v_nargs_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_args_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_dummy_1193_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_1194_ = l_Lean_Expr_getAppNumArgs(v_e_1164_);
lean_inc(v_nargs_1194_);
v___x_1195_ = lean_mk_array(v_nargs_1194_, v_dummy_1193_);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_sub(v_nargs_1194_, v___x_1196_);
lean_dec(v_nargs_1194_);
v_args_1198_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1164_, v___x_1195_, v___x_1197_);
v___x_1199_ = lean_array_get_size(v_args_1198_);
v___x_1200_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1189_);
v___x_1201_ = lean_nat_dec_lt(v___x_1199_, v___x_1200_);
lean_dec(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v_numParams_1202_; lean_object* v_numDiscrs_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v_numParams_1202_ = lean_ctor_get(v_val_1189_, 0);
v_numDiscrs_1203_ = lean_ctor_get(v_val_1189_, 1);
v___x_1204_ = lean_array_mk(v_us_1183_);
v___x_1205_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1202_);
v___x_1206_ = l_Array_extract___redArg(v_args_1198_, v___x_1205_, v_numParams_1202_);
v___x_1207_ = l_Lean_instInhabitedExpr;
v___x_1208_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1189_);
v___x_1209_ = lean_array_get(v___x_1207_, v_args_1198_, v___x_1208_);
lean_dec(v___x_1208_);
v___x_1210_ = lean_nat_add(v_numParams_1202_, v___x_1196_);
v___x_1211_ = lean_nat_add(v___x_1210_, v_numDiscrs_1203_);
lean_inc(v___x_1211_);
lean_inc_ref(v_args_1198_);
v___x_1212_ = l_Array_toSubarray___redArg(v_args_1198_, v___x_1210_, v___x_1211_);
v___x_1213_ = l_Subarray_copy___redArg(v___x_1212_);
v___x_1214_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1189_);
v___x_1215_ = lean_nat_add(v___x_1211_, v___x_1214_);
lean_dec(v___x_1214_);
lean_inc(v___x_1215_);
lean_inc_ref(v_args_1198_);
v___x_1216_ = l_Array_toSubarray___redArg(v_args_1198_, v___x_1211_, v___x_1215_);
v___x_1217_ = l_Subarray_copy___redArg(v___x_1216_);
v___x_1218_ = l_Array_toSubarray___redArg(v_args_1198_, v___x_1215_, v___x_1199_);
v___x_1219_ = l_Subarray_copy___redArg(v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1220_, 0, v_val_1189_);
lean_ctor_set(v___x_1220_, 1, v_declName_1182_);
lean_ctor_set(v___x_1220_, 2, v___x_1204_);
lean_ctor_set(v___x_1220_, 3, v___x_1206_);
lean_ctor_set(v___x_1220_, 4, v___x_1209_);
lean_ctor_set(v___x_1220_, 5, v___x_1213_);
lean_ctor_set(v___x_1220_, 6, v___x_1217_);
lean_ctor_set(v___x_1220_, 7, v___x_1219_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1220_);
v___x_1222_ = v___x_1191_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1222_);
v___x_1224_ = v___x_1187_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec_ref(v_args_1198_);
lean_del_object(v___x_1191_);
lean_dec(v_val_1189_);
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
v___x_1227_ = lean_box(0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1227_);
v___x_1229_ = v___x_1187_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1232_; 
lean_del_object(v___x_1187_);
lean_dec(v_a_1185_);
v___x_1232_ = lean_st_ref_get(v___y_1173_);
if (v_alsoCasesOn_1165_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
lean_dec_ref(v_e_1164_);
goto v___jp_1175_;
}
else
{
lean_object* v_env_1233_; uint8_t v___x_1234_; 
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_env_1233_);
lean_dec(v___x_1232_);
lean_inc(v_declName_1182_);
v___x_1234_ = l_Lean_isCasesOnRecursor(v_env_1233_, v_declName_1182_);
if (v___x_1234_ == 0)
{
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
lean_dec_ref(v_e_1164_);
goto v___jp_1175_;
}
else
{
lean_object* v_indName_1235_; lean_object* v___x_1236_; 
v_indName_1235_ = l_Lean_Name_getPrefix(v_declName_1182_);
v___x_1236_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_indName_1235_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1330_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1330_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1330_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
if (lean_obj_tag(v_a_1237_) == 5)
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1325_; 
v_val_1241_ = lean_ctor_get(v_a_1237_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_a_1237_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1243_ = v_a_1237_;
v_isShared_1244_ = v_isSharedCheck_1325_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v_a_1237_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1325_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_toConstantVal_1245_; lean_object* v_numParams_1246_; lean_object* v_numIndices_1247_; lean_object* v_ctors_1248_; lean_object* v_nargs_1249_; lean_object* v_dummy_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_args_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_toConstantVal_1245_ = lean_ctor_get(v_val_1241_, 0);
lean_inc_ref(v_toConstantVal_1245_);
v_numParams_1246_ = lean_ctor_get(v_val_1241_, 1);
lean_inc(v_numParams_1246_);
v_numIndices_1247_ = lean_ctor_get(v_val_1241_, 2);
lean_inc(v_numIndices_1247_);
v_ctors_1248_ = lean_ctor_get(v_val_1241_, 4);
lean_inc(v_ctors_1248_);
v_nargs_1249_ = l_Lean_Expr_getAppNumArgs(v_e_1164_);
v_dummy_1250_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v_nargs_1249_);
v___x_1251_ = lean_mk_array(v_nargs_1249_, v_dummy_1250_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_sub(v_nargs_1249_, v___x_1252_);
lean_dec(v_nargs_1249_);
v_args_1254_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1164_, v___x_1251_, v___x_1253_);
v___x_1255_ = lean_nat_add(v_numParams_1246_, v___x_1252_);
v___x_1256_ = lean_nat_add(v___x_1255_, v_numIndices_1247_);
v___x_1257_ = lean_nat_add(v___x_1256_, v___x_1252_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Lean_InductiveVal_numCtors(v_val_1241_);
lean_dec_ref(v_val_1241_);
v___x_1259_ = lean_nat_add(v___x_1257_, v___x_1258_);
lean_dec(v___x_1258_);
v___x_1260_ = lean_array_get_size(v_args_1254_);
v___x_1261_ = lean_nat_dec_le(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_dec(v___x_1259_);
lean_dec(v___x_1257_);
lean_dec(v___x_1255_);
lean_dec_ref(v_args_1254_);
lean_dec(v_ctors_1248_);
lean_dec(v_numIndices_1247_);
lean_dec(v_numParams_1246_);
lean_dec_ref(v_toConstantVal_1245_);
lean_del_object(v___x_1243_);
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
v___x_1262_ = lean_box(0);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1262_);
v___x_1264_ = v___x_1239_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
else
{
lean_object* v___x_1266_; lean_object* v_params_1267_; lean_object* v___x_1268_; lean_object* v_motive_1269_; lean_object* v_discrs_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_discrInfos_1273_; lean_object* v_alts_1274_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v_lower_1316_; lean_object* v_upper_1317_; uint8_t v___x_1324_; 
lean_del_object(v___x_1239_);
v___x_1266_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1246_);
lean_inc_ref(v_args_1254_);
v_params_1267_ = l_Array_toSubarray___redArg(v_args_1254_, v___x_1266_, v_numParams_1246_);
v___x_1268_ = l_Lean_instInhabitedExpr;
v_motive_1269_ = lean_array_get(v___x_1268_, v_args_1254_, v_numParams_1246_);
lean_dec(v_numParams_1246_);
lean_inc(v___x_1257_);
lean_inc_ref(v_args_1254_);
v_discrs_1270_ = l_Array_toSubarray___redArg(v_args_1254_, v___x_1255_, v___x_1257_);
v___x_1271_ = lean_nat_add(v_numIndices_1247_, v___x_1252_);
lean_dec(v_numIndices_1247_);
v___x_1272_ = lean_box(0);
v_discrInfos_1273_ = lean_mk_array(v___x_1271_, v___x_1272_);
lean_inc(v___x_1259_);
lean_inc_ref(v_args_1254_);
v_alts_1274_ = l_Array_toSubarray___redArg(v_args_1254_, v___x_1257_, v___x_1259_);
v___x_1324_ = lean_nat_dec_le(v___x_1259_, v___x_1266_);
if (v___x_1324_ == 0)
{
v_lower_1316_ = v___x_1259_;
v_upper_1317_ = v___x_1260_;
goto v___jp_1315_;
}
else
{
lean_dec(v___x_1259_);
v_lower_1316_ = v___x_1266_;
v_upper_1317_ = v___x_1260_;
goto v___jp_1315_;
}
v___jp_1275_:
{
lean_object* v___x_1278_; size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_array_mk(v_ctors_1248_);
v_sz_1279_ = lean_array_size(v___x_1278_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__22(v_sz_1279_, v___x_1280_, v___x_1278_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1306_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1306_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1306_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_start_1286_; lean_object* v_stop_1287_; lean_object* v_start_1288_; lean_object* v_stop_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v_start_1286_ = lean_ctor_get(v_params_1267_, 1);
lean_inc(v_start_1286_);
v_stop_1287_ = lean_ctor_get(v_params_1267_, 2);
lean_inc(v_stop_1287_);
v_start_1288_ = lean_ctor_get(v_discrs_1270_, 1);
lean_inc(v_start_1288_);
v_stop_1289_ = lean_ctor_get(v_discrs_1270_, 2);
lean_inc(v_stop_1289_);
v___x_1290_ = lean_nat_sub(v_stop_1287_, v_start_1286_);
lean_dec(v_start_1286_);
lean_dec(v_stop_1287_);
v___x_1291_ = lean_nat_sub(v_stop_1289_, v_start_1288_);
lean_dec(v_start_1288_);
lean_dec(v_stop_1289_);
v___x_1292_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2);
v___x_1293_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1290_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v_a_1282_);
lean_ctor_set(v___x_1293_, 3, v___y_1277_);
lean_ctor_set(v___x_1293_, 4, v_discrInfos_1273_);
lean_ctor_set(v___x_1293_, 5, v___x_1292_);
v___x_1294_ = lean_array_mk(v_us_1183_);
v___x_1295_ = l_Subarray_copy___redArg(v_params_1267_);
v___x_1296_ = l_Subarray_copy___redArg(v_discrs_1270_);
v___x_1297_ = l_Subarray_copy___redArg(v_alts_1274_);
v___x_1298_ = l_Subarray_copy___redArg(v___y_1276_);
v___x_1299_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1293_);
lean_ctor_set(v___x_1299_, 1, v_declName_1182_);
lean_ctor_set(v___x_1299_, 2, v___x_1294_);
lean_ctor_set(v___x_1299_, 3, v___x_1295_);
lean_ctor_set(v___x_1299_, 4, v_motive_1269_);
lean_ctor_set(v___x_1299_, 5, v___x_1296_);
lean_ctor_set(v___x_1299_, 6, v___x_1297_);
lean_ctor_set(v___x_1299_, 7, v___x_1298_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
lean_ctor_set(v___x_1243_, 0, v___x_1299_);
v___x_1301_ = v___x_1243_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1301_);
v___x_1303_ = v___x_1284_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v_alts_1274_);
lean_dec_ref(v_discrInfos_1273_);
lean_dec_ref(v_discrs_1270_);
lean_dec(v_motive_1269_);
lean_dec_ref(v_params_1267_);
lean_del_object(v___x_1243_);
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
v_a_1307_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1281_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1281_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1315_:
{
lean_object* v_levelParams_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_levelParams_1318_ = lean_ctor_get(v_toConstantVal_1245_, 1);
lean_inc(v_levelParams_1318_);
lean_dec_ref(v_toConstantVal_1245_);
v___x_1319_ = l_Array_toSubarray___redArg(v_args_1254_, v_lower_1316_, v_upper_1317_);
v___x_1320_ = l_List_lengthTR___redArg(v_levelParams_1318_);
lean_dec(v_levelParams_1318_);
v___x_1321_ = l_List_lengthTR___redArg(v_us_1183_);
v___x_1322_ = lean_nat_dec_eq(v___x_1320_, v___x_1321_);
lean_dec(v___x_1321_);
lean_dec(v___x_1320_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3));
v___y_1276_ = v___x_1319_;
v___y_1277_ = v___x_1323_;
goto v___jp_1275_;
}
else
{
v___y_1276_ = v___x_1319_;
v___y_1277_ = v___x_1272_;
goto v___jp_1275_;
}
}
}
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec(v_a_1237_);
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
lean_dec_ref(v_e_1164_);
v___x_1326_ = lean_box(0);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1326_);
v___x_1328_ = v___x_1239_;
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
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_us_1183_);
lean_dec(v_declName_1182_);
lean_dec_ref(v_e_1164_);
v_a_1331_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1236_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1236_);
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
}
}
}
}
else
{
lean_dec_ref(v___x_1181_);
lean_dec_ref(v_e_1164_);
goto v___jp_1175_;
}
}
v___jp_1175_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_e_1340_, lean_object* v_alsoCasesOn_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1351_; lean_object* v_res_1352_; 
v_alsoCasesOn_boxed_1351_ = lean_unbox(v_alsoCasesOn_1341_);
v_res_1352_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_1340_, v_alsoCasesOn_boxed_1351_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(lean_object* v_k_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v_b_1358_, lean_object* v_c_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc(v___y_1354_);
v___x_1365_ = lean_apply_11(v_k_1353_, v_b_1358_, v_c_1359_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, lean_box(0));
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed(lean_object* v_k_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v_b_1371_, lean_object* v_c_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(v_k_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v_b_1371_, v_c_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec(v___y_1367_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(lean_object* v_e_1379_, lean_object* v_maxFVars_1380_, lean_object* v_k_1381_, uint8_t v_cleanupAnnotations_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___f_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc(v___y_1383_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1392_, 0, v_k_1381_);
lean_closure_set(v___f_1392_, 1, v___y_1383_);
lean_closure_set(v___f_1392_, 2, v___y_1384_);
lean_closure_set(v___f_1392_, 3, v___y_1385_);
lean_closure_set(v___f_1392_, 4, v___y_1386_);
v___x_1393_ = 1;
v___x_1394_ = 0;
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_maxFVars_1380_);
v___x_1396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1379_, v___x_1393_, v___x_1394_, v___x_1393_, v___x_1394_, v___x_1395_, v___f_1392_, v_cleanupAnnotations_1382_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___boxed(lean_object* v_e_1405_, lean_object* v_maxFVars_1406_, lean_object* v_k_1407_, lean_object* v_cleanupAnnotations_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1418_; lean_object* v_res_1419_; 
v_cleanupAnnotations_boxed_1418_ = lean_unbox(v_cleanupAnnotations_1408_);
v_res_1419_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_1405_, v_maxFVars_1406_, v_k_1407_, v_cleanupAnnotations_boxed_1418_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(lean_object* v_name_1420_, lean_object* v_type_1421_, lean_object* v_val_1422_, lean_object* v_k_1423_, uint8_t v_nondep_1424_, uint8_t v_kind_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___f_1435_; lean_object* v___x_1436_; 
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc(v___y_1426_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1435_, 0, v_k_1423_);
lean_closure_set(v___f_1435_, 1, v___y_1426_);
lean_closure_set(v___f_1435_, 2, v___y_1427_);
lean_closure_set(v___f_1435_, 3, v___y_1428_);
lean_closure_set(v___f_1435_, 4, v___y_1429_);
v___x_1436_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1420_, v_type_1421_, v_val_1422_, v___f_1435_, v_nondep_1424_, v_kind_1425_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1436_) == 0)
{
return v___x_1436_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg___boxed(lean_object* v_name_1445_, lean_object* v_type_1446_, lean_object* v_val_1447_, lean_object* v_k_1448_, lean_object* v_nondep_1449_, lean_object* v_kind_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v_nondep_boxed_1460_; uint8_t v_kind_boxed_1461_; lean_object* v_res_1462_; 
v_nondep_boxed_1460_ = lean_unbox(v_nondep_1449_);
v_kind_boxed_1461_ = lean_unbox(v_kind_1450_);
v_res_1462_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_1445_, v_type_1446_, v_val_1447_, v_k_1448_, v_nondep_boxed_1460_, v_kind_boxed_1461_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(lean_object* v_k_1463_, uint8_t v_usedLetOnly_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v_x_1465_);
v___x_1475_ = lean_apply_10(v_k_1463_, v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, lean_box(0));
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1478_, v_x_1465_);
v___x_1480_ = 0;
v___x_1481_ = 1;
v___x_1482_ = l_Lean_Meta_mkLetFVars(v___x_1479_, v_a_1476_, v_usedLetOnly_1464_, v___x_1480_, v___x_1481_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec_ref(v___x_1479_);
return v___x_1482_;
}
else
{
lean_dec_ref(v_x_1465_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed(lean_object* v_k_1483_, lean_object* v_usedLetOnly_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_usedLetOnly_boxed_1495_; lean_object* v_res_1496_; 
v_usedLetOnly_boxed_1495_ = lean_unbox(v_usedLetOnly_1484_);
v_res_1496_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(v_k_1483_, v_usedLetOnly_boxed_1495_, v_x_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v___y_1486_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_name_1497_, lean_object* v_type_1498_, lean_object* v_val_1499_, lean_object* v_k_1500_, uint8_t v_nondep_1501_, uint8_t v_kind_1502_, uint8_t v_usedLetOnly_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(v_usedLetOnly_1503_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1514_, 0, v_k_1500_);
lean_closure_set(v___f_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_1497_, v_type_1498_, v_val_1499_, v___f_1514_, v_nondep_1501_, v_kind_1502_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_name_1516_, lean_object* v_type_1517_, lean_object* v_val_1518_, lean_object* v_k_1519_, lean_object* v_nondep_1520_, lean_object* v_kind_1521_, lean_object* v_usedLetOnly_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_nondep_boxed_1532_; uint8_t v_kind_boxed_1533_; uint8_t v_usedLetOnly_boxed_1534_; lean_object* v_res_1535_; 
v_nondep_boxed_1532_ = lean_unbox(v_nondep_1520_);
v_kind_boxed_1533_ = lean_unbox(v_kind_1521_);
v_usedLetOnly_boxed_1534_ = lean_unbox(v_usedLetOnly_1522_);
v_res_1535_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_name_1516_, v_type_1517_, v_val_1518_, v_k_1519_, v_nondep_boxed_1532_, v_kind_boxed_1533_, v_usedLetOnly_boxed_1534_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___y_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_opts_1536_, lean_object* v_opt_1537_){
_start:
{
lean_object* v_name_1538_; lean_object* v_defValue_1539_; lean_object* v_map_1540_; lean_object* v___x_1541_; 
v_name_1538_ = lean_ctor_get(v_opt_1537_, 0);
v_defValue_1539_ = lean_ctor_get(v_opt_1537_, 1);
v_map_1540_ = lean_ctor_get(v_opts_1536_, 0);
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1540_, v_name_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_defValue_1539_);
return v___x_1542_;
}
else
{
lean_object* v_val_1543_; 
v_val_1543_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1543_);
lean_dec_ref(v___x_1541_);
if (lean_obj_tag(v_val_1543_) == 1)
{
uint8_t v_v_1544_; 
v_v_1544_ = lean_ctor_get_uint8(v_val_1543_, 0);
lean_dec_ref(v_val_1543_);
return v_v_1544_;
}
else
{
uint8_t v___x_1545_; 
lean_dec(v_val_1543_);
v___x_1545_ = lean_unbox(v_defValue_1539_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_opts_1546_, lean_object* v_opt_1547_){
_start:
{
uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_res_1548_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_opts_1546_, v_opt_1547_);
lean_dec_ref(v_opt_1547_);
lean_dec_ref(v_opts_1546_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(lean_object* v_a_1550_, lean_object* v_x_1551_){
_start:
{
if (lean_obj_tag(v_x_1551_) == 0)
{
uint8_t v___x_1552_; 
v___x_1552_ = 0;
return v___x_1552_;
}
else
{
lean_object* v_key_1553_; lean_object* v_tail_1554_; uint8_t v___x_1555_; 
v_key_1553_ = lean_ctor_get(v_x_1551_, 0);
v_tail_1554_ = lean_ctor_get(v_x_1551_, 2);
v___x_1555_ = lean_expr_eqv(v_key_1553_, v_a_1550_);
if (v___x_1555_ == 0)
{
v_x_1551_ = v_tail_1554_;
goto _start;
}
else
{
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg___boxed(lean_object* v_a_1557_, lean_object* v_x_1558_){
_start:
{
uint8_t v_res_1559_; lean_object* v_r_1560_; 
v_res_1559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_1557_, v_x_1558_);
lean_dec(v_x_1558_);
lean_dec_ref(v_a_1557_);
v_r_1560_ = lean_box(v_res_1559_);
return v_r_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(lean_object* v_a_1561_, lean_object* v_b_1562_, lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1563_) == 0)
{
lean_dec(v_b_1562_);
lean_dec_ref(v_a_1561_);
return v_x_1563_;
}
else
{
lean_object* v_key_1564_; lean_object* v_value_1565_; lean_object* v_tail_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1578_; 
v_key_1564_ = lean_ctor_get(v_x_1563_, 0);
v_value_1565_ = lean_ctor_get(v_x_1563_, 1);
v_tail_1566_ = lean_ctor_get(v_x_1563_, 2);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1563_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1568_ = v_x_1563_;
v_isShared_1569_ = v_isSharedCheck_1578_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_tail_1566_);
lean_inc(v_value_1565_);
lean_inc(v_key_1564_);
lean_dec(v_x_1563_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1578_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_expr_eqv(v_key_1564_, v_a_1561_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_1561_, v_b_1562_, v_tail_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 2, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_key_1564_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_value_1565_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1576_; 
lean_dec(v_value_1565_);
lean_dec(v_key_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_b_1562_);
lean_ctor_set(v___x_1568_, 0, v_a_1561_);
v___x_1576_ = v___x_1568_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1561_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_b_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_tail_1566_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(lean_object* v_x_1579_, lean_object* v_x_1580_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
return v_x_1579_;
}
else
{
lean_object* v_key_1581_; lean_object* v_value_1582_; lean_object* v_tail_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1606_; 
v_key_1581_ = lean_ctor_get(v_x_1580_, 0);
v_value_1582_ = lean_ctor_get(v_x_1580_, 1);
v_tail_1583_ = lean_ctor_get(v_x_1580_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1580_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1585_ = v_x_1580_;
v_isShared_1586_ = v_isSharedCheck_1606_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_tail_1583_);
lean_inc(v_value_1582_);
lean_inc(v_key_1581_);
lean_dec(v_x_1580_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1606_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; uint64_t v___x_1588_; uint64_t v___x_1589_; uint64_t v___x_1590_; uint64_t v_fold_1591_; uint64_t v___x_1592_; uint64_t v___x_1593_; uint64_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1587_ = lean_array_get_size(v_x_1579_);
v___x_1588_ = l_Lean_Expr_hash(v_key_1581_);
v___x_1589_ = 32ULL;
v___x_1590_ = lean_uint64_shift_right(v___x_1588_, v___x_1589_);
v_fold_1591_ = lean_uint64_xor(v___x_1588_, v___x_1590_);
v___x_1592_ = 16ULL;
v___x_1593_ = lean_uint64_shift_right(v_fold_1591_, v___x_1592_);
v___x_1594_ = lean_uint64_xor(v_fold_1591_, v___x_1593_);
v___x_1595_ = lean_uint64_to_usize(v___x_1594_);
v___x_1596_ = lean_usize_of_nat(v___x_1587_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_sub(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_usize_land(v___x_1595_, v___x_1598_);
v___x_1600_ = lean_array_uget_borrowed(v_x_1579_, v___x_1599_);
lean_inc(v___x_1600_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 2, v___x_1600_);
v___x_1602_ = v___x_1585_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_key_1581_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_value_1582_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_array_uset(v_x_1579_, v___x_1599_, v___x_1602_);
v_x_1579_ = v___x_1603_;
v_x_1580_ = v_tail_1583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(lean_object* v_i_1607_, lean_object* v_source_1608_, lean_object* v_target_1609_){
_start:
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = lean_array_get_size(v_source_1608_);
v___x_1611_ = lean_nat_dec_lt(v_i_1607_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_dec_ref(v_source_1608_);
lean_dec(v_i_1607_);
return v_target_1609_;
}
else
{
lean_object* v_es_1612_; lean_object* v___x_1613_; lean_object* v_source_1614_; lean_object* v_target_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_es_1612_ = lean_array_fget(v_source_1608_, v_i_1607_);
v___x_1613_ = lean_box(0);
v_source_1614_ = lean_array_fset(v_source_1608_, v_i_1607_, v___x_1613_);
v_target_1615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(v_target_1609_, v_es_1612_);
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_i_1607_, v___x_1616_);
lean_dec(v_i_1607_);
v_i_1607_ = v___x_1617_;
v_source_1608_ = v_source_1614_;
v_target_1609_ = v_target_1615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(lean_object* v_data_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_nbuckets_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1620_ = lean_array_get_size(v_data_1619_);
v___x_1621_ = lean_unsigned_to_nat(2u);
v_nbuckets_1622_ = lean_nat_mul(v___x_1620_, v___x_1621_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_mk_array(v_nbuckets_1622_, v___x_1624_);
v___x_1626_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(v___x_1623_, v_data_1619_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(lean_object* v_m_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_){
_start:
{
lean_object* v_size_1630_; lean_object* v_buckets_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1674_; 
v_size_1630_ = lean_ctor_get(v_m_1627_, 0);
v_buckets_1631_ = lean_ctor_get(v_m_1627_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_m_1627_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1633_ = v_m_1627_;
v_isShared_1634_ = v_isSharedCheck_1674_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_buckets_1631_);
lean_inc(v_size_1630_);
lean_dec(v_m_1627_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1674_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; uint64_t v___x_1636_; uint64_t v___x_1637_; uint64_t v___x_1638_; uint64_t v_fold_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; lean_object* v_bkt_1648_; uint8_t v___x_1649_; 
v___x_1635_ = lean_array_get_size(v_buckets_1631_);
v___x_1636_ = l_Lean_Expr_hash(v_a_1628_);
v___x_1637_ = 32ULL;
v___x_1638_ = lean_uint64_shift_right(v___x_1636_, v___x_1637_);
v_fold_1639_ = lean_uint64_xor(v___x_1636_, v___x_1638_);
v___x_1640_ = 16ULL;
v___x_1641_ = lean_uint64_shift_right(v_fold_1639_, v___x_1640_);
v___x_1642_ = lean_uint64_xor(v_fold_1639_, v___x_1641_);
v___x_1643_ = lean_uint64_to_usize(v___x_1642_);
v___x_1644_ = lean_usize_of_nat(v___x_1635_);
v___x_1645_ = ((size_t)1ULL);
v___x_1646_ = lean_usize_sub(v___x_1644_, v___x_1645_);
v___x_1647_ = lean_usize_land(v___x_1643_, v___x_1646_);
v_bkt_1648_ = lean_array_uget_borrowed(v_buckets_1631_, v___x_1647_);
v___x_1649_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_1628_, v_bkt_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v_size_x27_1651_; lean_object* v___x_1652_; lean_object* v_buckets_x27_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v_size_x27_1651_ = lean_nat_add(v_size_1630_, v___x_1650_);
lean_dec(v_size_1630_);
lean_inc(v_bkt_1648_);
v___x_1652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1628_);
lean_ctor_set(v___x_1652_, 1, v_b_1629_);
lean_ctor_set(v___x_1652_, 2, v_bkt_1648_);
v_buckets_x27_1653_ = lean_array_uset(v_buckets_1631_, v___x_1647_, v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(4u);
v___x_1655_ = lean_nat_mul(v_size_x27_1651_, v___x_1654_);
v___x_1656_ = lean_unsigned_to_nat(3u);
v___x_1657_ = lean_nat_div(v___x_1655_, v___x_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_array_get_size(v_buckets_x27_1653_);
v___x_1659_ = lean_nat_dec_le(v___x_1657_, v___x_1658_);
lean_dec(v___x_1657_);
if (v___x_1659_ == 0)
{
lean_object* v_val_1660_; lean_object* v___x_1662_; 
v_val_1660_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(v_buckets_x27_1653_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v_val_1660_);
lean_ctor_set(v___x_1633_, 0, v_size_x27_1651_);
v___x_1662_ = v___x_1633_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_size_x27_1651_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_val_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
else
{
lean_object* v___x_1665_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v_buckets_x27_1653_);
lean_ctor_set(v___x_1633_, 0, v_size_x27_1651_);
v___x_1665_ = v___x_1633_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_size_x27_1651_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_buckets_x27_1653_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v___x_1667_; lean_object* v_buckets_x27_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_inc(v_bkt_1648_);
v___x_1667_ = lean_box(0);
v_buckets_x27_1668_ = lean_array_uset(v_buckets_1631_, v___x_1647_, v___x_1667_);
v___x_1669_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_1628_, v_b_1629_, v_bkt_1648_);
v___x_1670_ = lean_array_uset(v_buckets_x27_1668_, v___x_1647_, v___x_1669_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v___x_1670_);
v___x_1672_ = v___x_1633_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_size_1630_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
if (lean_obj_tag(v_x_1676_) == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_box(0);
return v___x_1677_;
}
else
{
lean_object* v_key_1678_; lean_object* v_value_1679_; lean_object* v_tail_1680_; uint8_t v___x_1681_; 
v_key_1678_ = lean_ctor_get(v_x_1676_, 0);
v_value_1679_ = lean_ctor_get(v_x_1676_, 1);
v_tail_1680_ = lean_ctor_get(v_x_1676_, 2);
v___x_1681_ = lean_expr_eqv(v_key_1678_, v_a_1675_);
if (v___x_1681_ == 0)
{
v_x_1676_ = v_tail_1680_;
goto _start;
}
else
{
lean_object* v___x_1683_; 
lean_inc(v_value_1679_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_value_1679_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg___boxed(lean_object* v_a_1684_, lean_object* v_x_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_1684_, v_x_1685_);
lean_dec(v_x_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(lean_object* v_m_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_buckets_1689_; lean_object* v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v_fold_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; uint64_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_buckets_1689_ = lean_ctor_get(v_m_1687_, 1);
v___x_1690_ = lean_array_get_size(v_buckets_1689_);
v___x_1691_ = l_Lean_Expr_hash(v_a_1688_);
v___x_1692_ = 32ULL;
v___x_1693_ = lean_uint64_shift_right(v___x_1691_, v___x_1692_);
v_fold_1694_ = lean_uint64_xor(v___x_1691_, v___x_1693_);
v___x_1695_ = 16ULL;
v___x_1696_ = lean_uint64_shift_right(v_fold_1694_, v___x_1695_);
v___x_1697_ = lean_uint64_xor(v_fold_1694_, v___x_1696_);
v___x_1698_ = lean_uint64_to_usize(v___x_1697_);
v___x_1699_ = lean_usize_of_nat(v___x_1690_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_sub(v___x_1699_, v___x_1700_);
v___x_1702_ = lean_usize_land(v___x_1698_, v___x_1701_);
v___x_1703_ = lean_array_uget_borrowed(v_buckets_1689_, v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_1688_, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_m_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_1705_, v_a_1706_);
lean_dec_ref(v_a_1706_);
lean_dec_ref(v_m_1705_);
return v_res_1707_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1708_; double v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_float_of_nat(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(lean_object* v_cls_1713_, lean_object* v_msg_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_ref_1720_; lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1766_; 
v_ref_1720_ = lean_ctor_get(v___y_1717_, 5);
v___x_1721_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1766_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1766_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v_traceState_1727_; lean_object* v_env_1728_; lean_object* v_nextMacroScope_1729_; lean_object* v_ngen_1730_; lean_object* v_auxDeclNGen_1731_; lean_object* v_cache_1732_; lean_object* v_messages_1733_; lean_object* v_infoState_1734_; lean_object* v_snapshotTasks_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1765_; 
v___x_1726_ = lean_st_ref_take(v___y_1718_);
v_traceState_1727_ = lean_ctor_get(v___x_1726_, 4);
v_env_1728_ = lean_ctor_get(v___x_1726_, 0);
v_nextMacroScope_1729_ = lean_ctor_get(v___x_1726_, 1);
v_ngen_1730_ = lean_ctor_get(v___x_1726_, 2);
v_auxDeclNGen_1731_ = lean_ctor_get(v___x_1726_, 3);
v_cache_1732_ = lean_ctor_get(v___x_1726_, 5);
v_messages_1733_ = lean_ctor_get(v___x_1726_, 6);
v_infoState_1734_ = lean_ctor_get(v___x_1726_, 7);
v_snapshotTasks_1735_ = lean_ctor_get(v___x_1726_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1737_ = v___x_1726_;
v_isShared_1738_ = v_isSharedCheck_1765_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snapshotTasks_1735_);
lean_inc(v_infoState_1734_);
lean_inc(v_messages_1733_);
lean_inc(v_cache_1732_);
lean_inc(v_traceState_1727_);
lean_inc(v_auxDeclNGen_1731_);
lean_inc(v_ngen_1730_);
lean_inc(v_nextMacroScope_1729_);
lean_inc(v_env_1728_);
lean_dec(v___x_1726_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1765_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
uint64_t v_tid_1739_; lean_object* v_traces_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1764_; 
v_tid_1739_ = lean_ctor_get_uint64(v_traceState_1727_, sizeof(void*)*1);
v_traces_1740_ = lean_ctor_get(v_traceState_1727_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_traceState_1727_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1742_ = v_traceState_1727_;
v_isShared_1743_ = v_isSharedCheck_1764_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_traces_1740_);
lean_dec(v_traceState_1727_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1764_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; double v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0);
v___x_1746_ = 0;
v___x_1747_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1));
v___x_1748_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1748_, 0, v_cls_1713_);
lean_ctor_set(v___x_1748_, 1, v___x_1744_);
lean_ctor_set(v___x_1748_, 2, v___x_1747_);
lean_ctor_set_float(v___x_1748_, sizeof(void*)*3, v___x_1745_);
lean_ctor_set_float(v___x_1748_, sizeof(void*)*3 + 8, v___x_1745_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*3 + 16, v___x_1746_);
v___x_1749_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2));
v___x_1750_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v_a_1722_);
lean_ctor_set(v___x_1750_, 2, v___x_1749_);
lean_inc(v_ref_1720_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_ref_1720_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_PersistentArray_push___redArg(v_traces_1740_, v___x_1751_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1752_);
v___x_1754_ = v___x_1742_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1752_);
lean_ctor_set_uint64(v_reuseFailAlloc_1763_, sizeof(void*)*1, v_tid_1739_);
v___x_1754_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 4, v___x_1754_);
v___x_1756_ = v___x_1737_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_env_1728_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1729_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1730_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v_cache_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1733_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1734_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1735_);
v___x_1756_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1757_ = lean_st_ref_set(v___y_1718_, v___x_1756_);
v___x_1758_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1758_);
v___x_1760_ = v___x_1724_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___boxed(lean_object* v_cls_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1775_, lean_object* v_b_1776_){
_start:
{
lean_object* v_array_1777_; lean_object* v_start_1778_; lean_object* v_stop_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_array_1777_ = lean_ctor_get(v_a_1775_, 0);
v_start_1778_ = lean_ctor_get(v_a_1775_, 1);
v_stop_1779_ = lean_ctor_get(v_a_1775_, 2);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1781_ = v_a_1775_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_stop_1779_);
lean_inc(v_start_1778_);
lean_inc(v_array_1777_);
lean_dec(v_a_1775_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_nat_dec_lt(v_start_1778_, v_stop_1779_);
if (v___x_1783_ == 0)
{
lean_del_object(v___x_1781_);
lean_dec(v_stop_1779_);
lean_dec(v_start_1778_);
lean_dec_ref(v_array_1777_);
return v_b_1776_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_add(v_start_1778_, v___x_1784_);
lean_inc_ref(v_array_1777_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v___x_1785_);
v___x_1787_ = v___x_1781_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_array_1777_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_stop_1779_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_array_fget(v_array_1777_, v_start_1778_);
lean_dec(v_start_1778_);
lean_dec_ref(v_array_1777_);
v___x_1789_ = lean_array_push(v_b_1776_, v___x_1788_);
v_a_1775_ = v___x_1787_;
v_b_1776_ = v___x_1789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1793_, lean_object* v_recFnName_1794_, lean_object* v_fixedPrefixSize_1795_, lean_object* v_F_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_expr_instantiate1(v_body_1793_, v_x_1797_);
v___x_1808_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1794_, v_fixedPrefixSize_1795_, v_F_1796_, v___x_1807_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; uint8_t v___x_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___x_1812_ = lean_array_push(v___x_1811_, v_x_1797_);
v___x_1813_ = 0;
v___x_1814_ = 1;
v___x_1815_ = 1;
v___x_1816_ = l_Lean_Meta_mkLambdaFVars(v___x_1812_, v_a_1809_, v___x_1813_, v___x_1814_, v___x_1813_, v___x_1814_, v___x_1815_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v___x_1812_);
return v___x_1816_;
}
else
{
lean_dec_ref(v_x_1797_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1817_, lean_object* v_recFnName_1818_, lean_object* v_fixedPrefixSize_1819_, lean_object* v_F_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1817_, v_recFnName_1818_, v_fixedPrefixSize_1819_, v_F_1820_, v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v_body_1817_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1832_, lean_object* v_recFnName_1833_, lean_object* v_fixedPrefixSize_1834_, lean_object* v_F_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_expr_instantiate1(v_body_1832_, v_x_1836_);
v___x_1847_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1833_, v_fixedPrefixSize_1834_, v_F_1835_, v___x_1846_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = lean_unsigned_to_nat(1u);
v___x_1850_ = lean_mk_empty_array_with_capacity(v___x_1849_);
v___x_1851_ = lean_array_push(v___x_1850_, v_x_1836_);
v___x_1852_ = 0;
v___x_1853_ = 1;
v___x_1854_ = 1;
v___x_1855_ = l_Lean_Meta_mkForallFVars(v___x_1851_, v_a_1848_, v___x_1852_, v___x_1853_, v___x_1853_, v___x_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec_ref(v___x_1851_);
return v___x_1855_;
}
else
{
lean_dec_ref(v_x_1836_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1856_, lean_object* v_recFnName_1857_, lean_object* v_fixedPrefixSize_1858_, lean_object* v_F_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1856_, v_recFnName_1857_, v_fixedPrefixSize_1858_, v_F_1859_, v_x_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v_body_1856_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1871_, lean_object* v_recFnName_1872_, lean_object* v_fixedPrefixSize_1873_, lean_object* v_F_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1871_, v_recFnName_1872_, v_fixedPrefixSize_1873_, v_F_1874_, v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_body_1871_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1888_, lean_object* v_fixedPrefixSize_1889_, lean_object* v_F_1890_, size_t v_sz_1891_, size_t v_i_1892_, lean_object* v_bs_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_usize_dec_lt(v_i_1892_, v_sz_1891_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_bs_1893_);
return v___x_1904_;
}
else
{
lean_object* v_v_1905_; lean_object* v___x_1906_; 
v_v_1905_ = lean_array_uget_borrowed(v_bs_1893_, v_i_1892_);
lean_inc(v_v_1905_);
lean_inc_ref(v_F_1890_);
lean_inc(v_fixedPrefixSize_1889_);
lean_inc(v_recFnName_1888_);
v___x_1906_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1888_, v_fixedPrefixSize_1889_, v_F_1890_, v_v_1905_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v_bs_x27_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
v___x_1908_ = lean_unsigned_to_nat(0u);
v_bs_x27_1909_ = lean_array_uset(v_bs_1893_, v_i_1892_, v___x_1908_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1892_, v___x_1910_);
v___x_1912_ = lean_array_uset(v_bs_x27_1909_, v_i_1892_, v_a_1907_);
v_i_1892_ = v___x_1911_;
v_bs_1893_ = v___x_1912_;
goto _start;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v_bs_1893_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
v_a_1914_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1906_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1906_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1929_, lean_object* v_fixedPrefixSize_1930_, lean_object* v_F_1931_, lean_object* v_e_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1954_ = l_Lean_Expr_getAppNumArgs(v_e_1932_);
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_add(v_fixedPrefixSize_1930_, v___x_1955_);
v___x_1957_ = lean_nat_dec_lt(v___x_1954_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v_dummy_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_args_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_dummy_1958_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_1954_);
v___x_1959_ = lean_mk_array(v___x_1954_, v_dummy_1958_);
v___x_1960_ = lean_nat_sub(v___x_1954_, v___x_1955_);
lean_dec(v___x_1954_);
v_args_1961_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1932_, v___x_1959_, v___x_1960_);
v___x_1962_ = l_Lean_instInhabitedExpr;
v___x_1963_ = lean_array_get(v___x_1962_, v_args_1961_, v_fixedPrefixSize_1930_);
lean_inc_ref(v_F_1931_);
lean_inc(v_fixedPrefixSize_1930_);
lean_inc(v_recFnName_1929_);
v___x_1964_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1929_, v_fixedPrefixSize_1930_, v_F_1931_, v___x_1963_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
lean_inc_ref(v_F_1931_);
v___x_1966_ = l_Lean_Expr_app___override(v_F_1931_, v_a_1965_);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc_ref(v___x_1966_);
v___x_1967_ = lean_infer_type(v___x_1966_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_1969_ = lean_whnf(v_a_1968_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = l_Lean_Expr_bindingDomain_x21(v_a_1970_);
lean_dec(v_a_1970_);
lean_inc_ref(v_a_1939_);
v___x_1972_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1971_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; lean_object* v_lower_1976_; lean_object* v_upper_1977_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = l_Lean_Expr_app___override(v___x_1966_, v_a_1973_);
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_array_get_size(v_args_1961_);
v___x_2003_ = lean_nat_dec_le(v___x_1956_, v___x_2001_);
if (v___x_2003_ == 0)
{
v_lower_1976_ = v___x_1956_;
v_upper_1977_ = v___x_2002_;
goto v___jp_1975_;
}
else
{
lean_dec(v___x_1956_);
v_lower_1976_ = v___x_2001_;
v_upper_1977_ = v___x_2002_;
goto v___jp_1975_;
}
v___jp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; size_t v_sz_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1978_ = l_Array_toSubarray___redArg(v_args_1961_, v_lower_1976_, v_upper_1977_);
v___x_1979_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1980_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1978_, v___x_1979_);
v_sz_1981_ = lean_array_size(v___x_1980_);
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1929_, v_fixedPrefixSize_1930_, v_F_1931_, v_sz_1981_, v___x_1982_, v___x_1980_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_mkAppN(v___x_1974_, v_a_1984_);
lean_dec(v_a_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___x_1974_);
v_a_1993_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1983_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1983_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_args_1961_);
lean_dec(v___x_1956_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
return v___x_1972_;
}
}
else
{
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_args_1961_);
lean_dec(v___x_1956_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
return v___x_1969_;
}
}
else
{
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_args_1961_);
lean_dec(v___x_1956_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
return v___x_1967_;
}
}
else
{
lean_dec_ref(v_args_1961_);
lean_dec(v___x_1956_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
return v___x_1964_;
}
}
else
{
lean_object* v_cls_2004_; lean_object* v___x_2005_; 
lean_dec(v___x_1956_);
lean_dec(v___x_1954_);
v_cls_2004_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_2005_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2004_, v_a_1939_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; uint8_t v___x_2007_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = lean_unbox(v_a_2006_);
lean_dec(v_a_2006_);
if (v___x_2007_ == 0)
{
v___y_1943_ = v_a_1933_;
v___y_1944_ = v_a_1934_;
v___y_1945_ = v_a_1935_;
v___y_1946_ = v_a_1936_;
v___y_1947_ = v_a_1937_;
v___y_1948_ = v_a_1938_;
v___y_1949_ = v_a_1939_;
v___y_1950_ = v_a_1940_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3);
lean_inc_ref(v_e_1932_);
v___x_2009_ = l_Lean_indentExpr(v_e_1932_);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_2004_, v___x_2010_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref(v___x_2011_);
v___y_1943_ = v_a_1933_;
v___y_1944_ = v_a_1934_;
v___y_1945_ = v_a_1935_;
v___y_1946_ = v_a_1936_;
v___y_1947_ = v_a_1937_;
v___y_1948_ = v_a_1938_;
v___y_1949_ = v_a_1939_;
v___y_1950_ = v_a_1940_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_e_1932_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v_e_1932_);
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
v_a_2020_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2005_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2005_);
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
v___jp_1942_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_etaExpand(v_e_1932_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1929_, v_fixedPrefixSize_1930_, v_F_1931_, v_a_1952_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1953_;
}
else
{
lean_dec_ref(v_F_1931_);
lean_dec(v_fixedPrefixSize_1930_);
lean_dec(v_recFnName_1929_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(lean_object* v_recFnName_2028_, lean_object* v_fixedPrefixSize_2029_, lean_object* v_F_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
if (lean_obj_tag(v_x_2031_) == 5)
{
lean_object* v_fn_2043_; lean_object* v_arg_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_fn_2043_ = lean_ctor_get(v_x_2031_, 0);
lean_inc_ref(v_fn_2043_);
v_arg_2044_ = lean_ctor_get(v_x_2031_, 1);
lean_inc_ref(v_arg_2044_);
lean_dec_ref(v_x_2031_);
v___x_2045_ = lean_array_set(v_x_2032_, v_x_2033_, v_arg_2044_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_sub(v_x_2033_, v___x_2046_);
lean_dec(v_x_2033_);
v_x_2031_ = v_fn_2043_;
v_x_2032_ = v___x_2045_;
v_x_2033_ = v___x_2047_;
goto _start;
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_x_2033_);
lean_inc_ref(v_F_2030_);
lean_inc(v_fixedPrefixSize_2029_);
lean_inc(v_recFnName_2028_);
v___x_2049_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2028_, v_fixedPrefixSize_2029_, v_F_2030_, v_x_2031_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; size_t v_sz_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v_sz_2051_ = lean_array_size(v_x_2032_);
v___x_2052_ = ((size_t)0ULL);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2028_, v_fixedPrefixSize_2029_, v_F_2030_, v_sz_2051_, v___x_2052_, v_x_2032_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2062_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = l_Lean_mkAppN(v_a_2050_, v_a_2054_);
lean_dec(v_a_2054_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2050_);
v_a_2063_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2053_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2053_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_dec_ref(v_x_2032_);
lean_dec_ref(v_F_2030_);
lean_dec(v_fixedPrefixSize_2029_);
lean_dec(v_recFnName_2028_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2071_, lean_object* v_fixedPrefixSize_2072_, lean_object* v_F_2073_, lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Expr_isAppOf(v_e_2074_, v_recFnName_2071_);
if (v___x_2084_ == 0)
{
lean_object* v_dummy_2085_; lean_object* v_nargs_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_dummy_2085_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_2086_ = l_Lean_Expr_getAppNumArgs(v_e_2074_);
lean_inc(v_nargs_2086_);
v___x_2087_ = lean_mk_array(v_nargs_2086_, v_dummy_2085_);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_sub(v_nargs_2086_, v___x_2088_);
lean_dec(v_nargs_2086_);
v___x_2090_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2071_, v_fixedPrefixSize_2072_, v_F_2073_, v_e_2074_, v___x_2087_, v___x_2089_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2071_, v_fixedPrefixSize_2072_, v_F_2073_, v_e_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2091_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0));
v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2));
v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(lean_object* v___x_2098_, lean_object* v_b_2099_, lean_object* v_recFnName_2100_, lean_object* v_fixedPrefixSize_2101_, uint8_t v___x_2102_, lean_object* v___x_2103_, lean_object* v_a_2104_, lean_object* v_e_2105_, lean_object* v_xs_2106_, lean_object* v_altBody_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_xs_2106_);
v___x_2125_ = lean_nat_dec_eq(v___x_2124_, v___x_2103_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_altBody_2107_);
lean_dec(v_fixedPrefixSize_2101_);
lean_dec(v_recFnName_2100_);
lean_dec_ref(v___x_2098_);
v___x_2126_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1);
v___x_2127_ = l_Lean_indentExpr(v_a_2104_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_indentExpr(v_e_2105_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_2132_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_dec_ref(v_e_2105_);
lean_dec_ref(v_a_2104_);
goto v___jp_2117_;
}
v___jp_2117_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_array_get_borrowed(v___x_2098_, v_xs_2106_, v_b_2099_);
lean_inc(v___x_2118_);
v___x_2119_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2100_, v_fixedPrefixSize_2101_, v___x_2118_, v_altBody_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; uint8_t v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = 0;
v___x_2122_ = 1;
v___x_2123_ = l_Lean_Meta_mkLambdaFVars(v_xs_2106_, v_a_2120_, v___x_2121_, v___x_2102_, v___x_2121_, v___x_2102_, v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2123_;
}
else
{
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed(lean_object** _args){
lean_object* v___x_2142_ = _args[0];
lean_object* v_b_2143_ = _args[1];
lean_object* v_recFnName_2144_ = _args[2];
lean_object* v_fixedPrefixSize_2145_ = _args[3];
lean_object* v___x_2146_ = _args[4];
lean_object* v___x_2147_ = _args[5];
lean_object* v_a_2148_ = _args[6];
lean_object* v_e_2149_ = _args[7];
lean_object* v_xs_2150_ = _args[8];
lean_object* v_altBody_2151_ = _args[9];
lean_object* v___y_2152_ = _args[10];
lean_object* v___y_2153_ = _args[11];
lean_object* v___y_2154_ = _args[12];
lean_object* v___y_2155_ = _args[13];
lean_object* v___y_2156_ = _args[14];
lean_object* v___y_2157_ = _args[15];
lean_object* v___y_2158_ = _args[16];
lean_object* v___y_2159_ = _args[17];
lean_object* v___y_2160_ = _args[18];
_start:
{
uint8_t v___x_67097__boxed_2161_; lean_object* v_res_2162_; 
v___x_67097__boxed_2161_ = lean_unbox(v___x_2146_);
v_res_2162_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(v___x_2142_, v_b_2143_, v_recFnName_2144_, v_fixedPrefixSize_2145_, v___x_67097__boxed_2161_, v___x_2147_, v_a_2148_, v_e_2149_, v_xs_2150_, v_altBody_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v_xs_2150_);
lean_dec(v___x_2147_);
lean_dec(v_b_2143_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(lean_object* v_recFnName_2163_, lean_object* v_fixedPrefixSize_2164_, lean_object* v_e_2165_, lean_object* v_as_2166_, lean_object* v_bs_2167_, lean_object* v_i_2168_, lean_object* v_cs_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_array_get_size(v_as_2166_);
v___x_2180_ = lean_nat_dec_lt(v_i_2168_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
lean_dec(v_i_2168_);
lean_dec_ref(v_e_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_cs_2169_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_array_get_size(v_bs_2167_);
v___x_2183_ = lean_nat_dec_lt(v_i_2168_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec(v_i_2168_);
lean_dec_ref(v_e_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_cs_2169_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v_b_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2185_ = l_Lean_instInhabitedExpr;
v_a_2186_ = lean_array_fget_borrowed(v_as_2166_, v_i_2168_);
v_b_2187_ = lean_array_fget_borrowed(v_bs_2167_, v_i_2168_);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_add(v_b_2187_, v___x_2188_);
v___x_2190_ = lean_box(v___x_2183_);
lean_inc_ref(v_e_2165_);
lean_inc(v_a_2186_);
lean_inc(v___x_2189_);
lean_inc(v_fixedPrefixSize_2164_);
lean_inc(v_recFnName_2163_);
lean_inc(v_b_2187_);
v___f_2191_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2191_, 0, v___x_2185_);
lean_closure_set(v___f_2191_, 1, v_b_2187_);
lean_closure_set(v___f_2191_, 2, v_recFnName_2163_);
lean_closure_set(v___f_2191_, 3, v_fixedPrefixSize_2164_);
lean_closure_set(v___f_2191_, 4, v___x_2190_);
lean_closure_set(v___f_2191_, 5, v___x_2189_);
lean_closure_set(v___f_2191_, 6, v_a_2186_);
lean_closure_set(v___f_2191_, 7, v_e_2165_);
v___x_2192_ = 0;
lean_inc(v_a_2186_);
v___x_2193_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_a_2186_, v___x_2189_, v___f_2191_, v___x_2192_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = lean_nat_add(v_i_2168_, v___x_2188_);
lean_dec(v_i_2168_);
v___x_2196_ = lean_array_push(v_cs_2169_, v_a_2194_);
v_i_2168_ = v___x_2195_;
v_cs_2169_ = v___x_2196_;
goto _start;
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_cs_2169_);
lean_dec(v_i_2168_);
lean_dec_ref(v_e_2165_);
lean_dec(v_fixedPrefixSize_2164_);
lean_dec(v_recFnName_2163_);
v_a_2198_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2193_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2193_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2206_, lean_object* v_fixedPrefixSize_2207_, lean_object* v_F_2208_, lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
switch(lean_obj_tag(v_e_2209_))
{
case 6:
{
lean_object* v_binderName_2219_; lean_object* v_binderType_2220_; lean_object* v_body_2221_; uint8_t v_binderInfo_2222_; lean_object* v___x_2223_; 
v_binderName_2219_ = lean_ctor_get(v_e_2209_, 0);
lean_inc(v_binderName_2219_);
v_binderType_2220_ = lean_ctor_get(v_e_2209_, 1);
lean_inc_ref(v_binderType_2220_);
v_body_2221_ = lean_ctor_get(v_e_2209_, 2);
lean_inc_ref(v_body_2221_);
v_binderInfo_2222_ = lean_ctor_get_uint8(v_e_2209_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2209_);
lean_inc_ref(v_F_2208_);
lean_inc(v_fixedPrefixSize_2207_);
lean_inc(v_recFnName_2206_);
v___x_2223_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_binderType_2220_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___f_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2223_);
v___f_2225_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2225_, 0, v_body_2221_);
lean_closure_set(v___f_2225_, 1, v_recFnName_2206_);
lean_closure_set(v___f_2225_, 2, v_fixedPrefixSize_2207_);
lean_closure_set(v___f_2225_, 3, v_F_2208_);
v___x_2226_ = 0;
v___x_2227_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2219_, v_binderInfo_2222_, v_a_2224_, v___f_2225_, v___x_2226_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2227_;
}
else
{
lean_dec_ref(v_body_2221_);
lean_dec(v_binderName_2219_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
return v___x_2223_;
}
}
case 7:
{
lean_object* v_binderName_2228_; lean_object* v_binderType_2229_; lean_object* v_body_2230_; uint8_t v_binderInfo_2231_; lean_object* v___x_2232_; 
v_binderName_2228_ = lean_ctor_get(v_e_2209_, 0);
lean_inc(v_binderName_2228_);
v_binderType_2229_ = lean_ctor_get(v_e_2209_, 1);
lean_inc_ref(v_binderType_2229_);
v_body_2230_ = lean_ctor_get(v_e_2209_, 2);
lean_inc_ref(v_body_2230_);
v_binderInfo_2231_ = lean_ctor_get_uint8(v_e_2209_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2209_);
lean_inc_ref(v_F_2208_);
lean_inc(v_fixedPrefixSize_2207_);
lean_inc(v_recFnName_2206_);
v___x_2232_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_binderType_2229_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___f_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___f_2234_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2234_, 0, v_body_2230_);
lean_closure_set(v___f_2234_, 1, v_recFnName_2206_);
lean_closure_set(v___f_2234_, 2, v_fixedPrefixSize_2207_);
lean_closure_set(v___f_2234_, 3, v_F_2208_);
v___x_2235_ = 0;
v___x_2236_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2228_, v_binderInfo_2231_, v_a_2233_, v___f_2234_, v___x_2235_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2236_;
}
else
{
lean_dec_ref(v_body_2230_);
lean_dec(v_binderName_2228_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
return v___x_2232_;
}
}
case 8:
{
lean_object* v_declName_2237_; lean_object* v_type_2238_; lean_object* v_value_2239_; lean_object* v_body_2240_; uint8_t v_nondep_2241_; lean_object* v___x_2242_; 
v_declName_2237_ = lean_ctor_get(v_e_2209_, 0);
lean_inc(v_declName_2237_);
v_type_2238_ = lean_ctor_get(v_e_2209_, 1);
lean_inc_ref(v_type_2238_);
v_value_2239_ = lean_ctor_get(v_e_2209_, 2);
lean_inc_ref(v_value_2239_);
v_body_2240_ = lean_ctor_get(v_e_2209_, 3);
lean_inc_ref(v_body_2240_);
v_nondep_2241_ = lean_ctor_get_uint8(v_e_2209_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2209_);
lean_inc_ref(v_F_2208_);
lean_inc(v_fixedPrefixSize_2207_);
lean_inc(v_recFnName_2206_);
v___x_2242_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_type_2238_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref(v___x_2242_);
lean_inc_ref(v_F_2208_);
lean_inc(v_fixedPrefixSize_2207_);
lean_inc(v_recFnName_2206_);
v___x_2244_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_value_2239_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___f_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2246_, 0, v_body_2240_);
lean_closure_set(v___f_2246_, 1, v_recFnName_2206_);
lean_closure_set(v___f_2246_, 2, v_fixedPrefixSize_2207_);
lean_closure_set(v___f_2246_, 3, v_F_2208_);
v___x_2247_ = 0;
v___x_2248_ = 0;
v___x_2249_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_declName_2237_, v_a_2243_, v_a_2245_, v___f_2246_, v_nondep_2241_, v___x_2247_, v___x_2248_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2249_;
}
else
{
lean_dec(v_a_2243_);
lean_dec_ref(v_body_2240_);
lean_dec(v_declName_2237_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
return v___x_2244_;
}
}
else
{
lean_dec_ref(v_body_2240_);
lean_dec_ref(v_value_2239_);
lean_dec(v_declName_2237_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
return v___x_2242_;
}
}
case 10:
{
lean_object* v_data_2250_; lean_object* v_expr_2251_; lean_object* v___x_2252_; 
v_data_2250_ = lean_ctor_get(v_e_2209_, 0);
lean_inc(v_data_2250_);
v_expr_2251_ = lean_ctor_get(v_e_2209_, 1);
lean_inc_ref(v_expr_2251_);
v___x_2252_ = l_Lean_getRecAppSyntax_x3f(v_e_2209_);
lean_dec_ref(v_e_2209_);
if (lean_obj_tag(v___x_2252_) == 1)
{
lean_object* v_val_2253_; lean_object* v_fileName_2254_; lean_object* v_fileMap_2255_; lean_object* v_options_2256_; lean_object* v_currRecDepth_2257_; lean_object* v_maxRecDepth_2258_; lean_object* v_ref_2259_; lean_object* v_currNamespace_2260_; lean_object* v_openDecls_2261_; lean_object* v_initHeartbeats_2262_; lean_object* v_maxHeartbeats_2263_; lean_object* v_quotContext_2264_; lean_object* v_currMacroScope_2265_; uint8_t v_diag_2266_; lean_object* v_cancelTk_x3f_2267_; uint8_t v_suppressElabErrors_2268_; lean_object* v_inheritedTraceOptions_2269_; lean_object* v_ref_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v_data_2250_);
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2253_);
lean_dec_ref(v___x_2252_);
v_fileName_2254_ = lean_ctor_get(v_a_2216_, 0);
v_fileMap_2255_ = lean_ctor_get(v_a_2216_, 1);
v_options_2256_ = lean_ctor_get(v_a_2216_, 2);
v_currRecDepth_2257_ = lean_ctor_get(v_a_2216_, 3);
v_maxRecDepth_2258_ = lean_ctor_get(v_a_2216_, 4);
v_ref_2259_ = lean_ctor_get(v_a_2216_, 5);
v_currNamespace_2260_ = lean_ctor_get(v_a_2216_, 6);
v_openDecls_2261_ = lean_ctor_get(v_a_2216_, 7);
v_initHeartbeats_2262_ = lean_ctor_get(v_a_2216_, 8);
v_maxHeartbeats_2263_ = lean_ctor_get(v_a_2216_, 9);
v_quotContext_2264_ = lean_ctor_get(v_a_2216_, 10);
v_currMacroScope_2265_ = lean_ctor_get(v_a_2216_, 11);
v_diag_2266_ = lean_ctor_get_uint8(v_a_2216_, sizeof(void*)*14);
v_cancelTk_x3f_2267_ = lean_ctor_get(v_a_2216_, 12);
v_suppressElabErrors_2268_ = lean_ctor_get_uint8(v_a_2216_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2269_ = lean_ctor_get(v_a_2216_, 13);
v_ref_2270_ = l_Lean_replaceRef(v_val_2253_, v_ref_2259_);
lean_dec(v_val_2253_);
lean_inc_ref(v_inheritedTraceOptions_2269_);
lean_inc(v_cancelTk_x3f_2267_);
lean_inc(v_currMacroScope_2265_);
lean_inc(v_quotContext_2264_);
lean_inc(v_maxHeartbeats_2263_);
lean_inc(v_initHeartbeats_2262_);
lean_inc(v_openDecls_2261_);
lean_inc(v_currNamespace_2260_);
lean_inc(v_maxRecDepth_2258_);
lean_inc(v_currRecDepth_2257_);
lean_inc_ref(v_options_2256_);
lean_inc_ref(v_fileMap_2255_);
lean_inc_ref(v_fileName_2254_);
v___x_2271_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2271_, 0, v_fileName_2254_);
lean_ctor_set(v___x_2271_, 1, v_fileMap_2255_);
lean_ctor_set(v___x_2271_, 2, v_options_2256_);
lean_ctor_set(v___x_2271_, 3, v_currRecDepth_2257_);
lean_ctor_set(v___x_2271_, 4, v_maxRecDepth_2258_);
lean_ctor_set(v___x_2271_, 5, v_ref_2270_);
lean_ctor_set(v___x_2271_, 6, v_currNamespace_2260_);
lean_ctor_set(v___x_2271_, 7, v_openDecls_2261_);
lean_ctor_set(v___x_2271_, 8, v_initHeartbeats_2262_);
lean_ctor_set(v___x_2271_, 9, v_maxHeartbeats_2263_);
lean_ctor_set(v___x_2271_, 10, v_quotContext_2264_);
lean_ctor_set(v___x_2271_, 11, v_currMacroScope_2265_);
lean_ctor_set(v___x_2271_, 12, v_cancelTk_x3f_2267_);
lean_ctor_set(v___x_2271_, 13, v_inheritedTraceOptions_2269_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*14, v_diag_2266_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*14 + 1, v_suppressElabErrors_2268_);
v___x_2272_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_expr_2251_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v___x_2271_, v_a_2217_);
lean_dec_ref(v___x_2271_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v___x_2252_);
v___x_2273_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_expr_2251_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = l_Lean_mkMData(v_data_2250_, v_a_2274_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_dec(v_data_2250_);
return v___x_2273_;
}
}
}
case 11:
{
lean_object* v_typeName_2283_; lean_object* v_idx_2284_; lean_object* v_struct_2285_; lean_object* v___x_2286_; 
v_typeName_2283_ = lean_ctor_get(v_e_2209_, 0);
lean_inc(v_typeName_2283_);
v_idx_2284_ = lean_ctor_get(v_e_2209_, 1);
lean_inc(v_idx_2284_);
v_struct_2285_ = lean_ctor_get(v_e_2209_, 2);
lean_inc_ref(v_struct_2285_);
lean_dec_ref(v_e_2209_);
v___x_2286_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_struct_2285_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2295_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = l_Lean_mkProj(v_typeName_2283_, v_idx_2284_, v_a_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
else
{
lean_dec(v_idx_2284_);
lean_dec(v_typeName_2283_);
return v___x_2286_;
}
}
case 4:
{
uint8_t v___x_2296_; 
v___x_2296_ = l_Lean_Expr_isConstOf(v_e_2209_, v_recFnName_2206_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_e_2209_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2298_;
}
}
case 5:
{
uint8_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = 1;
lean_inc_ref(v_e_2209_);
v___x_2300_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_2209_, v___x_2299_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2300_);
if (lean_obj_tag(v_a_2301_) == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2302_;
}
else
{
lean_object* v_val_2303_; lean_object* v___x_2304_; 
v_val_2303_ = lean_ctor_get(v_a_2301_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v_a_2301_);
lean_inc_ref(v_F_2208_);
v___x_2304_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2303_, v_F_2208_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v_val_2306_; lean_object* v_toMatcherInfo_2307_; lean_object* v_matcherName_2308_; lean_object* v_matcherLevels_2309_; lean_object* v_params_2310_; lean_object* v_motive_2311_; lean_object* v_discrs_2312_; lean_object* v_alts_2313_; lean_object* v_remaining_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_val_2306_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_val_2306_);
lean_dec_ref(v_a_2305_);
v_toMatcherInfo_2307_ = lean_ctor_get(v_val_2306_, 0);
lean_inc_ref(v_toMatcherInfo_2307_);
v_matcherName_2308_ = lean_ctor_get(v_val_2306_, 1);
lean_inc(v_matcherName_2308_);
v_matcherLevels_2309_ = lean_ctor_get(v_val_2306_, 2);
lean_inc_ref(v_matcherLevels_2309_);
v_params_2310_ = lean_ctor_get(v_val_2306_, 3);
lean_inc_ref(v_params_2310_);
v_motive_2311_ = lean_ctor_get(v_val_2306_, 4);
lean_inc_ref(v_motive_2311_);
v_discrs_2312_ = lean_ctor_get(v_val_2306_, 5);
lean_inc_ref(v_discrs_2312_);
v_alts_2313_ = lean_ctor_get(v_val_2306_, 6);
lean_inc_ref(v_alts_2313_);
v_remaining_2314_ = lean_ctor_get(v_val_2306_, 7);
lean_inc_ref(v_remaining_2314_);
v___x_2315_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2306_);
v___x_2316_ = lean_unsigned_to_nat(0u);
v___x_2317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2207_);
lean_inc(v_recFnName_2206_);
v___x_2318_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_e_2209_, v_alts_2313_, v___x_2315_, v___x_2316_, v___x_2317_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec_ref(v___x_2315_);
lean_dec_ref(v_alts_2313_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; size_t v_sz_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v_sz_2320_ = lean_array_size(v_discrs_2312_);
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_sz_2320_, v___x_2321_, v_discrs_2312_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2332_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2327_, 0, v_toMatcherInfo_2307_);
lean_ctor_set(v___x_2327_, 1, v_matcherName_2308_);
lean_ctor_set(v___x_2327_, 2, v_matcherLevels_2309_);
lean_ctor_set(v___x_2327_, 3, v_params_2310_);
lean_ctor_set(v___x_2327_, 4, v_motive_2311_);
lean_ctor_set(v___x_2327_, 5, v_a_2323_);
lean_ctor_set(v___x_2327_, 6, v_a_2319_);
lean_ctor_set(v___x_2327_, 7, v_remaining_2314_);
v___x_2328_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_a_2319_);
lean_dec_ref(v_remaining_2314_);
lean_dec_ref(v_motive_2311_);
lean_dec_ref(v_params_2310_);
lean_dec_ref(v_matcherLevels_2309_);
lean_dec(v_matcherName_2308_);
lean_dec_ref(v_toMatcherInfo_2307_);
v_a_2333_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2322_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2322_);
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
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v_remaining_2314_);
lean_dec_ref(v_discrs_2312_);
lean_dec_ref(v_motive_2311_);
lean_dec_ref(v_params_2310_);
lean_dec_ref(v_matcherLevels_2309_);
lean_dec(v_matcherName_2308_);
lean_dec_ref(v_toMatcherInfo_2307_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
v_a_2341_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2318_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2318_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; 
lean_dec(v_a_2305_);
v___x_2349_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2206_, v_fixedPrefixSize_2207_, v_F_2208_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2349_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_e_2209_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
v_a_2350_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2304_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2304_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_e_2209_);
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
lean_dec(v_recFnName_2206_);
v_a_2358_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2300_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2300_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
default: 
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_F_2208_);
lean_dec(v_fixedPrefixSize_2207_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_mk_empty_array_with_capacity(v___x_2366_);
v___x_2368_ = lean_array_push(v___x_2367_, v_recFnName_2206_);
lean_inc_ref(v_e_2209_);
v___x_2369_ = l_Lean_Elab_ensureNoRecFn(v___x_2368_, v_e_2209_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2369_, 0);
lean_dec(v_unused_2377_);
v___x_2371_ = v___x_2369_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_dec(v___x_2369_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v_e_2209_);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_e_2209_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec_ref(v_e_2209_);
v_a_2378_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2369_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2369_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
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
uint8_t v___x_2386_; uint64_t v___x_2387_; 
v___x_2386_ = 0;
v___x_2387_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2388_, lean_object* v_fixedPrefixSize_2389_, lean_object* v_F_2390_, lean_object* v_e_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; 
lean_inc_ref(v_e_2391_);
lean_inc(v_recFnName_2388_);
v___x_2401_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2388_, v_e_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2540_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2540_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2540_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2408_; 
lean_dec_ref(v_F_2390_);
lean_dec(v_fixedPrefixSize_2389_);
lean_dec(v_recFnName_2388_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v_e_2391_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_e_2391_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
else
{
lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___x_2518_; 
lean_del_object(v___x_2404_);
v___x_2410_ = lean_st_ref_get(v_a_2393_);
v___x_2411_ = 0;
v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v___x_2410_, v_e_2391_);
lean_dec(v___x_2410_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___x_2522_; 
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v___x_2518_);
v_fst_2520_ = lean_ctor_get(v_val_2519_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v_val_2519_, 1);
lean_inc(v_snd_2521_);
lean_dec(v_val_2519_);
lean_inc_ref(v_a_2396_);
v___x_2522_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2521_, v_a_2396_);
lean_dec(v_snd_2521_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
if (v___x_2527_ == 0)
{
lean_del_object(v___x_2525_);
lean_dec(v_fst_2520_);
v___y_2413_ = v_a_2392_;
v___y_2414_ = v_a_2393_;
v___y_2415_ = v_a_2394_;
v___y_2416_ = v_a_2395_;
v___y_2417_ = v_a_2396_;
v___y_2418_ = v_a_2397_;
v___y_2419_ = v_a_2398_;
v___y_2420_ = v_a_2399_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2529_; 
lean_dec_ref(v_e_2391_);
lean_dec_ref(v_F_2390_);
lean_dec(v_fixedPrefixSize_2389_);
lean_dec(v_recFnName_2388_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_fst_2520_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_fst_2520_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_fst_2520_);
lean_dec_ref(v_e_2391_);
lean_dec_ref(v_F_2390_);
lean_dec(v_fixedPrefixSize_2389_);
lean_dec(v_recFnName_2388_);
v_a_2532_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2522_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2522_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_dec(v___x_2518_);
v___y_2413_ = v_a_2392_;
v___y_2414_ = v_a_2393_;
v___y_2415_ = v_a_2394_;
v___y_2416_ = v_a_2395_;
v___y_2417_ = v_a_2396_;
v___y_2418_ = v_a_2397_;
v___y_2419_ = v_a_2398_;
v___y_2420_ = v_a_2399_;
goto v___jp_2412_;
}
v___jp_2412_:
{
lean_object* v___x_2421_; 
lean_inc_ref(v_e_2391_);
v___x_2421_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2388_, v_fixedPrefixSize_2389_, v_F_2390_, v_e_2391_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
lean_inc_ref(v___y_2417_);
v___x_2423_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2509_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2509_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2509_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_options_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2428_ = lean_st_ref_take(v___y_2414_);
lean_inc(v_a_2422_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2422_);
lean_ctor_set(v___x_2429_, 1, v_a_2424_);
lean_inc_ref(v_e_2391_);
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v___x_2428_, v_e_2391_, v___x_2429_);
v___x_2431_ = lean_st_ref_set(v___y_2414_, v___x_2430_);
v_options_2432_ = lean_ctor_get(v___y_2419_, 2);
v___x_2433_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2434_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_options_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref(v_e_2391_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v_a_2422_);
v___x_2436_ = v___x_2426_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2422_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
else
{
lean_object* v___x_2438_; uint8_t v_foApprox_2439_; uint8_t v_ctxApprox_2440_; uint8_t v_quasiPatternApprox_2441_; uint8_t v_constApprox_2442_; uint8_t v_isDefEqStuckEx_2443_; uint8_t v_unificationHints_2444_; uint8_t v_proofIrrelevance_2445_; uint8_t v_assignSyntheticOpaque_2446_; uint8_t v_offsetCnstrs_2447_; uint8_t v_etaStruct_2448_; uint8_t v_univApprox_2449_; uint8_t v_iota_2450_; uint8_t v_beta_2451_; uint8_t v_proj_2452_; uint8_t v_zeta_2453_; uint8_t v_zetaDelta_2454_; uint8_t v_zetaUnused_2455_; uint8_t v_zetaHave_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2508_; 
lean_del_object(v___x_2426_);
v___x_2438_ = l_Lean_Meta_Context_config(v___y_2417_);
v_foApprox_2439_ = lean_ctor_get_uint8(v___x_2438_, 0);
v_ctxApprox_2440_ = lean_ctor_get_uint8(v___x_2438_, 1);
v_quasiPatternApprox_2441_ = lean_ctor_get_uint8(v___x_2438_, 2);
v_constApprox_2442_ = lean_ctor_get_uint8(v___x_2438_, 3);
v_isDefEqStuckEx_2443_ = lean_ctor_get_uint8(v___x_2438_, 4);
v_unificationHints_2444_ = lean_ctor_get_uint8(v___x_2438_, 5);
v_proofIrrelevance_2445_ = lean_ctor_get_uint8(v___x_2438_, 6);
v_assignSyntheticOpaque_2446_ = lean_ctor_get_uint8(v___x_2438_, 7);
v_offsetCnstrs_2447_ = lean_ctor_get_uint8(v___x_2438_, 8);
v_etaStruct_2448_ = lean_ctor_get_uint8(v___x_2438_, 10);
v_univApprox_2449_ = lean_ctor_get_uint8(v___x_2438_, 11);
v_iota_2450_ = lean_ctor_get_uint8(v___x_2438_, 12);
v_beta_2451_ = lean_ctor_get_uint8(v___x_2438_, 13);
v_proj_2452_ = lean_ctor_get_uint8(v___x_2438_, 14);
v_zeta_2453_ = lean_ctor_get_uint8(v___x_2438_, 15);
v_zetaDelta_2454_ = lean_ctor_get_uint8(v___x_2438_, 16);
v_zetaUnused_2455_ = lean_ctor_get_uint8(v___x_2438_, 17);
v_zetaHave_2456_ = lean_ctor_get_uint8(v___x_2438_, 18);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2458_ = v___x_2438_;
v_isShared_2459_ = v_isSharedCheck_2508_;
goto v_resetjp_2457_;
}
else
{
lean_dec(v___x_2438_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2508_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
uint8_t v_trackZetaDelta_2460_; lean_object* v_zetaDeltaSet_2461_; lean_object* v_lctx_2462_; lean_object* v_localInstances_2463_; lean_object* v_defEqCtx_x3f_2464_; lean_object* v_synthPendingDepth_2465_; lean_object* v_canUnfold_x3f_2466_; uint8_t v_univApprox_2467_; uint8_t v_inTypeClassResolution_2468_; uint8_t v_cacheInferType_2469_; uint8_t v___x_2470_; lean_object* v_config_2472_; 
v_trackZetaDelta_2460_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*7);
v_zetaDeltaSet_2461_ = lean_ctor_get(v___y_2417_, 1);
v_lctx_2462_ = lean_ctor_get(v___y_2417_, 2);
v_localInstances_2463_ = lean_ctor_get(v___y_2417_, 3);
v_defEqCtx_x3f_2464_ = lean_ctor_get(v___y_2417_, 4);
v_synthPendingDepth_2465_ = lean_ctor_get(v___y_2417_, 5);
v_canUnfold_x3f_2466_ = lean_ctor_get(v___y_2417_, 6);
v_univApprox_2467_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2468_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*7 + 2);
v_cacheInferType_2469_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*7 + 3);
v___x_2470_ = 0;
if (v_isShared_2459_ == 0)
{
v_config_2472_ = v___x_2458_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 0, v_foApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 1, v_ctxApprox_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 2, v_quasiPatternApprox_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 3, v_constApprox_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 4, v_isDefEqStuckEx_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 5, v_unificationHints_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 6, v_proofIrrelevance_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 7, v_assignSyntheticOpaque_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 8, v_offsetCnstrs_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 10, v_etaStruct_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 11, v_univApprox_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 12, v_iota_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 13, v_beta_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 14, v_proj_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 15, v_zeta_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 16, v_zetaDelta_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 17, v_zetaUnused_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 18, v_zetaHave_2456_);
v_config_2472_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
uint64_t v___x_2473_; uint64_t v___x_2474_; uint64_t v___x_2475_; lean_object* v___f_2476_; uint64_t v___x_2477_; uint64_t v___x_2478_; uint64_t v_key_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_ctor_set_uint8(v_config_2472_, 9, v___x_2470_);
v___x_2473_ = l_Lean_Meta_Context_configKey(v___y_2417_);
v___x_2474_ = 2ULL;
v___x_2475_ = lean_uint64_shift_right(v___x_2473_, v___x_2474_);
lean_inc(v_a_2422_);
v___f_2476_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2476_, 0, v_a_2422_);
lean_closure_set(v___f_2476_, 1, v_e_2391_);
v___x_2477_ = lean_uint64_shift_left(v___x_2475_, v___x_2474_);
v___x_2478_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___closed__0);
v_key_2479_ = lean_uint64_lor(v___x_2477_, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2480_, 0, v_config_2472_);
lean_ctor_set_uint64(v___x_2480_, sizeof(void*)*1, v_key_2479_);
lean_inc(v_canUnfold_x3f_2466_);
lean_inc(v_synthPendingDepth_2465_);
lean_inc(v_defEqCtx_x3f_2464_);
lean_inc_ref(v_localInstances_2463_);
lean_inc_ref(v_lctx_2462_);
lean_inc(v_zetaDeltaSet_2461_);
v___x_2481_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_zetaDeltaSet_2461_);
lean_ctor_set(v___x_2481_, 2, v_lctx_2462_);
lean_ctor_set(v___x_2481_, 3, v_localInstances_2463_);
lean_ctor_set(v___x_2481_, 4, v_defEqCtx_x3f_2464_);
lean_ctor_set(v___x_2481_, 5, v_synthPendingDepth_2465_);
lean_ctor_set(v___x_2481_, 6, v_canUnfold_x3f_2466_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7, v_trackZetaDelta_2460_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 1, v_univApprox_2467_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2468_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 3, v_cacheInferType_2469_);
v___x_2482_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___f_2476_, v___x_2411_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___x_2481_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec_ref(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2490_);
v___x_2484_ = v___x_2482_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_dec(v___x_2482_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v_a_2422_);
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2422_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2498_);
v___x_2492_ = v___x_2482_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v___x_2482_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2422_);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2422_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_a_2422_);
v_a_2499_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2482_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2482_);
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
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_a_2422_);
lean_dec_ref(v_e_2391_);
v_a_2510_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2423_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2423_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_dec_ref(v_e_2391_);
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_e_2391_);
lean_dec_ref(v_F_2390_);
lean_dec(v_fixedPrefixSize_2389_);
lean_dec(v_recFnName_2388_);
v_a_2541_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2401_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2401_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2549_, lean_object* v_recFnName_2550_, lean_object* v_fixedPrefixSize_2551_, lean_object* v_F_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_expr_instantiate1(v_body_2549_, v_x_2553_);
v___x_2564_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2550_, v_fixedPrefixSize_2551_, v_F_2552_, v___x_2563_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2565_, lean_object* v_fixedPrefixSize_2566_, lean_object* v_F_2567_, lean_object* v_e_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2565_, v_fixedPrefixSize_2566_, v_F_2567_, v_e_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2579_, lean_object* v_fixedPrefixSize_2580_, lean_object* v_F_2581_, lean_object* v_sz_2582_, lean_object* v_i_2583_, lean_object* v_bs_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
size_t v_sz_boxed_2594_; size_t v_i_boxed_2595_; lean_object* v_res_2596_; 
v_sz_boxed_2594_ = lean_unbox_usize(v_sz_2582_);
lean_dec(v_sz_2582_);
v_i_boxed_2595_ = lean_unbox_usize(v_i_2583_);
lean_dec(v_i_2583_);
v_res_2596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2579_, v_fixedPrefixSize_2580_, v_F_2581_, v_sz_boxed_2594_, v_i_boxed_2595_, v_bs_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17___boxed(lean_object* v_recFnName_2597_, lean_object* v_fixedPrefixSize_2598_, lean_object* v_F_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2597_, v_fixedPrefixSize_2598_, v_F_2599_, v_x_2600_, v_x_2601_, v_x_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec(v___y_2603_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___boxed(lean_object* v_recFnName_2613_, lean_object* v_fixedPrefixSize_2614_, lean_object* v_e_2615_, lean_object* v_as_2616_, lean_object* v_bs_2617_, lean_object* v_i_2618_, lean_object* v_cs_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2613_, v_fixedPrefixSize_2614_, v_e_2615_, v_as_2616_, v_bs_2617_, v_i_2618_, v_cs_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_bs_2617_);
lean_dec_ref(v_as_2616_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2630_, lean_object* v_fixedPrefixSize_2631_, lean_object* v_F_2632_, lean_object* v_e_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2630_, v_fixedPrefixSize_2631_, v_F_2632_, v_e_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec(v_a_2634_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2644_, lean_object* v_fixedPrefixSize_2645_, lean_object* v_F_2646_, lean_object* v_e_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2644_, v_fixedPrefixSize_2645_, v_F_2646_, v_e_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2658_, lean_object* v_fixedPrefixSize_2659_, lean_object* v_F_2660_, lean_object* v_e_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2658_, v_fixedPrefixSize_2659_, v_F_2660_, v_e_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec(v_a_2662_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b1_2672_, lean_object* v_k_2673_, uint8_t v_allowLevelAssignments_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_k_2673_, v_allowLevelAssignments_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b1_2685_, lean_object* v_k_2686_, lean_object* v_allowLevelAssignments_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2697_; lean_object* v_res_2698_; 
v_allowLevelAssignments_boxed_2697_ = lean_unbox(v_allowLevelAssignments_2687_);
v_res_2698_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b1_2685_, v_k_2686_, v_allowLevelAssignments_boxed_2697_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_00_u03b1_2699_, lean_object* v_name_2700_, uint8_t v_bi_2701_, lean_object* v_type_2702_, lean_object* v_k_2703_, uint8_t v_kind_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_name_2700_, v_bi_2701_, v_type_2702_, v_k_2703_, v_kind_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_name_2716_, lean_object* v_bi_2717_, lean_object* v_type_2718_, lean_object* v_k_2719_, lean_object* v_kind_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v_bi_boxed_2730_; uint8_t v_kind_boxed_2731_; lean_object* v_res_2732_; 
v_bi_boxed_2730_ = lean_unbox(v_bi_2717_);
v_kind_boxed_2731_ = lean_unbox(v_kind_2720_);
v_res_2732_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_00_u03b1_2715_, v_name_2716_, v_bi_boxed_2730_, v_type_2718_, v_k_2719_, v_kind_boxed_2731_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_00_u03b1_2733_, lean_object* v_e_2734_, lean_object* v_maxFVars_2735_, lean_object* v_k_2736_, uint8_t v_cleanupAnnotations_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_2734_, v_maxFVars_2735_, v_k_2736_, v_cleanupAnnotations_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_e_2749_, lean_object* v_maxFVars_2750_, lean_object* v_k_2751_, lean_object* v_cleanupAnnotations_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2762_; lean_object* v_res_2763_; 
v_cleanupAnnotations_boxed_2762_ = lean_unbox(v_cleanupAnnotations_2752_);
v_res_2763_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_00_u03b1_2748_, v_e_2749_, v_maxFVars_2750_, v_k_2751_, v_cleanupAnnotations_boxed_2762_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec(v___y_2753_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2764_, lean_object* v_R_2765_, lean_object* v_a_2766_, lean_object* v_b_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2766_, v_b_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3(lean_object* v_cls_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg(v_cls_2769_, v_msg_2770_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___boxed(lean_object* v_cls_2781_, lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3(v_cls_2781_, v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_00_u03b2_2793_, lean_object* v_m_2794_, lean_object* v_a_2795_, lean_object* v_b_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v_m_2794_, v_a_2795_, v_b_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_msg_2799_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2810_, v_msg_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(lean_object* v_00_u03b2_2822_, lean_object* v_m_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_2823_, v_a_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b2_2826_, lean_object* v_m_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(v_00_u03b2_2826_, v_m_2827_, v_a_2828_);
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_m_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16(lean_object* v_00_u03b1_2830_, lean_object* v_name_2831_, lean_object* v_type_2832_, lean_object* v_val_2833_, lean_object* v_k_2834_, uint8_t v_nondep_2835_, uint8_t v_kind_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___redArg(v_name_2831_, v_type_2832_, v_val_2833_, v_k_2834_, v_nondep_2835_, v_kind_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2847_, lean_object* v_name_2848_, lean_object* v_type_2849_, lean_object* v_val_2850_, lean_object* v_k_2851_, lean_object* v_nondep_2852_, lean_object* v_kind_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v_nondep_boxed_2863_; uint8_t v_kind_boxed_2864_; lean_object* v_res_2865_; 
v_nondep_boxed_2863_ = lean_unbox(v_nondep_2852_);
v_kind_boxed_2864_ = lean_unbox(v_kind_2853_);
v_res_2865_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__16(v_00_u03b1_2847_, v_name_2848_, v_type_2849_, v_val_2850_, v_k_2851_, v_nondep_boxed_2863_, v_kind_boxed_2864_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec(v___y_2854_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(lean_object* v_declName_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___redArg(v_declName_2866_, v___y_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___boxed(lean_object* v_declName_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(v_declName_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v___y_2878_);
return v_res_2887_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5(lean_object* v_00_u03b2_2888_, lean_object* v_a_2889_, lean_object* v_x_2890_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___redArg(v_a_2889_, v_x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5___boxed(lean_object* v_00_u03b2_2892_, lean_object* v_a_2893_, lean_object* v_x_2894_){
_start:
{
uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_res_2895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__5(v_00_u03b2_2892_, v_a_2893_, v_x_2894_);
lean_dec(v_x_2894_);
lean_dec_ref(v_a_2893_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6(lean_object* v_00_u03b2_2897_, lean_object* v_data_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6___redArg(v_data_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7(lean_object* v_00_u03b2_2900_, lean_object* v_a_2901_, lean_object* v_b_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__7___redArg(v_a_2901_, v_b_2902_, v_x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12(lean_object* v_00_u03b2_2905_, lean_object* v_a_2906_, lean_object* v_x_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___redArg(v_a_2906_, v_x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2909_, lean_object* v_a_2910_, lean_object* v_x_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__12(v_00_u03b2_2909_, v_a_2910_, v_x_2911_);
lean_dec(v_x_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13(lean_object* v_00_u03b2_2913_, lean_object* v_i_2914_, lean_object* v_source_2915_, lean_object* v_target_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13___redArg(v_i_2914_, v_source_2915_, v_target_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22(lean_object* v_00_u03b1_2918_, lean_object* v_constName_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___redArg(v_constName_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_constName_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22(v_00_u03b1_2930_, v_constName_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23(lean_object* v_00_u03b2_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5_spec__6_spec__13_spec__23___redArg(v_x_2943_, v_x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28(lean_object* v_00_u03b1_2946_, lean_object* v_ref_2947_, lean_object* v_constName_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___redArg(v_ref_2947_, v_constName_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_ref_2960_, lean_object* v_constName_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28(v_00_u03b1_2959_, v_ref_2960_, v_constName_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v_ref_2960_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30(lean_object* v_00_u03b1_2972_, lean_object* v_ref_2973_, lean_object* v_msg_2974_, lean_object* v_declHint_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___redArg(v_ref_2973_, v_msg_2974_, v_declHint_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30___boxed(lean_object* v_00_u03b1_2986_, lean_object* v_ref_2987_, lean_object* v_msg_2988_, lean_object* v_declHint_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30(v_00_u03b1_2986_, v_ref_2987_, v_msg_2988_, v_declHint_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec(v_ref_2987_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32(lean_object* v_msg_3000_, lean_object* v_declHint_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___redArg(v_msg_3000_, v_declHint_3001_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32___boxed(lean_object* v_msg_3012_, lean_object* v_declHint_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__31_spec__32(v_msg_3012_, v_declHint_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32(lean_object* v_00_u03b1_3024_, lean_object* v_ref_3025_, lean_object* v_msg_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___redArg(v_ref_3025_, v_msg_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_ref_3038_, lean_object* v_msg_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19_spec__22_spec__28_spec__30_spec__32(v_00_u03b1_3037_, v_ref_3038_, v_msg_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec(v_ref_3038_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_options_3053_; uint8_t v_hasTrace_3054_; 
v_options_3053_ = lean_ctor_get(v___y_3051_, 2);
v_hasTrace_3054_ = lean_ctor_get_uint8(v_options_3053_, sizeof(void*)*1);
if (v_hasTrace_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec(v_cls_3050_);
v___x_3055_ = lean_box(v_hasTrace_3054_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
else
{
lean_object* v_inheritedTraceOptions_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_inheritedTraceOptions_3057_ = lean_ctor_get(v___y_3051_, 13);
v___x_3058_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3059_ = l_Lean_Name_append(v___x_3058_, v_cls_3050_);
v___x_3060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3057_, v_options_3053_, v___x_3059_);
lean_dec(v___x_3059_);
v___x_3061_ = lean_box(v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3063_, v___y_3064_);
lean_dec_ref(v___y_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3067_, v___y_3072_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(lean_object* v_cls_3085_, lean_object* v_msg_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_ref_3092_; lean_object* v___x_3093_; lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3138_; 
v_ref_3092_ = lean_ctor_get(v___y_3089_, 5);
v___x_3093_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3138_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3138_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v_traceState_3099_; lean_object* v_env_3100_; lean_object* v_nextMacroScope_3101_; lean_object* v_ngen_3102_; lean_object* v_auxDeclNGen_3103_; lean_object* v_cache_3104_; lean_object* v_messages_3105_; lean_object* v_infoState_3106_; lean_object* v_snapshotTasks_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3137_; 
v___x_3098_ = lean_st_ref_take(v___y_3090_);
v_traceState_3099_ = lean_ctor_get(v___x_3098_, 4);
v_env_3100_ = lean_ctor_get(v___x_3098_, 0);
v_nextMacroScope_3101_ = lean_ctor_get(v___x_3098_, 1);
v_ngen_3102_ = lean_ctor_get(v___x_3098_, 2);
v_auxDeclNGen_3103_ = lean_ctor_get(v___x_3098_, 3);
v_cache_3104_ = lean_ctor_get(v___x_3098_, 5);
v_messages_3105_ = lean_ctor_get(v___x_3098_, 6);
v_infoState_3106_ = lean_ctor_get(v___x_3098_, 7);
v_snapshotTasks_3107_ = lean_ctor_get(v___x_3098_, 8);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3109_ = v___x_3098_;
v_isShared_3110_ = v_isSharedCheck_3137_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snapshotTasks_3107_);
lean_inc(v_infoState_3106_);
lean_inc(v_messages_3105_);
lean_inc(v_cache_3104_);
lean_inc(v_traceState_3099_);
lean_inc(v_auxDeclNGen_3103_);
lean_inc(v_ngen_3102_);
lean_inc(v_nextMacroScope_3101_);
lean_inc(v_env_3100_);
lean_dec(v___x_3098_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3137_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
uint64_t v_tid_3111_; lean_object* v_traces_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3136_; 
v_tid_3111_ = lean_ctor_get_uint64(v_traceState_3099_, sizeof(void*)*1);
v_traces_3112_ = lean_ctor_get(v_traceState_3099_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_traceState_3099_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3114_ = v_traceState_3099_;
v_isShared_3115_ = v_isSharedCheck_3136_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_traces_3112_);
lean_dec(v_traceState_3099_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3136_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; double v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__0);
v___x_3118_ = 0;
v___x_3119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__1));
v___x_3120_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3120_, 0, v_cls_3085_);
lean_ctor_set(v___x_3120_, 1, v___x_3116_);
lean_ctor_set(v___x_3120_, 2, v___x_3119_);
lean_ctor_set_float(v___x_3120_, sizeof(void*)*3, v___x_3117_);
lean_ctor_set_float(v___x_3120_, sizeof(void*)*3 + 8, v___x_3117_);
lean_ctor_set_uint8(v___x_3120_, sizeof(void*)*3 + 16, v___x_3118_);
v___x_3121_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__3___redArg___closed__2));
v___x_3122_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3120_);
lean_ctor_set(v___x_3122_, 1, v_a_3094_);
lean_ctor_set(v___x_3122_, 2, v___x_3121_);
lean_inc(v_ref_3092_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_ref_3092_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_PersistentArray_push___redArg(v_traces_3112_, v___x_3123_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3124_);
v___x_3126_ = v___x_3114_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3124_);
lean_ctor_set_uint64(v_reuseFailAlloc_3135_, sizeof(void*)*1, v_tid_3111_);
v___x_3126_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 4, v___x_3126_);
v___x_3128_ = v___x_3109_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_env_3100_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_nextMacroScope_3101_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_ngen_3102_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_auxDeclNGen_3103_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3134_, 5, v_cache_3104_);
lean_ctor_set(v_reuseFailAlloc_3134_, 6, v_messages_3105_);
lean_ctor_set(v_reuseFailAlloc_3134_, 7, v_infoState_3106_);
lean_ctor_set(v_reuseFailAlloc_3134_, 8, v_snapshotTasks_3107_);
v___x_3128_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3129_ = lean_st_ref_set(v___y_3090_, v___x_3128_);
v___x_3130_ = lean_box(0);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3130_);
v___x_3132_ = v___x_3096_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg___boxed(lean_object* v_cls_3139_, lean_object* v_msg_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3139_, v_msg_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
return v_res_3146_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_unsigned_to_nat(16u);
v___x_3149_ = lean_mk_array(v___x_3148_, v___x_3147_);
return v___x_3149_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v___x_3150_);
return v___x_3152_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
return v___x_3155_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3158_ = l_Lean_stringToMessageData(v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3161_ = l_Lean_stringToMessageData(v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3162_, lean_object* v_fixedPrefixSize_3163_, lean_object* v_F_3164_, lean_object* v_e_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v_cls_3194_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___x_3223_; lean_object* v_a_3224_; uint8_t v___x_3225_; 
v_cls_3194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3223_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3194_, v_a_3170_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = lean_unbox(v_a_3224_);
lean_dec(v_a_3224_);
if (v___x_3225_ == 0)
{
v___y_3196_ = v_a_3166_;
v___y_3197_ = v_a_3167_;
v___y_3198_ = v_a_3168_;
v___y_3199_ = v_a_3169_;
v___y_3200_ = v_a_3170_;
v___y_3201_ = v_a_3171_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3226_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3165_);
v___x_3227_ = l_Lean_indentExpr(v_e_3165_);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3226_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3194_, v___x_3228_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_dec_ref(v___x_3229_);
v___y_3196_ = v_a_3166_;
v___y_3197_ = v_a_3167_;
v___y_3198_ = v_a_3168_;
v___y_3199_ = v_a_3169_;
v___y_3200_ = v_a_3170_;
v___y_3201_ = v_a_3171_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_e_3165_);
lean_dec_ref(v_F_3164_);
lean_dec(v_fixedPrefixSize_3163_);
lean_dec(v_recFnName_3162_);
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
v___jp_3173_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3180_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3181_ = lean_st_mk_ref(v___x_3180_);
v___x_3182_ = lean_st_mk_ref(v___x_3180_);
v___x_3183_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3162_, v_fixedPrefixSize_3163_, v_F_3164_, v_e_3165_, v___x_3182_, v___x_3181_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3193_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3193_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3188_ = lean_st_ref_get(v___x_3182_);
lean_dec(v___x_3182_);
lean_dec(v___x_3188_);
v___x_3189_ = lean_st_ref_get(v___x_3181_);
lean_dec(v___x_3181_);
lean_dec(v___x_3189_);
if (v_isShared_3187_ == 0)
{
v___x_3191_ = v___x_3186_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3184_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
else
{
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
return v___x_3183_;
}
}
v___jp_3195_:
{
lean_object* v___x_3202_; lean_object* v_a_3203_; uint8_t v___x_3204_; 
v___x_3202_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3194_, v___y_3200_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref(v___x_3202_);
v___x_3204_ = lean_unbox(v_a_3203_);
lean_dec(v_a_3203_);
if (v___x_3204_ == 0)
{
v___y_3174_ = v___y_3196_;
v___y_3175_ = v___y_3197_;
v___y_3176_ = v___y_3198_;
v___y_3177_ = v___y_3199_;
v___y_3178_ = v___y_3200_;
v___y_3179_ = v___y_3201_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3205_; 
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3200_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc_ref(v_F_3164_);
v___x_3205_ = lean_infer_type(v_F_3164_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3164_);
v___x_3208_ = l_Lean_MessageData_ofExpr(v_F_3164_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_indentExpr(v_a_3206_);
v___x_3213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3194_, v___x_3213_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_dec_ref(v___x_3214_);
v___y_3174_ = v___y_3196_;
v___y_3175_ = v___y_3197_;
v___y_3176_ = v___y_3198_;
v___y_3177_ = v___y_3199_;
v___y_3178_ = v___y_3200_;
v___y_3179_ = v___y_3201_;
goto v___jp_3173_;
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_e_3165_);
lean_dec_ref(v_F_3164_);
lean_dec(v_fixedPrefixSize_3163_);
lean_dec(v_recFnName_3162_);
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_dec_ref(v_e_3165_);
lean_dec_ref(v_F_3164_);
lean_dec(v_fixedPrefixSize_3163_);
lean_dec(v_recFnName_3162_);
return v___x_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3238_, lean_object* v_fixedPrefixSize_3239_, lean_object* v_F_3240_, lean_object* v_e_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3238_, v_fixedPrefixSize_3239_, v_F_3240_, v_e_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1(lean_object* v_cls_3250_, lean_object* v_msg_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___redArg(v_cls_3250_, v_msg_3251_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1___boxed(lean_object* v_cls_3260_, lean_object* v_msg_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__1(v_cls_3260_, v_msg_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v_b_3273_, lean_object* v_c_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; 
lean_inc(v___y_3278_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
v___x_3280_ = lean_apply_9(v_k_3270_, v_b_3273_, v_c_3274_, v___y_3271_, v___y_3272_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, lean_box(0));
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v_b_3284_, lean_object* v_c_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3281_, v___y_3282_, v___y_3283_, v_b_3284_, v_c_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3292_, lean_object* v_maxFVars_3293_, lean_object* v_k_3294_, uint8_t v_cleanupAnnotations_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___f_3303_; uint8_t v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
v___f_3303_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3303_, 0, v_k_3294_);
lean_closure_set(v___f_3303_, 1, v___y_3296_);
lean_closure_set(v___f_3303_, 2, v___y_3297_);
v___x_3304_ = 1;
v___x_3305_ = 0;
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_maxFVars_3293_);
v___x_3307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3292_, v___x_3304_, v___x_3305_, v___x_3304_, v___x_3305_, v___x_3306_, v___f_3303_, v_cleanupAnnotations_3295_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
return v___x_3307_;
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3316_, lean_object* v_maxFVars_3317_, lean_object* v_k_3318_, lean_object* v_cleanupAnnotations_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3327_; lean_object* v_res_3328_; 
v_cleanupAnnotations_boxed_3327_ = lean_unbox(v_cleanupAnnotations_3319_);
v_res_3328_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3316_, v_maxFVars_3317_, v_k_3318_, v_cleanupAnnotations_boxed_3327_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3329_, lean_object* v_e_3330_, lean_object* v_maxFVars_3331_, lean_object* v_k_3332_, uint8_t v_cleanupAnnotations_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3330_, v_maxFVars_3331_, v_k_3332_, v_cleanupAnnotations_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_e_3343_, lean_object* v_maxFVars_3344_, lean_object* v_k_3345_, lean_object* v_cleanupAnnotations_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3354_; lean_object* v_res_3355_; 
v_cleanupAnnotations_boxed_3354_ = lean_unbox(v_cleanupAnnotations_3346_);
v_res_3355_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3342_, v_e_3343_, v_maxFVars_3344_, v_k_3345_, v_cleanupAnnotations_boxed_3354_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3356_, lean_object* v_k_3357_, uint8_t v_cleanupAnnotations_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___f_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3366_, 0, v_k_3357_);
lean_closure_set(v___f_3366_, 1, v___y_3359_);
lean_closure_set(v___f_3366_, 2, v___y_3360_);
v___x_3367_ = 1;
v___x_3368_ = 0;
v___x_3369_ = lean_box(0);
v___x_3370_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3356_, v___x_3367_, v___x_3368_, v___x_3367_, v___x_3368_, v___x_3369_, v___f_3366_, v_cleanupAnnotations_3358_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3370_) == 0)
{
return v___x_3370_;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3379_, lean_object* v_k_3380_, lean_object* v_cleanupAnnotations_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3389_; lean_object* v_res_3390_; 
v_cleanupAnnotations_boxed_3389_ = lean_unbox(v_cleanupAnnotations_3381_);
v_res_3390_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3379_, v_k_3380_, v_cleanupAnnotations_boxed_3389_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3391_, lean_object* v_e_3392_, lean_object* v_k_3393_, uint8_t v_cleanupAnnotations_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3392_, v_k_3393_, v_cleanupAnnotations_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_e_3404_, lean_object* v_k_3405_, lean_object* v_cleanupAnnotations_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3414_; lean_object* v_res_3415_; 
v_cleanupAnnotations_boxed_3414_ = lean_unbox(v_cleanupAnnotations_3406_);
v_res_3415_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3403_, v_e_3404_, v_k_3405_, v_cleanupAnnotations_boxed_3414_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3416_, lean_object* v___x_3417_, lean_object* v___x_3418_, lean_object* v_x_3419_, uint8_t v___x_3420_, lean_object* v_xs_3421_, lean_object* v_type_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3430_ = l_Lean_LocalDecl_type(v_a_3416_);
v___x_3431_ = lean_array_get_borrowed(v___x_3417_, v_xs_3421_, v___x_3418_);
v___x_3432_ = l_Lean_Expr_replaceFVar(v___x_3430_, v_x_3419_, v___x_3431_);
lean_dec_ref(v___x_3430_);
v___x_3433_ = l_Lean_mkArrow(v___x_3432_, v_type_3422_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; uint8_t v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = 0;
v___x_3436_ = 1;
lean_inc(v_a_3434_);
v___x_3437_ = l_Lean_Meta_mkLambdaFVars(v_xs_3421_, v_a_3434_, v___x_3435_, v___x_3420_, v___x_3435_, v___x_3420_, v___x_3436_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l_Lean_Meta_getLevel(v_a_3434_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3448_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v_a_3438_);
lean_ctor_set(v___x_3444_, 1, v_a_3440_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_a_3438_);
v_a_3449_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3439_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3439_);
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
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_a_3434_);
v_a_3457_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3437_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3437_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
v_a_3465_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3433_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3433_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3473_, lean_object* v___x_3474_, lean_object* v___x_3475_, lean_object* v_x_3476_, lean_object* v___x_3477_, lean_object* v_xs_3478_, lean_object* v_type_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v___x_6703__boxed_3487_; lean_object* v_res_3488_; 
v___x_6703__boxed_3487_ = lean_unbox(v___x_3477_);
v_res_3488_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3473_, v___x_3474_, v___x_3475_, v_x_3476_, v___x_6703__boxed_3487_, v_xs_3478_, v_type_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v_xs_3478_);
lean_dec(v___x_3475_);
lean_dec_ref(v_a_3473_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
lean_inc(v___y_3496_);
lean_inc_ref(v___y_3495_);
lean_inc(v___y_3494_);
lean_inc_ref(v___y_3493_);
lean_inc(v___y_3491_);
lean_inc_ref(v___y_3490_);
v___x_3498_ = lean_apply_8(v_k_3489_, v_b_3492_, v___y_3490_, v___y_3491_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, lean_box(0));
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3499_, v___y_3500_, v___y_3501_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3509_, uint8_t v_bi_3510_, lean_object* v_type_3511_, lean_object* v_k_3512_, uint8_t v_kind_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___f_3521_; lean_object* v___x_3522_; 
lean_inc(v___y_3515_);
lean_inc_ref(v___y_3514_);
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3521_, 0, v_k_3512_);
lean_closure_set(v___f_3521_, 1, v___y_3514_);
lean_closure_set(v___f_3521_, 2, v___y_3515_);
v___x_3522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3509_, v_bi_3510_, v_type_3511_, v___f_3521_, v_kind_3513_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
if (lean_obj_tag(v___x_3522_) == 0)
{
return v___x_3522_;
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3531_, lean_object* v_bi_3532_, lean_object* v_type_3533_, lean_object* v_k_3534_, lean_object* v_kind_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
uint8_t v_bi_boxed_3543_; uint8_t v_kind_boxed_3544_; lean_object* v_res_3545_; 
v_bi_boxed_3543_ = lean_unbox(v_bi_3532_);
v_kind_boxed_3544_ = lean_unbox(v_kind_3535_);
v_res_3545_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3531_, v_bi_boxed_3543_, v_type_3533_, v_k_3534_, v_kind_boxed_3544_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3546_, lean_object* v_type_3547_, lean_object* v_k_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
uint8_t v___x_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = 0;
v___x_3557_ = 0;
v___x_3558_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3546_, v___x_3556_, v_type_3547_, v_k_3548_, v___x_3557_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3559_, lean_object* v_type_3560_, lean_object* v_k_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3559_, v_type_3560_, v_k_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3583_, lean_object* v_F_3584_, lean_object* v_val_3585_, lean_object* v_k_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
uint8_t v___y_3595_; uint8_t v___x_3710_; 
v___x_3710_ = l_Lean_Expr_isFVar(v_x_3583_);
if (v___x_3710_ == 0)
{
v___y_3595_ = v___x_3710_;
goto v___jp_3594_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3711_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3712_ = lean_unsigned_to_nat(6u);
v___x_3713_ = l_Lean_Expr_isAppOfArity(v_val_3585_, v___x_3711_, v___x_3712_);
v___y_3595_ = v___x_3713_;
goto v___jp_3594_;
}
v___jp_3594_:
{
if (v___y_3595_ == 0)
{
lean_object* v___x_3596_; 
lean_inc(v_a_3592_);
lean_inc_ref(v_a_3591_);
lean_inc(v_a_3590_);
lean_inc_ref(v_a_3589_);
lean_inc(v_a_3588_);
lean_inc_ref(v_a_3587_);
v___x_3596_ = lean_apply_10(v_k_3586_, v_x_3583_, v_F_3584_, v_val_3585_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, lean_box(0));
return v___x_3596_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; 
v___x_3597_ = lean_unsigned_to_nat(3u);
v___x_3598_ = l_Lean_Expr_getAppNumArgs(v_val_3585_);
v___x_3599_ = lean_nat_sub(v___x_3598_, v___x_3597_);
v___x_3600_ = lean_unsigned_to_nat(1u);
v___x_3601_ = lean_nat_sub(v___x_3599_, v___x_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = l_Lean_Expr_getRevArg_x21(v_val_3585_, v___x_3601_);
v___x_3603_ = lean_expr_eqv(v___x_3602_, v_x_3583_);
lean_dec_ref(v___x_3602_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; 
lean_dec(v___x_3598_);
lean_inc(v_a_3592_);
lean_inc_ref(v_a_3591_);
lean_inc(v_a_3590_);
lean_inc_ref(v_a_3589_);
lean_inc(v_a_3588_);
lean_inc_ref(v_a_3587_);
v___x_3604_ = lean_apply_10(v_k_3586_, v_x_3583_, v_F_3584_, v_val_3585_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, lean_box(0));
return v___x_3604_;
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3605_ = lean_unsigned_to_nat(4u);
v___x_3606_ = lean_nat_sub(v___x_3598_, v___x_3605_);
v___x_3607_ = lean_nat_sub(v___x_3606_, v___x_3600_);
lean_dec(v___x_3606_);
v___x_3608_ = l_Lean_Expr_getRevArg_x21(v_val_3585_, v___x_3607_);
v___x_3609_ = l_Lean_Expr_isLambda(v___x_3608_);
lean_dec_ref(v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v___x_3598_);
lean_inc(v_a_3592_);
lean_inc_ref(v_a_3591_);
lean_inc(v_a_3590_);
lean_inc_ref(v_a_3589_);
lean_inc(v_a_3588_);
lean_inc_ref(v_a_3587_);
v___x_3610_ = lean_apply_10(v_k_3586_, v_x_3583_, v_F_3584_, v_val_3585_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, lean_box(0));
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3611_ = lean_unsigned_to_nat(5u);
v___x_3612_ = lean_nat_sub(v___x_3598_, v___x_3611_);
v___x_3613_ = lean_nat_sub(v___x_3612_, v___x_3600_);
lean_dec(v___x_3612_);
v___x_3614_ = l_Lean_Expr_getRevArg_x21(v_val_3585_, v___x_3613_);
v___x_3615_ = l_Lean_Expr_isLambda(v___x_3614_);
lean_dec_ref(v___x_3614_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
lean_dec(v___x_3598_);
lean_inc(v_a_3592_);
lean_inc_ref(v_a_3591_);
lean_inc(v_a_3590_);
lean_inc_ref(v_a_3589_);
lean_inc(v_a_3588_);
lean_inc_ref(v_a_3587_);
v___x_3616_ = lean_apply_10(v_k_3586_, v_x_3583_, v_F_3584_, v_val_3585_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, lean_box(0));
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = l_Lean_Expr_fvarId_x21(v_F_3584_);
lean_inc_ref(v_a_3589_);
v___x_3618_ = l_Lean_FVarId_getDecl___redArg(v___x_3617_, v_a_3589_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_dummy_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v_args_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v_00_u03b1_3626_; lean_object* v___x_3627_; lean_object* v___f_3628_; lean_object* v_00_u03b2_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v___x_3618_);
v_dummy_3620_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_3598_);
v___x_3621_ = lean_mk_array(v___x_3598_, v_dummy_3620_);
v___x_3622_ = lean_nat_sub(v___x_3598_, v___x_3600_);
lean_dec(v___x_3598_);
v_args_3623_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3585_, v___x_3621_, v___x_3622_);
v___x_3624_ = l_Lean_instInhabitedExpr;
v___x_3625_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3626_ = lean_array_get(v___x_3624_, v_args_3623_, v___x_3625_);
v___x_3627_ = lean_box(v___x_3609_);
lean_inc_ref(v_x_3583_);
lean_inc(v_a_3619_);
v___f_3628_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3628_, 0, v_a_3619_);
lean_closure_set(v___f_3628_, 1, v___x_3624_);
lean_closure_set(v___f_3628_, 2, v___x_3625_);
lean_closure_set(v___f_3628_, 3, v_x_3583_);
lean_closure_set(v___f_3628_, 4, v___x_3627_);
v_00_u03b2_3629_ = lean_array_get(v___x_3624_, v_args_3623_, v___x_3600_);
v___x_3630_ = lean_unsigned_to_nat(2u);
v___x_3631_ = lean_array_get(v___x_3624_, v_args_3623_, v___x_3630_);
v___x_3632_ = 0;
v___x_3633_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3631_, v___f_3628_, v___x_3632_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_fst_3635_; lean_object* v_snd_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3693_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v_fst_3635_ = lean_ctor_get(v_a_3634_, 0);
v_snd_3636_ = lean_ctor_get(v_a_3634_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3638_ = v_a_3634_;
v_isShared_3639_ = v_isSharedCheck_3693_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_snd_3636_);
lean_inc(v_fst_3635_);
lean_dec(v_a_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3693_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3641_ = lean_array_get(v___x_3624_, v_args_3623_, v___x_3605_);
lean_inc_ref(v_x_3583_);
lean_inc(v_a_3619_);
lean_inc_ref(v_k_3586_);
lean_inc(v_00_u03b2_3629_);
lean_inc(v_00_u03b1_3626_);
v___x_3642_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3624_, v___x_3625_, v_00_u03b1_3626_, v_00_u03b2_3629_, v___x_3597_, v_k_3586_, v___x_3630_, v___x_3632_, v___x_3609_, v_a_3619_, v_x_3583_, v___x_3600_, v___x_3640_, v___x_3641_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3645_ = lean_array_get(v___x_3624_, v_args_3623_, v___x_3611_);
lean_dec_ref(v_args_3623_);
lean_inc_ref(v_x_3583_);
lean_inc(v_00_u03b2_3629_);
lean_inc(v_00_u03b1_3626_);
v___x_3646_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3624_, v___x_3625_, v_00_u03b1_3626_, v_00_u03b2_3629_, v___x_3597_, v_k_3586_, v___x_3630_, v___x_3632_, v___x_3609_, v_a_3619_, v_x_3583_, v___x_3600_, v___x_3644_, v___x_3645_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref(v___x_3646_);
lean_inc(v_00_u03b1_3626_);
v___x_3648_ = l_Lean_Meta_getLevel(v_00_u03b1_3626_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
lean_inc(v_00_u03b2_3629_);
v___x_3650_ = l_Lean_Meta_getLevel(v_00_u03b2_3629_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3676_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3676_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3676_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3656_ = lean_box(0);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3656_);
lean_ctor_set(v___x_3638_, 0, v_a_3651_);
v___x_3658_ = v___x_3638_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3651_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_a_3649_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3660_, 0, v_snd_3636_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_mkConst(v___x_3655_, v___x_3660_);
v___x_3662_ = lean_unsigned_to_nat(7u);
v___x_3663_ = lean_mk_empty_array_with_capacity(v___x_3662_);
v___x_3664_ = lean_array_push(v___x_3663_, v_00_u03b1_3626_);
v___x_3665_ = lean_array_push(v___x_3664_, v_00_u03b2_3629_);
v___x_3666_ = lean_array_push(v___x_3665_, v_fst_3635_);
v___x_3667_ = lean_array_push(v___x_3666_, v_x_3583_);
v___x_3668_ = lean_array_push(v___x_3667_, v_a_3643_);
v___x_3669_ = lean_array_push(v___x_3668_, v_a_3647_);
v___x_3670_ = lean_array_push(v___x_3669_, v_F_3584_);
v___x_3671_ = l_Lean_mkAppN(v___x_3661_, v___x_3670_);
lean_dec_ref(v___x_3670_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3671_);
v___x_3673_ = v___x_3653_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_a_3649_);
lean_dec(v_a_3647_);
lean_dec(v_a_3643_);
lean_del_object(v___x_3638_);
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
lean_dec(v_00_u03b2_3629_);
lean_dec(v_00_u03b1_3626_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
v_a_3677_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3650_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3650_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3647_);
lean_dec(v_a_3643_);
lean_del_object(v___x_3638_);
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
lean_dec(v_00_u03b2_3629_);
lean_dec(v_00_u03b1_3626_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
v_a_3685_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3648_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3648_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_dec(v_a_3643_);
lean_del_object(v___x_3638_);
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
lean_dec(v_00_u03b2_3629_);
lean_dec(v_00_u03b1_3626_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
return v___x_3646_;
}
}
else
{
lean_del_object(v___x_3638_);
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
lean_dec(v_00_u03b2_3629_);
lean_dec(v_00_u03b1_3626_);
lean_dec_ref(v_args_3623_);
lean_dec(v_a_3619_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
return v___x_3642_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v_00_u03b2_3629_);
lean_dec(v_00_u03b1_3626_);
lean_dec_ref(v_args_3623_);
lean_dec(v_a_3619_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
v_a_3694_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3633_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3633_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_dec(v___x_3598_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_val_3585_);
lean_dec_ref(v_F_3584_);
lean_dec_ref(v_x_3583_);
v_a_3702_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3618_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3618_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3714_, lean_object* v_body_3715_, lean_object* v_k_3716_, lean_object* v___x_3717_, uint8_t v___x_3718_, uint8_t v___x_3719_, lean_object* v_FNew_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
lean_inc_ref(v_FNew_3720_);
lean_inc_ref(v___x_3714_);
v___x_3728_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3714_, v_FNew_3720_, v_body_3715_, v_k_3716_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref(v___x_3728_);
v___x_3730_ = lean_mk_empty_array_with_capacity(v___x_3717_);
v___x_3731_ = lean_array_push(v___x_3730_, v___x_3714_);
v___x_3732_ = lean_array_push(v___x_3731_, v_FNew_3720_);
v___x_3733_ = 1;
v___x_3734_ = l_Lean_Meta_mkLambdaFVars(v___x_3732_, v_a_3729_, v___x_3718_, v___x_3719_, v___x_3718_, v___x_3719_, v___x_3733_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
lean_dec_ref(v___x_3732_);
return v___x_3734_;
}
else
{
lean_dec_ref(v_FNew_3720_);
lean_dec_ref(v___x_3714_);
return v___x_3728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3735_, lean_object* v_body_3736_, lean_object* v_k_3737_, lean_object* v___x_3738_, lean_object* v___x_3739_, lean_object* v___x_3740_, lean_object* v_FNew_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
uint8_t v___x_6949__boxed_3749_; uint8_t v___x_6950__boxed_3750_; lean_object* v_res_3751_; 
v___x_6949__boxed_3749_ = lean_unbox(v___x_3739_);
v___x_6950__boxed_3750_ = lean_unbox(v___x_3740_);
v_res_3751_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3735_, v_body_3736_, v_k_3737_, v___x_3738_, v___x_6949__boxed_3749_, v___x_6950__boxed_3750_, v_FNew_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___x_3738_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3752_, lean_object* v___x_3753_, lean_object* v_00_u03b1_3754_, lean_object* v_00_u03b2_3755_, lean_object* v___x_3756_, lean_object* v_ctorName_3757_, lean_object* v_k_3758_, lean_object* v___x_3759_, uint8_t v___x_3760_, uint8_t v___x_3761_, lean_object* v_a_3762_, lean_object* v_x_3763_, lean_object* v_xs_3764_, lean_object* v_body_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3773_ = lean_array_get_borrowed(v___x_3752_, v_xs_3764_, v___x_3753_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_00_u03b1_3754_);
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_00_u03b2_3755_);
lean_inc(v___x_3773_);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3773_);
v___x_3777_ = lean_mk_empty_array_with_capacity(v___x_3756_);
v___x_3778_ = lean_array_push(v___x_3777_, v___x_3774_);
v___x_3779_ = lean_array_push(v___x_3778_, v___x_3775_);
v___x_3780_ = lean_array_push(v___x_3779_, v___x_3776_);
v___x_3781_ = l_Lean_Meta_mkAppOptM(v_ctorName_3757_, v___x_3780_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = lean_box(v___x_3760_);
v___x_3784_ = lean_box(v___x_3761_);
lean_inc(v___x_3773_);
v___f_3785_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3785_, 0, v___x_3773_);
lean_closure_set(v___f_3785_, 1, v_body_3765_);
lean_closure_set(v___f_3785_, 2, v_k_3758_);
lean_closure_set(v___f_3785_, 3, v___x_3759_);
lean_closure_set(v___f_3785_, 4, v___x_3783_);
lean_closure_set(v___f_3785_, 5, v___x_3784_);
v___x_3786_ = l_Lean_LocalDecl_type(v_a_3762_);
v___x_3787_ = l_Lean_Expr_replaceFVar(v___x_3786_, v_x_3763_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l_Lean_LocalDecl_userName(v_a_3762_);
v___x_3789_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3788_, v___x_3787_, v___f_3785_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3789_;
}
else
{
lean_dec_ref(v_body_3765_);
lean_dec_ref(v_x_3763_);
lean_dec(v___x_3759_);
lean_dec_ref(v_k_3758_);
return v___x_3781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3790_ = _args[0];
lean_object* v___x_3791_ = _args[1];
lean_object* v_00_u03b1_3792_ = _args[2];
lean_object* v_00_u03b2_3793_ = _args[3];
lean_object* v___x_3794_ = _args[4];
lean_object* v_ctorName_3795_ = _args[5];
lean_object* v_k_3796_ = _args[6];
lean_object* v___x_3797_ = _args[7];
lean_object* v___x_3798_ = _args[8];
lean_object* v___x_3799_ = _args[9];
lean_object* v_a_3800_ = _args[10];
lean_object* v_x_3801_ = _args[11];
lean_object* v_xs_3802_ = _args[12];
lean_object* v_body_3803_ = _args[13];
lean_object* v___y_3804_ = _args[14];
lean_object* v___y_3805_ = _args[15];
lean_object* v___y_3806_ = _args[16];
lean_object* v___y_3807_ = _args[17];
lean_object* v___y_3808_ = _args[18];
lean_object* v___y_3809_ = _args[19];
lean_object* v___y_3810_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3811_; uint8_t v___x_6971__boxed_3812_; lean_object* v_res_3813_; 
v___x_6970__boxed_3811_ = lean_unbox(v___x_3798_);
v___x_6971__boxed_3812_ = lean_unbox(v___x_3799_);
v_res_3813_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3790_, v___x_3791_, v_00_u03b1_3792_, v_00_u03b2_3793_, v___x_3794_, v_ctorName_3795_, v_k_3796_, v___x_3797_, v___x_6970__boxed_3811_, v___x_6971__boxed_3812_, v_a_3800_, v_x_3801_, v_xs_3802_, v_body_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_xs_3802_);
lean_dec_ref(v_a_3800_);
lean_dec(v___x_3794_);
lean_dec(v___x_3791_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3814_, lean_object* v___x_3815_, lean_object* v_00_u03b1_3816_, lean_object* v_00_u03b2_3817_, lean_object* v___x_3818_, lean_object* v_k_3819_, lean_object* v___x_3820_, uint8_t v___x_3821_, uint8_t v___x_3822_, lean_object* v_a_3823_, lean_object* v_x_3824_, lean_object* v___x_3825_, lean_object* v_ctorName_3826_, lean_object* v_minor_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___f_3837_; lean_object* v___x_3838_; 
v___x_3835_ = lean_box(v___x_3821_);
v___x_3836_ = lean_box(v___x_3822_);
v___f_3837_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3837_, 0, v___x_3814_);
lean_closure_set(v___f_3837_, 1, v___x_3815_);
lean_closure_set(v___f_3837_, 2, v_00_u03b1_3816_);
lean_closure_set(v___f_3837_, 3, v_00_u03b2_3817_);
lean_closure_set(v___f_3837_, 4, v___x_3818_);
lean_closure_set(v___f_3837_, 5, v_ctorName_3826_);
lean_closure_set(v___f_3837_, 6, v_k_3819_);
lean_closure_set(v___f_3837_, 7, v___x_3820_);
lean_closure_set(v___f_3837_, 8, v___x_3835_);
lean_closure_set(v___f_3837_, 9, v___x_3836_);
lean_closure_set(v___f_3837_, 10, v_a_3823_);
lean_closure_set(v___f_3837_, 11, v_x_3824_);
v___x_3838_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3827_, v___x_3825_, v___f_3837_, v___x_3821_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3839_ = _args[0];
lean_object* v___x_3840_ = _args[1];
lean_object* v_00_u03b1_3841_ = _args[2];
lean_object* v_00_u03b2_3842_ = _args[3];
lean_object* v___x_3843_ = _args[4];
lean_object* v_k_3844_ = _args[5];
lean_object* v___x_3845_ = _args[6];
lean_object* v___x_3846_ = _args[7];
lean_object* v___x_3847_ = _args[8];
lean_object* v_a_3848_ = _args[9];
lean_object* v_x_3849_ = _args[10];
lean_object* v___x_3850_ = _args[11];
lean_object* v_ctorName_3851_ = _args[12];
lean_object* v_minor_3852_ = _args[13];
lean_object* v___y_3853_ = _args[14];
lean_object* v___y_3854_ = _args[15];
lean_object* v___y_3855_ = _args[16];
lean_object* v___y_3856_ = _args[17];
lean_object* v___y_3857_ = _args[18];
lean_object* v___y_3858_ = _args[19];
lean_object* v___y_3859_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3860_; uint8_t v___x_6935__boxed_3861_; lean_object* v_res_3862_; 
v___x_6934__boxed_3860_ = lean_unbox(v___x_3846_);
v___x_6935__boxed_3861_ = lean_unbox(v___x_3847_);
v_res_3862_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3839_, v___x_3840_, v_00_u03b1_3841_, v_00_u03b2_3842_, v___x_3843_, v_k_3844_, v___x_3845_, v___x_6934__boxed_3860_, v___x_6935__boxed_3861_, v_a_3848_, v_x_3849_, v___x_3850_, v_ctorName_3851_, v_minor_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3863_, lean_object* v_F_3864_, lean_object* v_val_3865_, lean_object* v_k_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3863_, v_F_3864_, v_val_3865_, v_k_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3875_, lean_object* v_name_3876_, uint8_t v_bi_3877_, lean_object* v_type_3878_, lean_object* v_k_3879_, uint8_t v_kind_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3876_, v_bi_3877_, v_type_3878_, v_k_3879_, v_kind_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3889_, lean_object* v_name_3890_, lean_object* v_bi_3891_, lean_object* v_type_3892_, lean_object* v_k_3893_, lean_object* v_kind_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
uint8_t v_bi_boxed_3902_; uint8_t v_kind_boxed_3903_; lean_object* v_res_3904_; 
v_bi_boxed_3902_ = lean_unbox(v_bi_3891_);
v_kind_boxed_3903_ = lean_unbox(v_kind_3894_);
v_res_3904_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3889_, v_name_3890_, v_bi_boxed_3902_, v_type_3892_, v_k_3893_, v_kind_boxed_3903_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3905_, lean_object* v_name_3906_, lean_object* v_type_3907_, lean_object* v_k_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3906_, v_type_3907_, v_k_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3917_, lean_object* v_name_3918_, lean_object* v_type_3919_, lean_object* v_k_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3917_, v_name_3918_, v_type_3919_, v_k_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
return v_res_3928_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3874__overap_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3939_ = lean_panic_fn(v___x_3938_, v_msg_3930_);
lean_inc(v___y_3936_);
lean_inc_ref(v___y_3935_);
lean_inc(v___y_3934_);
lean_inc_ref(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc_ref(v___y_3931_);
v___x_3940_ = lean_apply_7(v___x_3874__overap_3939_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, lean_box(0));
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
return v_res_3949_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3954_ = lean_unsigned_to_nat(49u);
v___x_3955_ = lean_unsigned_to_nat(186u);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3958_ = l_mkPanicMessageWithDecl(v___x_3957_, v___x_3956_, v___x_3955_, v___x_3954_, v___x_3953_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3964_, lean_object* v_a_3965_, lean_object* v_k_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v_FNew_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
uint8_t v___x_4042__boxed_3980_; uint8_t v___x_4043__boxed_3981_; uint8_t v___x_4044__boxed_3982_; lean_object* v_res_3983_; 
v___x_4042__boxed_3980_ = lean_unbox(v___x_3969_);
v___x_4043__boxed_3981_ = lean_unbox(v___x_3970_);
v___x_4044__boxed_3982_ = lean_unbox(v___x_3971_);
v_res_3983_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3964_, v_a_3965_, v_k_3966_, v___x_3967_, v___x_3968_, v___x_4042__boxed_3980_, v___x_4043__boxed_3981_, v___x_4044__boxed_3982_, v_FNew_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___x_3967_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3984_, lean_object* v___x_3985_, lean_object* v___x_3986_, lean_object* v___x_3987_, uint8_t v___x_3988_, uint8_t v___x_3989_, lean_object* v_00_u03b1_3990_, lean_object* v_00_u03b2_3991_, lean_object* v___x_3992_, lean_object* v_k_3993_, lean_object* v___x_3994_, lean_object* v_a_3995_, lean_object* v_x_3996_, lean_object* v_xs_3997_, lean_object* v_body_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; lean_object* v___x_4012_; 
lean_inc_ref(v___x_3984_);
v___x_4006_ = lean_array_get(v___x_3984_, v_xs_3997_, v___x_3985_);
v___x_4007_ = lean_array_get(v___x_3984_, v_xs_3997_, v___x_3986_);
v___x_4008_ = lean_array_get_size(v_xs_3997_);
v___x_4009_ = l_Array_toSubarray___redArg(v_xs_3997_, v___x_3987_, v___x_4008_);
v___x_4010_ = l_Subarray_copy___redArg(v___x_4009_);
v___x_4011_ = 1;
v___x_4012_ = l_Lean_Meta_mkLambdaFVars(v___x_4010_, v_body_3998_, v___x_3988_, v___x_3989_, v___x_3988_, v___x_3989_, v___x_4011_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec_ref(v___x_4010_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4039_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4039_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4039_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4017_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 1);
lean_ctor_set(v___x_4015_, 0, v_00_u03b1_3990_);
v___x_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_00_u03b1_3990_);
v___x_4019_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4020_, 0, v_00_u03b2_3991_);
lean_inc(v___x_4006_);
v___x_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4006_);
lean_inc(v___x_4007_);
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4007_);
v___x_4023_ = lean_mk_empty_array_with_capacity(v___x_3992_);
v___x_4024_ = lean_array_push(v___x_4023_, v___x_4019_);
v___x_4025_ = lean_array_push(v___x_4024_, v___x_4020_);
v___x_4026_ = lean_array_push(v___x_4025_, v___x_4021_);
v___x_4027_ = lean_array_push(v___x_4026_, v___x_4022_);
v___x_4028_ = l_Lean_Meta_mkAppOptM(v___x_4017_, v___x_4027_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___f_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
v___x_4030_ = lean_box(v___x_3988_);
v___x_4031_ = lean_box(v___x_3989_);
v___x_4032_ = lean_box(v___x_4011_);
v___f_4033_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4033_, 0, v___x_4007_);
lean_closure_set(v___f_4033_, 1, v_a_4013_);
lean_closure_set(v___f_4033_, 2, v_k_3993_);
lean_closure_set(v___f_4033_, 3, v___x_3994_);
lean_closure_set(v___f_4033_, 4, v___x_4006_);
lean_closure_set(v___f_4033_, 5, v___x_4030_);
lean_closure_set(v___f_4033_, 6, v___x_4031_);
lean_closure_set(v___f_4033_, 7, v___x_4032_);
v___x_4034_ = l_Lean_LocalDecl_type(v_a_3995_);
v___x_4035_ = l_Lean_Expr_replaceFVar(v___x_4034_, v_x_3996_, v_a_4029_);
lean_dec(v_a_4029_);
lean_dec_ref(v___x_4034_);
v___x_4036_ = l_Lean_LocalDecl_userName(v_a_3995_);
v___x_4037_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4036_, v___x_4035_, v___f_4033_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4037_;
}
else
{
lean_dec(v_a_4013_);
lean_dec(v___x_4007_);
lean_dec(v___x_4006_);
lean_dec_ref(v_x_3996_);
lean_dec(v___x_3994_);
lean_dec_ref(v_k_3993_);
return v___x_4028_;
}
}
}
}
else
{
lean_dec(v___x_4007_);
lean_dec(v___x_4006_);
lean_dec_ref(v_x_3996_);
lean_dec(v___x_3994_);
lean_dec_ref(v_k_3993_);
lean_dec_ref(v_00_u03b2_3991_);
lean_dec_ref(v_00_u03b1_3990_);
return v___x_4012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_4040_ = _args[0];
lean_object* v___x_4041_ = _args[1];
lean_object* v___x_4042_ = _args[2];
lean_object* v___x_4043_ = _args[3];
lean_object* v___x_4044_ = _args[4];
lean_object* v___x_4045_ = _args[5];
lean_object* v_00_u03b1_4046_ = _args[6];
lean_object* v_00_u03b2_4047_ = _args[7];
lean_object* v___x_4048_ = _args[8];
lean_object* v_k_4049_ = _args[9];
lean_object* v___x_4050_ = _args[10];
lean_object* v_a_4051_ = _args[11];
lean_object* v_x_4052_ = _args[12];
lean_object* v_xs_4053_ = _args[13];
lean_object* v_body_4054_ = _args[14];
lean_object* v___y_4055_ = _args[15];
lean_object* v___y_4056_ = _args[16];
lean_object* v___y_4057_ = _args[17];
lean_object* v___y_4058_ = _args[18];
lean_object* v___y_4059_ = _args[19];
lean_object* v___y_4060_ = _args[20];
lean_object* v___y_4061_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_4062_; uint8_t v___x_4070__boxed_4063_; lean_object* v_res_4064_; 
v___x_4069__boxed_4062_ = lean_unbox(v___x_4044_);
v___x_4070__boxed_4063_ = lean_unbox(v___x_4045_);
v_res_4064_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_4040_, v___x_4041_, v___x_4042_, v___x_4043_, v___x_4069__boxed_4062_, v___x_4070__boxed_4063_, v_00_u03b1_4046_, v_00_u03b2_4047_, v___x_4048_, v_k_4049_, v___x_4050_, v_a_4051_, v_x_4052_, v_xs_4053_, v_body_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v_a_4051_);
lean_dec(v___x_4048_);
lean_dec(v___x_4042_);
lean_dec(v___x_4041_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_4068_, lean_object* v_F_4069_, lean_object* v_val_4070_, lean_object* v_k_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4089_; uint8_t v___x_4181_; 
v___x_4181_ = l_Lean_Expr_isFVar(v_x_4068_);
if (v___x_4181_ == 0)
{
v___y_4089_ = v___x_4181_;
goto v___jp_4088_;
}
else
{
lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4183_ = lean_unsigned_to_nat(5u);
v___x_4184_ = l_Lean_Expr_isAppOfArity(v_val_4070_, v___x_4182_, v___x_4183_);
v___y_4089_ = v___x_4184_;
goto v___jp_4088_;
}
v___jp_4079_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4087_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4086_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
return v___x_4087_;
}
v___jp_4088_:
{
if (v___y_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v_x_4068_);
lean_inc(v_a_4077_);
lean_inc_ref(v_a_4076_);
lean_inc(v_a_4075_);
lean_inc_ref(v_a_4074_);
lean_inc(v_a_4073_);
lean_inc_ref(v_a_4072_);
v___x_4090_ = lean_apply_9(v_k_4071_, v_F_4069_, v_val_4070_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, lean_box(0));
return v___x_4090_;
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v___x_4091_ = lean_unsigned_to_nat(3u);
v___x_4092_ = l_Lean_Expr_getAppNumArgs(v_val_4070_);
v___x_4093_ = lean_nat_sub(v___x_4092_, v___x_4091_);
v___x_4094_ = lean_unsigned_to_nat(1u);
v___x_4095_ = lean_nat_sub(v___x_4093_, v___x_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = l_Lean_Expr_getRevArg_x21(v_val_4070_, v___x_4095_);
v___x_4097_ = lean_expr_eqv(v___x_4096_, v_x_4068_);
lean_dec_ref(v___x_4096_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
lean_dec(v___x_4092_);
lean_dec_ref(v_x_4068_);
lean_inc(v_a_4077_);
lean_inc_ref(v_a_4076_);
lean_inc(v_a_4075_);
lean_inc_ref(v_a_4074_);
lean_inc(v_a_4073_);
lean_inc_ref(v_a_4072_);
v___x_4098_ = lean_apply_9(v_k_4071_, v_F_4069_, v_val_4070_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, lean_box(0));
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v___x_4099_ = lean_unsigned_to_nat(4u);
v___x_4100_ = lean_nat_sub(v___x_4092_, v___x_4099_);
v___x_4101_ = lean_nat_sub(v___x_4100_, v___x_4094_);
lean_dec(v___x_4100_);
v___x_4102_ = l_Lean_Expr_getRevArg_x21(v_val_4070_, v___x_4101_);
v___x_4103_ = l_Lean_Expr_isLambda(v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; 
lean_dec_ref(v___x_4102_);
lean_dec(v___x_4092_);
lean_dec_ref(v_x_4068_);
lean_inc(v_a_4077_);
lean_inc_ref(v_a_4076_);
lean_inc(v_a_4075_);
lean_inc_ref(v_a_4074_);
lean_inc(v_a_4073_);
lean_inc_ref(v_a_4072_);
v___x_4104_ = lean_apply_9(v_k_4071_, v_F_4069_, v_val_4070_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, lean_box(0));
return v___x_4104_;
}
else
{
lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4105_ = l_Lean_Expr_bindingBody_x21(v___x_4102_);
lean_dec_ref(v___x_4102_);
v___x_4106_ = l_Lean_Expr_isLambda(v___x_4105_);
lean_dec_ref(v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; 
lean_dec(v___x_4092_);
lean_dec_ref(v_x_4068_);
lean_inc(v_a_4077_);
lean_inc_ref(v_a_4076_);
lean_inc(v_a_4075_);
lean_inc_ref(v_a_4074_);
lean_inc(v_a_4073_);
lean_inc_ref(v_a_4072_);
v___x_4107_ = lean_apply_9(v_k_4071_, v_F_4069_, v_val_4070_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, lean_box(0));
return v___x_4107_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = l_Lean_Expr_getAppFn(v_val_4070_);
v___x_4109_ = l_Lean_Expr_constLevels_x21(v___x_4108_);
lean_dec_ref(v___x_4108_);
if (lean_obj_tag(v___x_4109_) == 1)
{
lean_object* v_tail_4110_; 
v_tail_4110_ = lean_ctor_get(v___x_4109_, 1);
lean_inc(v_tail_4110_);
lean_dec_ref(v___x_4109_);
if (lean_obj_tag(v_tail_4110_) == 1)
{
lean_object* v_tail_4111_; 
v_tail_4111_ = lean_ctor_get(v_tail_4110_, 1);
lean_inc(v_tail_4111_);
if (lean_obj_tag(v_tail_4111_) == 1)
{
lean_object* v_tail_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4179_; 
v_tail_4112_ = lean_ctor_get(v_tail_4111_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_tail_4111_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; 
v_unused_4180_ = lean_ctor_get(v_tail_4111_, 0);
lean_dec(v_unused_4180_);
v___x_4114_ = v_tail_4111_;
v_isShared_4115_ = v_isSharedCheck_4179_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_tail_4112_);
lean_dec(v_tail_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4179_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
if (lean_obj_tag(v_tail_4112_) == 0)
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = l_Lean_Expr_fvarId_x21(v_F_4069_);
lean_inc_ref(v_a_4074_);
v___x_4117_ = l_Lean_FVarId_getDecl___redArg(v___x_4116_, v_a_4074_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v_dummy_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v_args_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v_00_u03b1_4125_; lean_object* v___x_4126_; lean_object* v___f_4127_; lean_object* v_00_u03b2_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref(v___x_4117_);
v_dummy_4119_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_4092_);
v___x_4120_ = lean_mk_array(v___x_4092_, v_dummy_4119_);
v___x_4121_ = lean_nat_sub(v___x_4092_, v___x_4094_);
lean_dec(v___x_4092_);
v_args_4122_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_4070_, v___x_4120_, v___x_4121_);
v___x_4123_ = l_Lean_instInhabitedExpr;
v___x_4124_ = lean_unsigned_to_nat(0u);
v_00_u03b1_4125_ = lean_array_get(v___x_4123_, v_args_4122_, v___x_4124_);
v___x_4126_ = lean_box(v___x_4103_);
lean_inc_ref(v_x_4068_);
lean_inc(v_a_4118_);
v___f_4127_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4127_, 0, v_a_4118_);
lean_closure_set(v___f_4127_, 1, v___x_4123_);
lean_closure_set(v___f_4127_, 2, v___x_4124_);
lean_closure_set(v___f_4127_, 3, v_x_4068_);
lean_closure_set(v___f_4127_, 4, v___x_4126_);
v_00_u03b2_4128_ = lean_array_get(v___x_4123_, v_args_4122_, v___x_4094_);
v___x_4129_ = lean_unsigned_to_nat(2u);
v___x_4130_ = lean_array_get(v___x_4123_, v_args_4122_, v___x_4129_);
v___x_4131_ = 0;
v___x_4132_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4130_, v___f_4127_, v___x_4131_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v_fst_4134_; lean_object* v_snd_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref(v___x_4132_);
v_fst_4134_ = lean_ctor_get(v_a_4133_, 0);
lean_inc(v_fst_4134_);
v_snd_4135_ = lean_ctor_get(v_a_4133_, 1);
lean_inc(v_snd_4135_);
lean_dec(v_a_4133_);
v___x_4136_ = lean_box(v___x_4131_);
v___x_4137_ = lean_box(v___x_4103_);
lean_inc_ref(v_x_4068_);
lean_inc(v_00_u03b2_4128_);
lean_inc(v_00_u03b1_4125_);
v___f_4138_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4138_, 0, v___x_4123_);
lean_closure_set(v___f_4138_, 1, v___x_4124_);
lean_closure_set(v___f_4138_, 2, v___x_4094_);
lean_closure_set(v___f_4138_, 3, v___x_4129_);
lean_closure_set(v___f_4138_, 4, v___x_4136_);
lean_closure_set(v___f_4138_, 5, v___x_4137_);
lean_closure_set(v___f_4138_, 6, v_00_u03b1_4125_);
lean_closure_set(v___f_4138_, 7, v_00_u03b2_4128_);
lean_closure_set(v___f_4138_, 8, v___x_4099_);
lean_closure_set(v___f_4138_, 9, v_k_4071_);
lean_closure_set(v___f_4138_, 10, v___x_4091_);
lean_closure_set(v___f_4138_, 11, v_a_4118_);
lean_closure_set(v___f_4138_, 12, v_x_4068_);
v___x_4139_ = lean_array_get(v___x_4123_, v_args_4122_, v___x_4099_);
lean_dec_ref(v_args_4122_);
v___x_4140_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4139_, v___f_4138_, v___x_4131_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4162_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4162_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4162_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4145_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v_tail_4110_);
lean_ctor_set(v___x_4114_, 0, v_snd_4135_);
v___x_4147_ = v___x_4114_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_snd_4135_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_tail_4110_);
v___x_4147_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4148_ = l_Lean_mkConst(v___x_4145_, v___x_4147_);
v___x_4149_ = lean_unsigned_to_nat(6u);
v___x_4150_ = lean_mk_empty_array_with_capacity(v___x_4149_);
v___x_4151_ = lean_array_push(v___x_4150_, v_00_u03b1_4125_);
v___x_4152_ = lean_array_push(v___x_4151_, v_00_u03b2_4128_);
v___x_4153_ = lean_array_push(v___x_4152_, v_fst_4134_);
v___x_4154_ = lean_array_push(v___x_4153_, v_x_4068_);
v___x_4155_ = lean_array_push(v___x_4154_, v_a_4141_);
v___x_4156_ = lean_array_push(v___x_4155_, v_F_4069_);
v___x_4157_ = l_Lean_mkAppN(v___x_4148_, v___x_4156_);
lean_dec_ref(v___x_4156_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4157_);
v___x_4159_ = v___x_4143_;
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
lean_dec(v_snd_4135_);
lean_dec(v_fst_4134_);
lean_dec(v_00_u03b2_4128_);
lean_dec(v_00_u03b1_4125_);
lean_del_object(v___x_4114_);
lean_dec_ref(v_tail_4110_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
return v___x_4140_;
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec(v_00_u03b2_4128_);
lean_dec(v_00_u03b1_4125_);
lean_dec_ref(v_args_4122_);
lean_dec(v_a_4118_);
lean_del_object(v___x_4114_);
lean_dec_ref(v_tail_4110_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v_a_4163_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4132_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4132_);
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
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_del_object(v___x_4114_);
lean_dec_ref(v_tail_4110_);
lean_dec(v___x_4092_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_val_4070_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v_a_4171_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4117_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4117_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
lean_del_object(v___x_4114_);
lean_dec(v_tail_4112_);
lean_dec_ref(v_tail_4110_);
lean_dec(v___x_4092_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_val_4070_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v___y_4080_ = v_a_4072_;
v___y_4081_ = v_a_4073_;
v___y_4082_ = v_a_4074_;
v___y_4083_ = v_a_4075_;
v___y_4084_ = v_a_4076_;
v___y_4085_ = v_a_4077_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v_tail_4111_);
lean_dec_ref(v_tail_4110_);
lean_dec(v___x_4092_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_val_4070_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v___y_4080_ = v_a_4072_;
v___y_4081_ = v_a_4073_;
v___y_4082_ = v_a_4074_;
v___y_4083_ = v_a_4075_;
v___y_4084_ = v_a_4076_;
v___y_4085_ = v_a_4077_;
goto v___jp_4079_;
}
}
else
{
lean_dec(v_tail_4110_);
lean_dec(v___x_4092_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_val_4070_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v___y_4080_ = v_a_4072_;
v___y_4081_ = v_a_4073_;
v___y_4082_ = v_a_4074_;
v___y_4083_ = v_a_4075_;
v___y_4084_ = v_a_4076_;
v___y_4085_ = v_a_4077_;
goto v___jp_4079_;
}
}
else
{
lean_dec(v___x_4109_);
lean_dec(v___x_4092_);
lean_dec_ref(v_k_4071_);
lean_dec_ref(v_val_4070_);
lean_dec_ref(v_F_4069_);
lean_dec_ref(v_x_4068_);
v___y_4080_ = v_a_4072_;
v___y_4081_ = v_a_4073_;
v___y_4082_ = v_a_4074_;
v___y_4083_ = v_a_4075_;
v___y_4084_ = v_a_4076_;
v___y_4085_ = v_a_4077_;
goto v___jp_4079_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4185_, lean_object* v_a_4186_, lean_object* v_k_4187_, lean_object* v___x_4188_, lean_object* v___x_4189_, uint8_t v___x_4190_, uint8_t v___x_4191_, uint8_t v___x_4192_, lean_object* v_FNew_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
lean_inc_ref(v_FNew_4193_);
lean_inc_ref(v___x_4185_);
v___x_4201_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4185_, v_FNew_4193_, v_a_4186_, v_k_4187_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4201_);
v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4188_);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4189_);
v___x_4205_ = lean_array_push(v___x_4204_, v___x_4185_);
v___x_4206_ = lean_array_push(v___x_4205_, v_FNew_4193_);
v___x_4207_ = l_Lean_Meta_mkLambdaFVars(v___x_4206_, v_a_4202_, v___x_4190_, v___x_4191_, v___x_4190_, v___x_4191_, v___x_4192_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec_ref(v___x_4206_);
return v___x_4207_;
}
else
{
lean_dec_ref(v_FNew_4193_);
lean_dec_ref(v___x_4189_);
lean_dec_ref(v___x_4185_);
return v___x_4201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4208_, lean_object* v_F_4209_, lean_object* v_val_4210_, lean_object* v_k_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4208_, v_F_4209_, v_val_4210_, v_k_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_ref_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec_ref(v___x_4233_);
v_ref_4234_ = lean_ctor_get(v___y_4230_, 5);
v___x_4235_ = 0;
v___x_4236_ = l_Lean_SourceInfo_fromRef(v_ref_4234_, v___x_4235_);
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4236_);
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4236_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l_Lean_Syntax_node1(v___x_4236_, v___x_4237_, v___x_4239_);
v___x_4241_ = l_Lean_Elab_Tactic_evalTactic(v___x_4240_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
return v___x_4241_;
}
else
{
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v___f_4261_; lean_object* v___x_4262_; 
v___f_4261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4262_ = l_Lean_Elab_Tactic_run(v_mvarId_4253_, v___f_4261_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4273_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4265_ = v___x_4262_;
v_isShared_4266_ = v_isSharedCheck_4273_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4273_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
uint8_t v___x_4267_; 
v___x_4267_ = l_List_isEmpty___redArg(v_a_4263_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
lean_del_object(v___x_4265_);
v___x_4268_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4263_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4268_;
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4271_; 
lean_dec(v_a_4263_);
v___x_4269_ = lean_box(0);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4269_);
v___x_4271_ = v___x_4265_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
v_a_4274_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4262_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4262_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_, lean_object* v_x_4294_){
_start:
{
lean_object* v_ks_4295_; lean_object* v_vs_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4320_; 
v_ks_4295_ = lean_ctor_get(v_x_4291_, 0);
v_vs_4296_ = lean_ctor_get(v_x_4291_, 1);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_x_4291_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4298_ = v_x_4291_;
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_vs_4296_);
lean_inc(v_ks_4295_);
lean_dec(v_x_4291_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4300_ = lean_array_get_size(v_ks_4295_);
v___x_4301_ = lean_nat_dec_lt(v_x_4292_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
lean_dec(v_x_4292_);
v___x_4302_ = lean_array_push(v_ks_4295_, v_x_4293_);
v___x_4303_ = lean_array_push(v_vs_4296_, v_x_4294_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 1, v___x_4303_);
lean_ctor_set(v___x_4298_, 0, v___x_4302_);
v___x_4305_ = v___x_4298_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4306_, 1, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
else
{
lean_object* v_k_x27_4307_; uint8_t v___x_4308_; 
v_k_x27_4307_ = lean_array_fget_borrowed(v_ks_4295_, v_x_4292_);
v___x_4308_ = l_Lean_instBEqMVarId_beq(v_x_4293_, v_k_x27_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4310_; 
if (v_isShared_4299_ == 0)
{
v___x_4310_ = v___x_4298_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_ks_4295_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_vs_4296_);
v___x_4310_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = lean_unsigned_to_nat(1u);
v___x_4312_ = lean_nat_add(v_x_4292_, v___x_4311_);
lean_dec(v_x_4292_);
v_x_4291_ = v___x_4310_;
v_x_4292_ = v___x_4312_;
goto _start;
}
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4315_ = lean_array_fset(v_ks_4295_, v_x_4292_, v_x_4293_);
v___x_4316_ = lean_array_fset(v_vs_4296_, v_x_4292_, v_x_4294_);
lean_dec(v_x_4292_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 1, v___x_4316_);
lean_ctor_set(v___x_4298_, 0, v___x_4315_);
v___x_4318_ = v___x_4298_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4321_, lean_object* v_k_4322_, lean_object* v_v_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4321_, v___x_4324_, v_k_4322_, v_v_4323_);
return v___x_4325_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4326_; size_t v___x_4327_; size_t v___x_4328_; 
v___x_4326_ = ((size_t)5ULL);
v___x_4327_ = ((size_t)1ULL);
v___x_4328_ = lean_usize_shift_left(v___x_4327_, v___x_4326_);
return v___x_4328_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4329_; size_t v___x_4330_; size_t v___x_4331_; 
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4331_ = lean_usize_sub(v___x_4330_, v___x_4329_);
return v___x_4331_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4333_, size_t v_x_4334_, size_t v_x_4335_, lean_object* v_x_4336_, lean_object* v_x_4337_){
_start:
{
if (lean_obj_tag(v_x_4333_) == 0)
{
lean_object* v_es_4338_; size_t v___x_4339_; size_t v___x_4340_; size_t v___x_4341_; size_t v___x_4342_; lean_object* v_j_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_es_4338_ = lean_ctor_get(v_x_4333_, 0);
v___x_4339_ = ((size_t)5ULL);
v___x_4340_ = ((size_t)1ULL);
v___x_4341_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4342_ = lean_usize_land(v_x_4334_, v___x_4341_);
v_j_4343_ = lean_usize_to_nat(v___x_4342_);
v___x_4344_ = lean_array_get_size(v_es_4338_);
v___x_4345_ = lean_nat_dec_lt(v_j_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec(v_j_4343_);
lean_dec(v_x_4337_);
lean_dec(v_x_4336_);
return v_x_4333_;
}
else
{
lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4382_; 
lean_inc_ref(v_es_4338_);
v_isSharedCheck_4382_ = !lean_is_exclusive(v_x_4333_);
if (v_isSharedCheck_4382_ == 0)
{
lean_object* v_unused_4383_; 
v_unused_4383_ = lean_ctor_get(v_x_4333_, 0);
lean_dec(v_unused_4383_);
v___x_4347_ = v_x_4333_;
v_isShared_4348_ = v_isSharedCheck_4382_;
goto v_resetjp_4346_;
}
else
{
lean_dec(v_x_4333_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4382_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_v_4349_; lean_object* v___x_4350_; lean_object* v_xs_x27_4351_; lean_object* v___y_4353_; 
v_v_4349_ = lean_array_fget(v_es_4338_, v_j_4343_);
v___x_4350_ = lean_box(0);
v_xs_x27_4351_ = lean_array_fset(v_es_4338_, v_j_4343_, v___x_4350_);
switch(lean_obj_tag(v_v_4349_))
{
case 0:
{
lean_object* v_key_4358_; lean_object* v_val_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4369_; 
v_key_4358_ = lean_ctor_get(v_v_4349_, 0);
v_val_4359_ = lean_ctor_get(v_v_4349_, 1);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_v_4349_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4361_ = v_v_4349_;
v_isShared_4362_ = v_isSharedCheck_4369_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_val_4359_);
lean_inc(v_key_4358_);
lean_dec(v_v_4349_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4369_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
uint8_t v___x_4363_; 
v___x_4363_ = l_Lean_instBEqMVarId_beq(v_x_4336_, v_key_4358_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_del_object(v___x_4361_);
v___x_4364_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4358_, v_val_4359_, v_x_4336_, v_x_4337_);
v___x_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
v___y_4353_ = v___x_4365_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4367_; 
lean_dec(v_val_4359_);
lean_dec(v_key_4358_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 1, v_x_4337_);
lean_ctor_set(v___x_4361_, 0, v_x_4336_);
v___x_4367_ = v___x_4361_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_x_4336_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_x_4337_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
v___y_4353_ = v___x_4367_;
goto v___jp_4352_;
}
}
}
}
case 1:
{
lean_object* v_node_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4380_; 
v_node_4370_ = lean_ctor_get(v_v_4349_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_v_4349_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4372_ = v_v_4349_;
v_isShared_4373_ = v_isSharedCheck_4380_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_node_4370_);
lean_dec(v_v_4349_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4380_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
size_t v___x_4374_; size_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v___x_4374_ = lean_usize_shift_right(v_x_4334_, v___x_4339_);
v___x_4375_ = lean_usize_add(v_x_4335_, v___x_4340_);
v___x_4376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4370_, v___x_4374_, v___x_4375_, v_x_4336_, v_x_4337_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4376_);
v___x_4378_ = v___x_4372_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
v___y_4353_ = v___x_4378_;
goto v___jp_4352_;
}
}
}
default: 
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_x_4336_);
lean_ctor_set(v___x_4381_, 1, v_x_4337_);
v___y_4353_ = v___x_4381_;
goto v___jp_4352_;
}
}
v___jp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4354_ = lean_array_fset(v_xs_x27_4351_, v_j_4343_, v___y_4353_);
lean_dec(v_j_4343_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4354_);
v___x_4356_ = v___x_4347_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
else
{
lean_object* v_ks_4384_; lean_object* v_vs_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4405_; 
v_ks_4384_ = lean_ctor_get(v_x_4333_, 0);
v_vs_4385_ = lean_ctor_get(v_x_4333_, 1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_x_4333_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4387_ = v_x_4333_;
v_isShared_4388_ = v_isSharedCheck_4405_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_vs_4385_);
lean_inc(v_ks_4384_);
lean_dec(v_x_4333_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4405_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_ks_4384_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_vs_4385_);
v___x_4390_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v_newNode_4391_; uint8_t v___y_4393_; size_t v___x_4399_; uint8_t v___x_4400_; 
v_newNode_4391_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4390_, v_x_4336_, v_x_4337_);
v___x_4399_ = ((size_t)7ULL);
v___x_4400_ = lean_usize_dec_le(v___x_4399_, v_x_4335_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4401_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4391_);
v___x_4402_ = lean_unsigned_to_nat(4u);
v___x_4403_ = lean_nat_dec_lt(v___x_4401_, v___x_4402_);
lean_dec(v___x_4401_);
v___y_4393_ = v___x_4403_;
goto v___jp_4392_;
}
else
{
v___y_4393_ = v___x_4400_;
goto v___jp_4392_;
}
v___jp_4392_:
{
if (v___y_4393_ == 0)
{
lean_object* v_ks_4394_; lean_object* v_vs_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_ks_4394_ = lean_ctor_get(v_newNode_4391_, 0);
lean_inc_ref(v_ks_4394_);
v_vs_4395_ = lean_ctor_get(v_newNode_4391_, 1);
lean_inc_ref(v_vs_4395_);
lean_dec_ref(v_newNode_4391_);
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_4398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4335_, v_ks_4394_, v_vs_4395_, v___x_4396_, v___x_4397_);
lean_dec_ref(v_vs_4395_);
lean_dec_ref(v_ks_4394_);
return v___x_4398_;
}
else
{
return v_newNode_4391_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4406_, lean_object* v_keys_4407_, lean_object* v_vals_4408_, lean_object* v_i_4409_, lean_object* v_entries_4410_){
_start:
{
lean_object* v___x_4411_; uint8_t v___x_4412_; 
v___x_4411_ = lean_array_get_size(v_keys_4407_);
v___x_4412_ = lean_nat_dec_lt(v_i_4409_, v___x_4411_);
if (v___x_4412_ == 0)
{
lean_dec(v_i_4409_);
return v_entries_4410_;
}
else
{
lean_object* v_k_4413_; lean_object* v_v_4414_; uint64_t v___x_4415_; size_t v_h_4416_; size_t v___x_4417_; lean_object* v___x_4418_; size_t v___x_4419_; size_t v___x_4420_; size_t v___x_4421_; size_t v_h_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_k_4413_ = lean_array_fget_borrowed(v_keys_4407_, v_i_4409_);
v_v_4414_ = lean_array_fget_borrowed(v_vals_4408_, v_i_4409_);
v___x_4415_ = l_Lean_instHashableMVarId_hash(v_k_4413_);
v_h_4416_ = lean_uint64_to_usize(v___x_4415_);
v___x_4417_ = ((size_t)5ULL);
v___x_4418_ = lean_unsigned_to_nat(1u);
v___x_4419_ = ((size_t)1ULL);
v___x_4420_ = lean_usize_sub(v_depth_4406_, v___x_4419_);
v___x_4421_ = lean_usize_mul(v___x_4417_, v___x_4420_);
v_h_4422_ = lean_usize_shift_right(v_h_4416_, v___x_4421_);
v___x_4423_ = lean_nat_add(v_i_4409_, v___x_4418_);
lean_dec(v_i_4409_);
lean_inc(v_v_4414_);
lean_inc(v_k_4413_);
v___x_4424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4410_, v_h_4422_, v_depth_4406_, v_k_4413_, v_v_4414_);
v_i_4409_ = v___x_4423_;
v_entries_4410_ = v___x_4424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4426_, lean_object* v_keys_4427_, lean_object* v_vals_4428_, lean_object* v_i_4429_, lean_object* v_entries_4430_){
_start:
{
size_t v_depth_boxed_4431_; lean_object* v_res_4432_; 
v_depth_boxed_4431_ = lean_unbox_usize(v_depth_4426_);
lean_dec(v_depth_4426_);
v_res_4432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4431_, v_keys_4427_, v_vals_4428_, v_i_4429_, v_entries_4430_);
lean_dec_ref(v_vals_4428_);
lean_dec_ref(v_keys_4427_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4433_, lean_object* v_x_4434_, lean_object* v_x_4435_, lean_object* v_x_4436_, lean_object* v_x_4437_){
_start:
{
size_t v_x_4257__boxed_4438_; size_t v_x_4258__boxed_4439_; lean_object* v_res_4440_; 
v_x_4257__boxed_4438_ = lean_unbox_usize(v_x_4434_);
lean_dec(v_x_4434_);
v_x_4258__boxed_4439_ = lean_unbox_usize(v_x_4435_);
lean_dec(v_x_4435_);
v_res_4440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4433_, v_x_4257__boxed_4438_, v_x_4258__boxed_4439_, v_x_4436_, v_x_4437_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4441_, lean_object* v_x_4442_, lean_object* v_x_4443_){
_start:
{
uint64_t v___x_4444_; size_t v___x_4445_; size_t v___x_4446_; lean_object* v___x_4447_; 
v___x_4444_ = l_Lean_instHashableMVarId_hash(v_x_4442_);
v___x_4445_ = lean_uint64_to_usize(v___x_4444_);
v___x_4446_ = ((size_t)1ULL);
v___x_4447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4441_, v___x_4445_, v___x_4446_, v_x_4442_, v_x_4443_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4448_, lean_object* v_val_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; lean_object* v_mctx_4453_; lean_object* v_cache_4454_; lean_object* v_zetaDeltaFVarIds_4455_; lean_object* v_postponed_4456_; lean_object* v_diag_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4484_; 
v___x_4452_ = lean_st_ref_take(v___y_4450_);
v_mctx_4453_ = lean_ctor_get(v___x_4452_, 0);
v_cache_4454_ = lean_ctor_get(v___x_4452_, 1);
v_zetaDeltaFVarIds_4455_ = lean_ctor_get(v___x_4452_, 2);
v_postponed_4456_ = lean_ctor_get(v___x_4452_, 3);
v_diag_4457_ = lean_ctor_get(v___x_4452_, 4);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4459_ = v___x_4452_;
v_isShared_4460_ = v_isSharedCheck_4484_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_diag_4457_);
lean_inc(v_postponed_4456_);
lean_inc(v_zetaDeltaFVarIds_4455_);
lean_inc(v_cache_4454_);
lean_inc(v_mctx_4453_);
lean_dec(v___x_4452_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4484_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_depth_4461_; lean_object* v_levelAssignDepth_4462_; lean_object* v_mvarCounter_4463_; lean_object* v_lDepth_4464_; lean_object* v_decls_4465_; lean_object* v_userNames_4466_; lean_object* v_lAssignment_4467_; lean_object* v_eAssignment_4468_; lean_object* v_dAssignment_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4483_; 
v_depth_4461_ = lean_ctor_get(v_mctx_4453_, 0);
v_levelAssignDepth_4462_ = lean_ctor_get(v_mctx_4453_, 1);
v_mvarCounter_4463_ = lean_ctor_get(v_mctx_4453_, 2);
v_lDepth_4464_ = lean_ctor_get(v_mctx_4453_, 3);
v_decls_4465_ = lean_ctor_get(v_mctx_4453_, 4);
v_userNames_4466_ = lean_ctor_get(v_mctx_4453_, 5);
v_lAssignment_4467_ = lean_ctor_get(v_mctx_4453_, 6);
v_eAssignment_4468_ = lean_ctor_get(v_mctx_4453_, 7);
v_dAssignment_4469_ = lean_ctor_get(v_mctx_4453_, 8);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_mctx_4453_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4471_ = v_mctx_4453_;
v_isShared_4472_ = v_isSharedCheck_4483_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_dAssignment_4469_);
lean_inc(v_eAssignment_4468_);
lean_inc(v_lAssignment_4467_);
lean_inc(v_userNames_4466_);
lean_inc(v_decls_4465_);
lean_inc(v_lDepth_4464_);
lean_inc(v_mvarCounter_4463_);
lean_inc(v_levelAssignDepth_4462_);
lean_inc(v_depth_4461_);
lean_dec(v_mctx_4453_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4483_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4468_, v_mvarId_4448_, v_val_4449_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 7, v___x_4473_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_depth_4461_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_levelAssignDepth_4462_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_mvarCounter_4463_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v_lDepth_4464_);
lean_ctor_set(v_reuseFailAlloc_4482_, 4, v_decls_4465_);
lean_ctor_set(v_reuseFailAlloc_4482_, 5, v_userNames_4466_);
lean_ctor_set(v_reuseFailAlloc_4482_, 6, v_lAssignment_4467_);
lean_ctor_set(v_reuseFailAlloc_4482_, 7, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4482_, 8, v_dAssignment_4469_);
v___x_4475_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4475_);
v___x_4477_ = v___x_4459_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_cache_4454_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_zetaDeltaFVarIds_4455_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_postponed_4456_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v_diag_4457_);
v___x_4477_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_st_ref_set(v___y_4450_, v___x_4477_);
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4485_, lean_object* v_val_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4485_, v_val_4486_, v___y_4487_);
lean_dec(v___y_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4494_, lean_object* v_mv_u2082_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4504_; 
lean_inc(v_mv_u2081_4494_);
v___x_4504_ = l_Lean_MVarId_getDecl(v_mv_u2081_4494_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4506_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
lean_inc(v_mv_u2082_4495_);
v___x_4506_ = l_Lean_MVarId_getDecl(v_mv_u2082_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v_lctx_4508_; lean_object* v_type_4509_; lean_object* v_lctx_4510_; lean_object* v_type_4511_; uint8_t v___x_4512_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref(v___x_4506_);
v_lctx_4508_ = lean_ctor_get(v_a_4505_, 1);
lean_inc_ref(v_lctx_4508_);
v_type_4509_ = lean_ctor_get(v_a_4505_, 2);
lean_inc_ref(v_type_4509_);
lean_dec(v_a_4505_);
v_lctx_4510_ = lean_ctor_get(v_a_4507_, 1);
lean_inc_ref(v_lctx_4510_);
v_type_4511_ = lean_ctor_get(v_a_4507_, 2);
lean_inc_ref(v_type_4511_);
lean_dec(v_a_4507_);
v___x_4512_ = lean_expr_eqv(v_type_4509_, v_type_4511_);
lean_dec_ref(v_type_4511_);
lean_dec_ref(v_type_4509_);
if (v___x_4512_ == 0)
{
lean_dec_ref(v_lctx_4510_);
lean_dec_ref(v_lctx_4508_);
lean_dec(v_mv_u2082_4495_);
lean_dec(v_mv_u2081_4494_);
goto v___jp_4501_;
}
else
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc_ref(v_lctx_4510_);
lean_inc_ref(v_lctx_4508_);
v___x_4514_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4508_, v_lctx_4510_, v___x_4513_);
if (v___x_4514_ == 0)
{
uint8_t v___x_4515_; 
v___x_4515_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4510_, v_lctx_4508_, v___x_4513_);
if (v___x_4515_ == 0)
{
lean_dec(v_mv_u2082_4495_);
lean_dec(v_mv_u2081_4494_);
goto v___jp_4501_;
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4527_; 
v___x_4516_ = l_Lean_Expr_mvar___override(v_mv_u2082_4495_);
v___x_4517_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4494_, v___x_4516_, v___y_4497_);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v___x_4517_, 0);
lean_dec(v_unused_4528_);
v___x_4519_ = v___x_4517_;
v_isShared_4520_ = v_isSharedCheck_4527_;
goto v_resetjp_4518_;
}
else
{
lean_dec(v___x_4517_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4527_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4521_ = lean_box(v___x_4514_);
v___x_4522_ = lean_box(v___x_4512_);
v___x_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4521_);
lean_ctor_set(v___x_4523_, 1, v___x_4522_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v___x_4523_);
v___x_4525_ = v___x_4519_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_lctx_4510_);
lean_dec_ref(v_lctx_4508_);
v___x_4529_ = l_Lean_Expr_mvar___override(v_mv_u2081_4494_);
v___x_4530_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4495_, v___x_4529_, v___y_4497_);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4541_ == 0)
{
lean_object* v_unused_4542_; 
v_unused_4542_ = lean_ctor_get(v___x_4530_, 0);
lean_dec(v_unused_4542_);
v___x_4532_ = v___x_4530_;
v_isShared_4533_ = v_isSharedCheck_4541_;
goto v_resetjp_4531_;
}
else
{
lean_dec(v___x_4530_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4541_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4539_; 
v___x_4534_ = 0;
v___x_4535_ = lean_box(v___x_4512_);
v___x_4536_ = lean_box(v___x_4534_);
v___x_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4535_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4537_);
v___x_4539_ = v___x_4532_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4537_);
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
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v_a_4505_);
lean_dec(v_mv_u2082_4495_);
lean_dec(v_mv_u2081_4494_);
v_a_4543_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4506_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4506_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_mv_u2082_4495_);
lean_dec(v_mv_u2081_4494_);
v_a_4551_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4504_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4504_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
v___jp_4501_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4559_, lean_object* v_mv_u2082_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4559_, v_mv_u2082_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4567_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4581_, lean_object* v_removed_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v___y_4592_; uint8_t v___x_4615_; 
v___x_4615_ = lean_nat_dec_lt(v_a_4584_, v_upperBound_4581_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; 
lean_dec(v_a_4584_);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_b_4585_);
return v___x_4616_;
}
else
{
uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4617_ = 0;
v___x_4618_ = lean_box(v___x_4617_);
v___x_4619_ = lean_array_get_borrowed(v___x_4618_, v_removed_4582_, v_a_4584_);
v___x_4620_ = lean_unbox(v___x_4619_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___f_4624_; 
v___x_4621_ = lean_array_fget_borrowed(v_a_4583_, v_a_4584_);
lean_inc(v___x_4621_);
v___x_4622_ = lean_array_push(v_b_4585_, v___x_4621_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
v___f_4624_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4624_, 0, v___x_4623_);
v___y_4592_ = v___f_4624_;
goto v___jp_4591_;
}
else
{
lean_object* v___x_4625_; lean_object* v___f_4626_; 
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_b_4585_);
v___f_4626_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4626_, 0, v___x_4625_);
v___y_4592_ = v___f_4626_;
goto v___jp_4591_;
}
}
v___jp_4591_:
{
lean_object* v___x_4593_; 
lean_inc(v___y_4589_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4587_);
lean_inc_ref(v___y_4586_);
v___x_4593_ = lean_apply_5(v___y_4592_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, lean_box(0));
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4606_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4596_ = v___x_4593_;
v_isShared_4597_ = v_isSharedCheck_4606_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4593_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4606_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
if (lean_obj_tag(v_a_4594_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; 
lean_dec(v_a_4584_);
v_a_4598_ = lean_ctor_get(v_a_4594_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v_a_4594_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v_a_4598_);
v___x_4600_ = v___x_4596_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
lean_del_object(v___x_4596_);
v_a_4602_ = lean_ctor_get(v_a_4594_, 0);
lean_inc(v_a_4602_);
lean_dec_ref(v_a_4594_);
v___x_4603_ = lean_unsigned_to_nat(1u);
v___x_4604_ = lean_nat_add(v_a_4584_, v___x_4603_);
lean_dec(v_a_4584_);
v_a_4584_ = v___x_4604_;
v_b_4585_ = v_a_4602_;
goto _start;
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec(v_a_4584_);
v_a_4607_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4593_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4593_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4627_, lean_object* v_removed_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_b_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4627_, v_removed_4628_, v_a_4629_, v_a_4630_, v_b_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec_ref(v_a_4629_);
lean_dec_ref(v_removed_4628_);
lean_dec(v_upperBound_4627_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4638_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4652_, lean_object* v___x_4653_, lean_object* v___x_4654_, lean_object* v___x_4655_, lean_object* v_a_4656_, uint8_t v___x_4657_, lean_object* v_snd_4658_, lean_object* v_fst_4659_, lean_object* v_next_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_apply_7(v_f_4652_, v___x_4653_, v___x_4654_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, lean_box(0));
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4702_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4669_ = v___x_4666_;
v_isShared_4670_ = v_isSharedCheck_4702_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4702_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v_fst_4671_; lean_object* v_snd_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4701_; 
v_fst_4671_ = lean_ctor_get(v_a_4667_, 0);
v_snd_4672_ = lean_ctor_get(v_a_4667_, 1);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_a_4667_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4674_ = v_a_4667_;
v_isShared_4675_ = v_isSharedCheck_4701_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_snd_4672_);
lean_inc(v_fst_4671_);
lean_dec(v_a_4667_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4701_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_removed_4677_; lean_object* v_numRemoved_4678_; uint8_t v___x_4697_; 
v___x_4697_ = lean_unbox(v_fst_4671_);
lean_dec(v_fst_4671_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4698_ = lean_nat_add(v_snd_4658_, v___x_4655_);
lean_dec(v_snd_4658_);
v___x_4699_ = lean_box(v___x_4657_);
v___x_4700_ = lean_array_set(v_fst_4659_, v_next_4660_, v___x_4699_);
v_removed_4677_ = v___x_4700_;
v_numRemoved_4678_ = v___x_4698_;
goto v___jp_4676_;
}
else
{
v_removed_4677_ = v_fst_4659_;
v_numRemoved_4678_ = v_snd_4658_;
goto v___jp_4676_;
}
v___jp_4676_:
{
uint8_t v___x_4679_; 
v___x_4679_ = lean_unbox(v_snd_4672_);
lean_dec(v_snd_4672_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4680_ = lean_nat_add(v_numRemoved_4678_, v___x_4655_);
lean_dec(v_numRemoved_4678_);
v___x_4681_ = lean_box(v___x_4657_);
v___x_4682_ = lean_array_set(v_removed_4677_, v_a_4656_, v___x_4681_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 1, v___x_4680_);
lean_ctor_set(v___x_4674_, 0, v___x_4682_);
v___x_4684_ = v___x_4674_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v___x_4680_);
v___x_4684_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v___x_4685_);
v___x_4687_ = v___x_4669_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
else
{
lean_object* v___x_4691_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 1, v_numRemoved_4678_);
lean_ctor_set(v___x_4674_, 0, v_removed_4677_);
v___x_4691_ = v___x_4674_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_removed_4677_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_numRemoved_4678_);
v___x_4691_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v___x_4692_);
v___x_4694_ = v___x_4669_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_fst_4659_);
lean_dec(v_snd_4658_);
v_a_4703_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4666_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4666_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4711_, lean_object* v___x_4712_, lean_object* v___x_4713_, lean_object* v___x_4714_, lean_object* v_a_4715_, lean_object* v___x_4716_, lean_object* v_snd_4717_, lean_object* v_fst_4718_, lean_object* v_next_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
uint8_t v___x_4750__boxed_4725_; lean_object* v_res_4726_; 
v___x_4750__boxed_4725_ = lean_unbox(v___x_4716_);
v_res_4726_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4711_, v___x_4712_, v___x_4713_, v___x_4714_, v_a_4715_, v___x_4750__boxed_4725_, v_snd_4717_, v_fst_4718_, v_next_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v_next_4719_);
lean_dec(v_a_4715_);
lean_dec(v___x_4714_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4727_, lean_object* v_a_4728_, lean_object* v_next_4729_, lean_object* v_f_4730_, lean_object* v_a_4731_, lean_object* v_b_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
uint8_t v___x_4738_; 
v___x_4738_ = lean_nat_dec_lt(v_a_4731_, v_upperBound_4727_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
lean_dec(v_a_4731_);
lean_dec_ref(v_f_4730_);
lean_dec(v_next_4729_);
v___x_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4739_, 0, v_b_4732_);
return v___x_4739_;
}
else
{
lean_object* v_fst_4740_; lean_object* v_snd_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4788_; 
v_fst_4740_ = lean_ctor_get(v_b_4732_, 0);
v_snd_4741_ = lean_ctor_get(v_b_4732_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_b_4732_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4743_ = v_b_4732_;
v_isShared_4744_ = v_isSharedCheck_4788_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_snd_4741_);
lean_inc(v_fst_4740_);
lean_dec(v_b_4732_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4788_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___y_4747_; uint8_t v___y_4770_; uint8_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4745_ = lean_unsigned_to_nat(1u);
v___x_4780_ = 0;
v___x_4781_ = lean_box(v___x_4780_);
v___x_4782_ = lean_array_get_borrowed(v___x_4781_, v_fst_4740_, v_next_4729_);
v___x_4783_ = lean_unbox(v___x_4782_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4784_ = lean_box(v___x_4780_);
v___x_4785_ = lean_array_get_borrowed(v___x_4784_, v_fst_4740_, v_a_4731_);
v___x_4786_ = lean_unbox(v___x_4785_);
v___y_4770_ = v___x_4786_;
goto v___jp_4769_;
}
else
{
uint8_t v___x_4787_; 
v___x_4787_ = lean_unbox(v___x_4782_);
v___y_4770_ = v___x_4787_;
goto v___jp_4769_;
}
v___jp_4746_:
{
lean_object* v___x_4748_; 
lean_inc(v___y_4736_);
lean_inc_ref(v___y_4735_);
lean_inc(v___y_4734_);
lean_inc_ref(v___y_4733_);
v___x_4748_ = lean_apply_5(v___y_4747_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, lean_box(0));
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4760_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4760_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4760_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
if (lean_obj_tag(v_a_4749_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; 
lean_dec(v_a_4731_);
lean_dec_ref(v_f_4730_);
lean_dec(v_next_4729_);
v_a_4753_ = lean_ctor_get(v_a_4749_, 0);
lean_inc(v_a_4753_);
lean_dec_ref(v_a_4749_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v_a_4753_);
v___x_4755_ = v___x_4751_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4758_; 
lean_del_object(v___x_4751_);
v_a_4757_ = lean_ctor_get(v_a_4749_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v_a_4749_);
v___x_4758_ = lean_nat_add(v_a_4731_, v___x_4745_);
lean_dec(v_a_4731_);
v_a_4731_ = v___x_4758_;
v_b_4732_ = v_a_4757_;
goto _start;
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_a_4731_);
lean_dec_ref(v_f_4730_);
lean_dec(v_next_4729_);
v_a_4761_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4748_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4748_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
v___jp_4769_:
{
if (v___y_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___f_4774_; 
lean_del_object(v___x_4743_);
v___x_4771_ = lean_array_fget_borrowed(v_a_4728_, v_next_4729_);
v___x_4772_ = lean_array_fget_borrowed(v_a_4728_, v_a_4731_);
v___x_4773_ = lean_box(v___x_4738_);
lean_inc(v_next_4729_);
lean_inc(v_a_4731_);
lean_inc(v___x_4772_);
lean_inc(v___x_4771_);
lean_inc_ref(v_f_4730_);
v___f_4774_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4774_, 0, v_f_4730_);
lean_closure_set(v___f_4774_, 1, v___x_4771_);
lean_closure_set(v___f_4774_, 2, v___x_4772_);
lean_closure_set(v___f_4774_, 3, v___x_4745_);
lean_closure_set(v___f_4774_, 4, v_a_4731_);
lean_closure_set(v___f_4774_, 5, v___x_4773_);
lean_closure_set(v___f_4774_, 6, v_snd_4741_);
lean_closure_set(v___f_4774_, 7, v_fst_4740_);
lean_closure_set(v___f_4774_, 8, v_next_4729_);
v___y_4747_ = v___f_4774_;
goto v___jp_4746_;
}
else
{
lean_object* v___x_4776_; 
if (v_isShared_4744_ == 0)
{
v___x_4776_ = v___x_4743_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_fst_4740_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_snd_4741_);
v___x_4776_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
lean_object* v___x_4777_; lean_object* v___f_4778_; 
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
v___f_4778_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4778_, 0, v___x_4777_);
v___y_4747_ = v___f_4778_;
goto v___jp_4746_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4789_, lean_object* v_a_4790_, lean_object* v_next_4791_, lean_object* v_f_4792_, lean_object* v_a_4793_, lean_object* v_b_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4789_, v_a_4790_, v_next_4791_, v_f_4792_, v_a_4793_, v_b_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
lean_dec_ref(v_a_4790_);
lean_dec(v_upperBound_4789_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4801_, lean_object* v___x_4802_, lean_object* v_a_4803_, lean_object* v_f_4804_, lean_object* v_a_4805_, lean_object* v_b_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
uint8_t v___x_4812_; 
v___x_4812_ = lean_nat_dec_lt(v_a_4805_, v_upperBound_4801_);
if (v___x_4812_ == 0)
{
lean_object* v___x_4813_; 
lean_dec(v_a_4805_);
lean_dec_ref(v_f_4804_);
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_b_4806_);
return v___x_4813_;
}
else
{
lean_object* v_fst_4814_; lean_object* v_snd_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4836_; 
v_fst_4814_ = lean_ctor_get(v_b_4806_, 0);
v_snd_4815_ = lean_ctor_get(v_b_4806_, 1);
v_isSharedCheck_4836_ = !lean_is_exclusive(v_b_4806_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4817_ = v_b_4806_;
v_isShared_4818_ = v_isSharedCheck_4836_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_snd_4815_);
lean_inc(v_fst_4814_);
lean_dec(v_b_4806_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4836_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
v___x_4819_ = lean_unsigned_to_nat(1u);
v___x_4820_ = lean_nat_add(v_a_4805_, v___x_4819_);
if (v_isShared_4818_ == 0)
{
v___x_4822_ = v___x_4817_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_fst_4814_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_snd_4815_);
v___x_4822_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
lean_object* v___x_4823_; 
lean_inc(v___x_4820_);
lean_inc_ref(v_f_4804_);
v___x_4823_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4802_, v_a_4803_, v_a_4805_, v_f_4804_, v___x_4820_, v___x_4822_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v_fst_4825_; lean_object* v_snd_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4834_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref(v___x_4823_);
v_fst_4825_ = lean_ctor_get(v_a_4824_, 0);
v_snd_4826_ = lean_ctor_get(v_a_4824_, 1);
v_isSharedCheck_4834_ = !lean_is_exclusive(v_a_4824_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4828_ = v_a_4824_;
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_snd_4826_);
lean_inc(v_fst_4825_);
lean_dec(v_a_4824_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_fst_4825_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_snd_4826_);
v___x_4831_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
v_a_4805_ = v___x_4820_;
v_b_4806_ = v___x_4831_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4820_);
lean_dec_ref(v_f_4804_);
return v___x_4823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4837_, lean_object* v___x_4838_, lean_object* v_a_4839_, lean_object* v_f_4840_, lean_object* v_a_4841_, lean_object* v_b_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4837_, v___x_4838_, v_a_4839_, v_f_4840_, v_a_4841_, v_b_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec_ref(v_a_4839_);
lean_dec(v___x_4838_);
lean_dec(v_upperBound_4837_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4849_, lean_object* v_f_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v___x_4856_; uint8_t v___x_4857_; lean_object* v___x_4858_; lean_object* v_removed_4859_; lean_object* v_numRemoved_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4856_ = lean_array_get_size(v_a_4849_);
v___x_4857_ = 0;
v___x_4858_ = lean_box(v___x_4857_);
v_removed_4859_ = lean_mk_array(v___x_4856_, v___x_4858_);
v_numRemoved_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4861_, 0, v_removed_4859_);
lean_ctor_set(v___x_4861_, 1, v_numRemoved_4860_);
v___x_4862_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4856_, v___x_4856_, v_a_4849_, v_f_4850_, v_numRemoved_4860_, v___x_4861_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v_fst_4864_; lean_object* v_snd_4865_; lean_object* v_a_x27_4866_; lean_object* v___x_4867_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref(v___x_4862_);
v_fst_4864_ = lean_ctor_get(v_a_4863_, 0);
lean_inc(v_fst_4864_);
v_snd_4865_ = lean_ctor_get(v_a_4863_, 1);
lean_inc(v_snd_4865_);
lean_dec(v_a_4863_);
v_a_x27_4866_ = lean_mk_empty_array_with_capacity(v_snd_4865_);
lean_dec(v_snd_4865_);
v___x_4867_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4856_, v_fst_4864_, v_a_4849_, v_numRemoved_4860_, v_a_x27_4866_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
lean_dec(v_fst_4864_);
return v___x_4867_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4862_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4862_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4876_, lean_object* v_f_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4876_, v_f_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec_ref(v_a_4876_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_){
_start:
{
lean_object* v___f_4891_; lean_object* v___x_4892_; 
v___f_4891_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4892_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4885_, v___f_4891_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec_ref(v_mvars_4893_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4900_, lean_object* v_val_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4900_, v_val_4901_, v___y_4903_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4908_, lean_object* v_val_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4908_, v_val_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4916_, lean_object* v_a_4917_, lean_object* v_f_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4917_, v_f_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4925_, lean_object* v_a_4926_, lean_object* v_f_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4925_, v_a_4926_, v_f_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec_ref(v_a_4926_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4934_, lean_object* v_x_4935_, lean_object* v_x_4936_, lean_object* v_x_4937_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4935_, v_x_4936_, v_x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4939_, lean_object* v_00_u03b1_4940_, lean_object* v_a_4941_, lean_object* v_next_4942_, lean_object* v_f_4943_, lean_object* v_inst_4944_, lean_object* v_R_4945_, lean_object* v_a_4946_, lean_object* v_b_4947_, lean_object* v_c_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4939_, v_a_4941_, v_next_4942_, v_f_4943_, v_a_4946_, v_b_4947_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4955_, lean_object* v_00_u03b1_4956_, lean_object* v_a_4957_, lean_object* v_next_4958_, lean_object* v_f_4959_, lean_object* v_inst_4960_, lean_object* v_R_4961_, lean_object* v_a_4962_, lean_object* v_b_4963_, lean_object* v_c_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4955_, v_00_u03b1_4956_, v_a_4957_, v_next_4958_, v_f_4959_, v_inst_4960_, v_R_4961_, v_a_4962_, v_b_4963_, v_c_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec_ref(v_a_4957_);
lean_dec(v_upperBound_4955_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4971_, lean_object* v_upperBound_4972_, lean_object* v_removed_4973_, lean_object* v_a_4974_, lean_object* v_inst_4975_, lean_object* v_R_4976_, lean_object* v_a_4977_, lean_object* v_b_4978_, lean_object* v_c_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4972_, v_removed_4973_, v_a_4974_, v_a_4977_, v_b_4978_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4986_, lean_object* v_upperBound_4987_, lean_object* v_removed_4988_, lean_object* v_a_4989_, lean_object* v_inst_4990_, lean_object* v_R_4991_, lean_object* v_a_4992_, lean_object* v_b_4993_, lean_object* v_c_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4986_, v_upperBound_4987_, v_removed_4988_, v_a_4989_, v_inst_4990_, v_R_4991_, v_a_4992_, v_b_4993_, v_c_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec_ref(v_a_4989_);
lean_dec_ref(v_removed_4988_);
lean_dec(v_upperBound_4987_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_5001_, lean_object* v___x_5002_, lean_object* v_00_u03b1_5003_, lean_object* v_a_5004_, lean_object* v_f_5005_, lean_object* v_inst_5006_, lean_object* v_R_5007_, lean_object* v_a_5008_, lean_object* v_b_5009_, lean_object* v_c_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_5001_, v___x_5002_, v_a_5004_, v_f_5005_, v_a_5008_, v_b_5009_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_5017_, lean_object* v___x_5018_, lean_object* v_00_u03b1_5019_, lean_object* v_a_5020_, lean_object* v_f_5021_, lean_object* v_inst_5022_, lean_object* v_R_5023_, lean_object* v_a_5024_, lean_object* v_b_5025_, lean_object* v_c_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_WellFounded_opaqueFix_u2083___at___00Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_5017_, v___x_5018_, v_00_u03b1_5019_, v_a_5020_, v_f_5021_, v_inst_5022_, v_R_5023_, v_a_5024_, v_b_5025_, v_c_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec_ref(v_a_5020_);
lean_dec(v___x_5018_);
lean_dec(v_upperBound_5017_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5033_, lean_object* v_x_5034_, size_t v_x_5035_, size_t v_x_5036_, lean_object* v_x_5037_, lean_object* v_x_5038_){
_start:
{
lean_object* v___x_5039_; 
v___x_5039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_5034_, v_x_5035_, v_x_5036_, v_x_5037_, v_x_5038_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5040_, lean_object* v_x_5041_, lean_object* v_x_5042_, lean_object* v_x_5043_, lean_object* v_x_5044_, lean_object* v_x_5045_){
_start:
{
size_t v_x_5210__boxed_5046_; size_t v_x_5211__boxed_5047_; lean_object* v_res_5048_; 
v_x_5210__boxed_5046_ = lean_unbox_usize(v_x_5042_);
lean_dec(v_x_5042_);
v_x_5211__boxed_5047_ = lean_unbox_usize(v_x_5043_);
lean_dec(v_x_5043_);
v_res_5048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_5040_, v_x_5041_, v_x_5210__boxed_5046_, v_x_5211__boxed_5047_, v_x_5044_, v_x_5045_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_5049_, lean_object* v_n_5050_, lean_object* v_k_5051_, lean_object* v_v_5052_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_5050_, v_k_5051_, v_v_5052_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_5054_, size_t v_depth_5055_, lean_object* v_keys_5056_, lean_object* v_vals_5057_, lean_object* v_heq_5058_, lean_object* v_i_5059_, lean_object* v_entries_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_5055_, v_keys_5056_, v_vals_5057_, v_i_5059_, v_entries_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_5062_, lean_object* v_depth_5063_, lean_object* v_keys_5064_, lean_object* v_vals_5065_, lean_object* v_heq_5066_, lean_object* v_i_5067_, lean_object* v_entries_5068_){
_start:
{
size_t v_depth_boxed_5069_; lean_object* v_res_5070_; 
v_depth_boxed_5069_ = lean_unbox_usize(v_depth_5063_);
lean_dec(v_depth_5063_);
v_res_5070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_5062_, v_depth_boxed_5069_, v_keys_5064_, v_vals_5065_, v_heq_5066_, v_i_5067_, v_entries_5068_);
lean_dec_ref(v_vals_5065_);
lean_dec_ref(v_keys_5064_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_5071_, lean_object* v_x_5072_, lean_object* v_x_5073_, lean_object* v_x_5074_, lean_object* v_x_5075_){
_start:
{
lean_object* v___x_5076_; 
v___x_5076_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_5072_, v_x_5073_, v_x_5074_, v_x_5075_);
return v___x_5076_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5079_ = l_Lean_stringToMessageData(v___x_5078_);
return v___x_5079_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5082_ = l_Lean_stringToMessageData(v___x_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5083_, lean_object* v_as_5084_, size_t v_sz_5085_, size_t v_i_5086_, lean_object* v_b_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v_a_5094_; uint8_t v___x_5098_; 
v___x_5098_ = lean_usize_dec_lt(v_i_5086_, v_sz_5085_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
v___x_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5099_, 0, v_b_5087_);
return v___x_5099_;
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5101_; 
v_a_5100_ = lean_array_uget_borrowed(v_as_5084_, v_i_5086_);
lean_inc(v_a_5100_);
v___x_5101_ = l_Lean_MVarId_getType(v_a_5100_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref(v___x_5101_);
if (lean_obj_tag(v_a_5102_) == 10)
{
lean_object* v_expr_5120_; 
v_expr_5120_ = lean_ctor_get(v_a_5102_, 1);
if (lean_obj_tag(v_expr_5120_) == 5)
{
lean_object* v_arg_5121_; lean_object* v___x_5122_; 
lean_inc_ref(v_expr_5120_);
lean_dec_ref(v_a_5102_);
v_arg_5121_ = lean_ctor_get(v_expr_5120_, 1);
lean_inc_ref(v_arg_5121_);
lean_dec_ref(v_expr_5120_);
lean_inc_ref(v_arg_5121_);
v___x_5122_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5083_, v_arg_5121_);
if (lean_obj_tag(v___x_5122_) == 1)
{
lean_object* v_val_5123_; lean_object* v_fst_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; 
lean_dec_ref(v_arg_5121_);
v_val_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_val_5123_);
lean_dec_ref(v___x_5122_);
v_fst_5124_ = lean_ctor_get(v_val_5123_, 0);
lean_inc(v_fst_5124_);
lean_dec(v_val_5123_);
v___x_5125_ = lean_array_get_size(v_b_5087_);
v___x_5126_ = lean_nat_dec_lt(v_fst_5124_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_dec(v_fst_5124_);
v_a_5094_ = v_b_5087_;
goto v___jp_5093_;
}
else
{
lean_object* v_v_5127_; lean_object* v___x_5128_; lean_object* v_xs_x27_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v_v_5127_ = lean_array_fget(v_b_5087_, v_fst_5124_);
v___x_5128_ = lean_box(0);
v_xs_x27_5129_ = lean_array_fset(v_b_5087_, v_fst_5124_, v___x_5128_);
lean_inc(v_a_5100_);
v___x_5130_ = lean_array_push(v_v_5127_, v_a_5100_);
v___x_5131_ = lean_array_fset(v_xs_x27_5129_, v_fst_5124_, v___x_5130_);
lean_dec(v_fst_5124_);
v_a_5094_ = v___x_5131_;
goto v___jp_5093_;
}
}
else
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
lean_dec(v___x_5122_);
v___x_5132_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5133_ = l_Lean_indentExpr(v_arg_5121_);
v___x_5134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5132_);
lean_ctor_set(v___x_5134_, 1, v___x_5133_);
v___x_5135_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5134_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_dec_ref(v___x_5135_);
v_a_5094_ = v_b_5087_;
goto v___jp_5093_;
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_dec_ref(v_b_5087_);
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5135_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5135_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
}
else
{
v___y_5104_ = v___y_5088_;
v___y_5105_ = v___y_5089_;
v___y_5106_ = v___y_5090_;
v___y_5107_ = v___y_5091_;
goto v___jp_5103_;
}
}
else
{
v___y_5104_ = v___y_5088_;
v___y_5105_ = v___y_5089_;
v___y_5106_ = v___y_5090_;
v___y_5107_ = v___y_5091_;
goto v___jp_5103_;
}
v___jp_5103_:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5109_ = l_Lean_indentExpr(v_a_5102_);
v___x_5110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5108_);
lean_ctor_set(v___x_5110_, 1, v___x_5109_);
v___x_5111_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5110_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_dec_ref(v___x_5111_);
v_a_5094_ = v_b_5087_;
goto v___jp_5093_;
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_dec_ref(v_b_5087_);
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5151_; 
lean_dec_ref(v_b_5087_);
v_a_5144_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5146_ = v___x_5101_;
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5101_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5147_ == 0)
{
v___x_5149_ = v___x_5146_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
}
v___jp_5093_:
{
size_t v___x_5095_; size_t v___x_5096_; 
v___x_5095_ = ((size_t)1ULL);
v___x_5096_ = lean_usize_add(v_i_5086_, v___x_5095_);
v_i_5086_ = v___x_5096_;
v_b_5087_ = v_a_5094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5152_, lean_object* v_as_5153_, lean_object* v_sz_5154_, lean_object* v_i_5155_, lean_object* v_b_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
size_t v_sz_boxed_5162_; size_t v_i_boxed_5163_; lean_object* v_res_5164_; 
v_sz_boxed_5162_ = lean_unbox_usize(v_sz_5154_);
lean_dec(v_sz_5154_);
v_i_boxed_5163_ = lean_unbox_usize(v_i_5155_);
lean_dec(v_i_5155_);
v_res_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5152_, v_as_5153_, v_sz_boxed_5162_, v_i_boxed_5163_, v_b_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec_ref(v_as_5153_);
lean_dec_ref(v_argsPacker_5152_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5165_, lean_object* v_numFuncs_5166_, lean_object* v_goals_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v___x_5173_; lean_object* v_r_5174_; size_t v_sz_5175_; size_t v___x_5176_; lean_object* v___x_5177_; 
v___x_5173_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5174_ = lean_mk_array(v_numFuncs_5166_, v___x_5173_);
v_sz_5175_ = lean_array_size(v_goals_5167_);
v___x_5176_ = ((size_t)0ULL);
v___x_5177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5165_, v_goals_5167_, v_sz_5175_, v___x_5176_, v_r_5174_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5178_, lean_object* v_numFuncs_5179_, lean_object* v_goals_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5178_, v_numFuncs_5179_, v_goals_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
lean_dec_ref(v_a_5181_);
lean_dec_ref(v_goals_5180_);
lean_dec_ref(v_argsPacker_5178_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v___x_5190_; lean_object* v_infoState_5191_; uint8_t v_enabled_5192_; 
v___x_5190_ = lean_st_ref_get(v___y_5188_);
v_infoState_5191_ = lean_ctor_get(v___x_5190_, 7);
lean_inc_ref(v_infoState_5191_);
lean_dec(v___x_5190_);
v_enabled_5192_ = lean_ctor_get_uint8(v_infoState_5191_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5191_);
if (v_enabled_5192_ == 0)
{
lean_object* v___x_5193_; lean_object* v___x_5194_; 
lean_dec_ref(v_t_5187_);
v___x_5193_ = lean_box(0);
v___x_5194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
return v___x_5194_;
}
else
{
lean_object* v___x_5195_; lean_object* v_infoState_5196_; lean_object* v_env_5197_; lean_object* v_nextMacroScope_5198_; lean_object* v_ngen_5199_; lean_object* v_auxDeclNGen_5200_; lean_object* v_traceState_5201_; lean_object* v_cache_5202_; lean_object* v_messages_5203_; lean_object* v_snapshotTasks_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5226_; 
v___x_5195_ = lean_st_ref_take(v___y_5188_);
v_infoState_5196_ = lean_ctor_get(v___x_5195_, 7);
v_env_5197_ = lean_ctor_get(v___x_5195_, 0);
v_nextMacroScope_5198_ = lean_ctor_get(v___x_5195_, 1);
v_ngen_5199_ = lean_ctor_get(v___x_5195_, 2);
v_auxDeclNGen_5200_ = lean_ctor_get(v___x_5195_, 3);
v_traceState_5201_ = lean_ctor_get(v___x_5195_, 4);
v_cache_5202_ = lean_ctor_get(v___x_5195_, 5);
v_messages_5203_ = lean_ctor_get(v___x_5195_, 6);
v_snapshotTasks_5204_ = lean_ctor_get(v___x_5195_, 8);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5206_ = v___x_5195_;
v_isShared_5207_ = v_isSharedCheck_5226_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_snapshotTasks_5204_);
lean_inc(v_infoState_5196_);
lean_inc(v_messages_5203_);
lean_inc(v_cache_5202_);
lean_inc(v_traceState_5201_);
lean_inc(v_auxDeclNGen_5200_);
lean_inc(v_ngen_5199_);
lean_inc(v_nextMacroScope_5198_);
lean_inc(v_env_5197_);
lean_dec(v___x_5195_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5226_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
uint8_t v_enabled_5208_; lean_object* v_assignment_5209_; lean_object* v_lazyAssignment_5210_; lean_object* v_trees_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5225_; 
v_enabled_5208_ = lean_ctor_get_uint8(v_infoState_5196_, sizeof(void*)*3);
v_assignment_5209_ = lean_ctor_get(v_infoState_5196_, 0);
v_lazyAssignment_5210_ = lean_ctor_get(v_infoState_5196_, 1);
v_trees_5211_ = lean_ctor_get(v_infoState_5196_, 2);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_infoState_5196_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5213_ = v_infoState_5196_;
v_isShared_5214_ = v_isSharedCheck_5225_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_trees_5211_);
lean_inc(v_lazyAssignment_5210_);
lean_inc(v_assignment_5209_);
lean_dec(v_infoState_5196_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5225_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5215_ = l_Lean_PersistentArray_push___redArg(v_trees_5211_, v_t_5187_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 2, v___x_5215_);
v___x_5217_ = v___x_5213_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_assignment_5209_);
lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_lazyAssignment_5210_);
lean_ctor_set(v_reuseFailAlloc_5224_, 2, v___x_5215_);
lean_ctor_set_uint8(v_reuseFailAlloc_5224_, sizeof(void*)*3, v_enabled_5208_);
v___x_5217_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5219_; 
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 7, v___x_5217_);
v___x_5219_ = v___x_5206_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_env_5197_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_nextMacroScope_5198_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_ngen_5199_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_auxDeclNGen_5200_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v_traceState_5201_);
lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_cache_5202_);
lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_messages_5203_);
lean_ctor_set(v_reuseFailAlloc_5223_, 7, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_snapshotTasks_5204_);
v___x_5219_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5220_ = lean_st_ref_set(v___y_5188_, v___x_5219_);
v___x_5221_ = lean_box(0);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
return v___x_5222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5227_, v___y_5228_);
lean_dec(v___y_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5231_, v___y_5237_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5249_, lean_object* v___y_5250_){
_start:
{
uint8_t v___x_5252_; 
v___x_5252_ = l_Lean_Expr_hasMVar(v_e_5249_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v_e_5249_);
return v___x_5253_;
}
else
{
lean_object* v___x_5254_; lean_object* v_mctx_5255_; lean_object* v___x_5256_; lean_object* v_fst_5257_; lean_object* v_snd_5258_; lean_object* v___x_5259_; lean_object* v_cache_5260_; lean_object* v_zetaDeltaFVarIds_5261_; lean_object* v_postponed_5262_; lean_object* v_diag_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5272_; 
v___x_5254_ = lean_st_ref_get(v___y_5250_);
v_mctx_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc_ref(v_mctx_5255_);
lean_dec(v___x_5254_);
v___x_5256_ = l_Lean_instantiateMVarsCore(v_mctx_5255_, v_e_5249_);
v_fst_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_fst_5257_);
v_snd_5258_ = lean_ctor_get(v___x_5256_, 1);
lean_inc(v_snd_5258_);
lean_dec_ref(v___x_5256_);
v___x_5259_ = lean_st_ref_take(v___y_5250_);
v_cache_5260_ = lean_ctor_get(v___x_5259_, 1);
v_zetaDeltaFVarIds_5261_ = lean_ctor_get(v___x_5259_, 2);
v_postponed_5262_ = lean_ctor_get(v___x_5259_, 3);
v_diag_5263_ = lean_ctor_get(v___x_5259_, 4);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5259_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; 
v_unused_5273_ = lean_ctor_get(v___x_5259_, 0);
lean_dec(v_unused_5273_);
v___x_5265_ = v___x_5259_;
v_isShared_5266_ = v_isSharedCheck_5272_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_diag_5263_);
lean_inc(v_postponed_5262_);
lean_inc(v_zetaDeltaFVarIds_5261_);
lean_inc(v_cache_5260_);
lean_dec(v___x_5259_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5272_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
lean_ctor_set(v___x_5265_, 0, v_snd_5258_);
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_snd_5258_);
lean_ctor_set(v_reuseFailAlloc_5271_, 1, v_cache_5260_);
lean_ctor_set(v_reuseFailAlloc_5271_, 2, v_zetaDeltaFVarIds_5261_);
lean_ctor_set(v_reuseFailAlloc_5271_, 3, v_postponed_5262_);
lean_ctor_set(v_reuseFailAlloc_5271_, 4, v_diag_5263_);
v___x_5268_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5269_ = lean_st_ref_set(v___y_5250_, v___x_5268_);
v___x_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5270_, 0, v_fst_5257_);
return v___x_5270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5274_, v___y_5275_);
lean_dec(v___y_5275_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5278_, v___y_5280_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5292_, size_t v_i_5293_, size_t v_stop_5294_, lean_object* v_b_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
uint8_t v___x_5303_; 
v___x_5303_ = lean_usize_dec_eq(v_i_5293_, v_stop_5294_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5304_ = lean_array_uget_borrowed(v_as_5292_, v_i_5293_);
lean_inc(v___x_5304_);
v___x_5305_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5304_);
v___x_5306_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5305_, v___y_5301_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; size_t v___x_5308_; size_t v___x_5309_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = ((size_t)1ULL);
v___x_5309_ = lean_usize_add(v_i_5293_, v___x_5308_);
v_i_5293_ = v___x_5309_;
v_b_5295_ = v_a_5307_;
goto _start;
}
else
{
return v___x_5306_;
}
}
else
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v_b_5295_);
return v___x_5311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5312_, lean_object* v_i_5313_, lean_object* v_stop_5314_, lean_object* v_b_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
size_t v_i_boxed_5323_; size_t v_stop_boxed_5324_; lean_object* v_res_5325_; 
v_i_boxed_5323_ = lean_unbox_usize(v_i_5313_);
lean_dec(v_i_5313_);
v_stop_boxed_5324_ = lean_unbox_usize(v_stop_5314_);
lean_dec(v_stop_5314_);
v_res_5325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5312_, v_i_boxed_5323_, v_stop_boxed_5324_, v_b_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec_ref(v_as_5312_);
return v_res_5325_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5326_ = lean_unsigned_to_nat(32u);
v___x_5327_ = lean_mk_empty_array_with_capacity(v___x_5326_);
v___x_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5327_);
return v___x_5328_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5329_ = ((size_t)5ULL);
v___x_5330_ = lean_unsigned_to_nat(0u);
v___x_5331_ = lean_unsigned_to_nat(32u);
v___x_5332_ = lean_mk_empty_array_with_capacity(v___x_5331_);
v___x_5333_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5334_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5334_, 0, v___x_5333_);
lean_ctor_set(v___x_5334_, 1, v___x_5332_);
lean_ctor_set(v___x_5334_, 2, v___x_5330_);
lean_ctor_set(v___x_5334_, 3, v___x_5330_);
lean_ctor_set_usize(v___x_5334_, 4, v___x_5329_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5335_){
_start:
{
lean_object* v___x_5337_; lean_object* v_infoState_5338_; lean_object* v_trees_5339_; lean_object* v___x_5340_; lean_object* v_infoState_5341_; lean_object* v_env_5342_; lean_object* v_nextMacroScope_5343_; lean_object* v_ngen_5344_; lean_object* v_auxDeclNGen_5345_; lean_object* v_traceState_5346_; lean_object* v_cache_5347_; lean_object* v_messages_5348_; lean_object* v_snapshotTasks_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5370_; 
v___x_5337_ = lean_st_ref_get(v___y_5335_);
v_infoState_5338_ = lean_ctor_get(v___x_5337_, 7);
lean_inc_ref(v_infoState_5338_);
lean_dec(v___x_5337_);
v_trees_5339_ = lean_ctor_get(v_infoState_5338_, 2);
lean_inc_ref(v_trees_5339_);
lean_dec_ref(v_infoState_5338_);
v___x_5340_ = lean_st_ref_take(v___y_5335_);
v_infoState_5341_ = lean_ctor_get(v___x_5340_, 7);
v_env_5342_ = lean_ctor_get(v___x_5340_, 0);
v_nextMacroScope_5343_ = lean_ctor_get(v___x_5340_, 1);
v_ngen_5344_ = lean_ctor_get(v___x_5340_, 2);
v_auxDeclNGen_5345_ = lean_ctor_get(v___x_5340_, 3);
v_traceState_5346_ = lean_ctor_get(v___x_5340_, 4);
v_cache_5347_ = lean_ctor_get(v___x_5340_, 5);
v_messages_5348_ = lean_ctor_get(v___x_5340_, 6);
v_snapshotTasks_5349_ = lean_ctor_get(v___x_5340_, 8);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5351_ = v___x_5340_;
v_isShared_5352_ = v_isSharedCheck_5370_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_snapshotTasks_5349_);
lean_inc(v_infoState_5341_);
lean_inc(v_messages_5348_);
lean_inc(v_cache_5347_);
lean_inc(v_traceState_5346_);
lean_inc(v_auxDeclNGen_5345_);
lean_inc(v_ngen_5344_);
lean_inc(v_nextMacroScope_5343_);
lean_inc(v_env_5342_);
lean_dec(v___x_5340_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5370_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
uint8_t v_enabled_5353_; lean_object* v_assignment_5354_; lean_object* v_lazyAssignment_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5368_; 
v_enabled_5353_ = lean_ctor_get_uint8(v_infoState_5341_, sizeof(void*)*3);
v_assignment_5354_ = lean_ctor_get(v_infoState_5341_, 0);
v_lazyAssignment_5355_ = lean_ctor_get(v_infoState_5341_, 1);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_infoState_5341_);
if (v_isSharedCheck_5368_ == 0)
{
lean_object* v_unused_5369_; 
v_unused_5369_ = lean_ctor_get(v_infoState_5341_, 2);
lean_dec(v_unused_5369_);
v___x_5357_ = v_infoState_5341_;
v_isShared_5358_ = v_isSharedCheck_5368_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_lazyAssignment_5355_);
lean_inc(v_assignment_5354_);
lean_dec(v_infoState_5341_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5368_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 2, v___x_5359_);
v___x_5361_ = v___x_5357_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_assignment_5354_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_lazyAssignment_5355_);
lean_ctor_set(v_reuseFailAlloc_5367_, 2, v___x_5359_);
lean_ctor_set_uint8(v_reuseFailAlloc_5367_, sizeof(void*)*3, v_enabled_5353_);
v___x_5361_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5363_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 7, v___x_5361_);
v___x_5363_ = v___x_5351_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_env_5342_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_nextMacroScope_5343_);
lean_ctor_set(v_reuseFailAlloc_5366_, 2, v_ngen_5344_);
lean_ctor_set(v_reuseFailAlloc_5366_, 3, v_auxDeclNGen_5345_);
lean_ctor_set(v_reuseFailAlloc_5366_, 4, v_traceState_5346_);
lean_ctor_set(v_reuseFailAlloc_5366_, 5, v_cache_5347_);
lean_ctor_set(v_reuseFailAlloc_5366_, 6, v_messages_5348_);
lean_ctor_set(v_reuseFailAlloc_5366_, 7, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5366_, 8, v_snapshotTasks_5349_);
v___x_5363_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5364_ = lean_st_ref_set(v___y_5335_, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_trees_5339_);
return v___x_5365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5371_);
lean_dec(v___y_5371_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5374_, lean_object* v_mkInfoTree_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v_a_5383_, lean_object* v_a_x3f_5384_){
_start:
{
lean_object* v___x_5386_; lean_object* v_infoState_5387_; lean_object* v_trees_5388_; lean_object* v___x_5389_; 
v___x_5386_ = lean_st_ref_get(v___y_5374_);
v_infoState_5387_ = lean_ctor_get(v___x_5386_, 7);
lean_inc_ref(v_infoState_5387_);
lean_dec(v___x_5386_);
v_trees_5388_ = lean_ctor_get(v_infoState_5387_, 2);
lean_inc_ref(v_trees_5388_);
lean_dec_ref(v_infoState_5387_);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5382_);
lean_inc(v___y_5381_);
lean_inc_ref(v___y_5380_);
lean_inc(v___y_5379_);
lean_inc_ref(v___y_5378_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5376_);
v___x_5389_ = lean_apply_10(v_mkInfoTree_5375_, v_trees_5388_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5374_, lean_box(0));
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5428_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5392_ = v___x_5389_;
v_isShared_5393_ = v_isSharedCheck_5428_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5389_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5428_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5394_; lean_object* v_infoState_5395_; lean_object* v_env_5396_; lean_object* v_nextMacroScope_5397_; lean_object* v_ngen_5398_; lean_object* v_auxDeclNGen_5399_; lean_object* v_traceState_5400_; lean_object* v_cache_5401_; lean_object* v_messages_5402_; lean_object* v_snapshotTasks_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5427_; 
v___x_5394_ = lean_st_ref_take(v___y_5374_);
v_infoState_5395_ = lean_ctor_get(v___x_5394_, 7);
v_env_5396_ = lean_ctor_get(v___x_5394_, 0);
v_nextMacroScope_5397_ = lean_ctor_get(v___x_5394_, 1);
v_ngen_5398_ = lean_ctor_get(v___x_5394_, 2);
v_auxDeclNGen_5399_ = lean_ctor_get(v___x_5394_, 3);
v_traceState_5400_ = lean_ctor_get(v___x_5394_, 4);
v_cache_5401_ = lean_ctor_get(v___x_5394_, 5);
v_messages_5402_ = lean_ctor_get(v___x_5394_, 6);
v_snapshotTasks_5403_ = lean_ctor_get(v___x_5394_, 8);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5405_ = v___x_5394_;
v_isShared_5406_ = v_isSharedCheck_5427_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_snapshotTasks_5403_);
lean_inc(v_infoState_5395_);
lean_inc(v_messages_5402_);
lean_inc(v_cache_5401_);
lean_inc(v_traceState_5400_);
lean_inc(v_auxDeclNGen_5399_);
lean_inc(v_ngen_5398_);
lean_inc(v_nextMacroScope_5397_);
lean_inc(v_env_5396_);
lean_dec(v___x_5394_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5427_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
uint8_t v_enabled_5407_; lean_object* v_assignment_5408_; lean_object* v_lazyAssignment_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5425_; 
v_enabled_5407_ = lean_ctor_get_uint8(v_infoState_5395_, sizeof(void*)*3);
v_assignment_5408_ = lean_ctor_get(v_infoState_5395_, 0);
v_lazyAssignment_5409_ = lean_ctor_get(v_infoState_5395_, 1);
v_isSharedCheck_5425_ = !lean_is_exclusive(v_infoState_5395_);
if (v_isSharedCheck_5425_ == 0)
{
lean_object* v_unused_5426_; 
v_unused_5426_ = lean_ctor_get(v_infoState_5395_, 2);
lean_dec(v_unused_5426_);
v___x_5411_ = v_infoState_5395_;
v_isShared_5412_ = v_isSharedCheck_5425_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_lazyAssignment_5409_);
lean_inc(v_assignment_5408_);
lean_dec(v_infoState_5395_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5425_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; lean_object* v___x_5415_; 
v___x_5413_ = l_Lean_PersistentArray_push___redArg(v_a_5383_, v_a_5390_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 2, v___x_5413_);
v___x_5415_ = v___x_5411_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_assignment_5408_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_lazyAssignment_5409_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v___x_5413_);
lean_ctor_set_uint8(v_reuseFailAlloc_5424_, sizeof(void*)*3, v_enabled_5407_);
v___x_5415_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5417_; 
if (v_isShared_5406_ == 0)
{
lean_ctor_set(v___x_5405_, 7, v___x_5415_);
v___x_5417_ = v___x_5405_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_env_5396_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_nextMacroScope_5397_);
lean_ctor_set(v_reuseFailAlloc_5423_, 2, v_ngen_5398_);
lean_ctor_set(v_reuseFailAlloc_5423_, 3, v_auxDeclNGen_5399_);
lean_ctor_set(v_reuseFailAlloc_5423_, 4, v_traceState_5400_);
lean_ctor_set(v_reuseFailAlloc_5423_, 5, v_cache_5401_);
lean_ctor_set(v_reuseFailAlloc_5423_, 6, v_messages_5402_);
lean_ctor_set(v_reuseFailAlloc_5423_, 7, v___x_5415_);
lean_ctor_set(v_reuseFailAlloc_5423_, 8, v_snapshotTasks_5403_);
v___x_5417_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v___x_5418_ = lean_st_ref_set(v___y_5374_, v___x_5417_);
v___x_5419_ = lean_box(0);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5419_);
v___x_5421_ = v___x_5392_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_a_5383_);
v_a_5429_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5389_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5389_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5437_, lean_object* v_mkInfoTree_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v_a_5446_, lean_object* v_a_x3f_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5437_, v_mkInfoTree_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v_a_5446_, v_a_x3f_5447_);
lean_dec(v_a_x3f_5447_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5437_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5450_, lean_object* v_mkInfoTree_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v_infoState_5462_; uint8_t v_enabled_5463_; 
v___x_5461_ = lean_st_ref_get(v___y_5459_);
v_infoState_5462_ = lean_ctor_get(v___x_5461_, 7);
lean_inc_ref(v_infoState_5462_);
lean_dec(v___x_5461_);
v_enabled_5463_ = lean_ctor_get_uint8(v_infoState_5462_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5462_);
if (v_enabled_5463_ == 0)
{
lean_object* v___x_5464_; 
lean_dec_ref(v_mkInfoTree_5451_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5454_);
lean_inc(v___y_5453_);
lean_inc_ref(v___y_5452_);
v___x_5464_ = lean_apply_9(v_x_5450_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, lean_box(0));
return v___x_5464_;
}
else
{
lean_object* v___x_5465_; lean_object* v_a_5466_; lean_object* v_r_5467_; 
v___x_5465_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5459_);
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref(v___x_5465_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5454_);
lean_inc(v___y_5453_);
lean_inc_ref(v___y_5452_);
v_r_5467_ = lean_apply_9(v_x_5450_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, lean_box(0));
if (lean_obj_tag(v_r_5467_) == 0)
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5492_; 
v_a_5468_ = lean_ctor_get(v_r_5467_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v_r_5467_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5470_ = v_r_5467_;
v_isShared_5471_ = v_isSharedCheck_5492_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v_r_5467_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5492_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
lean_inc(v_a_5468_);
if (v_isShared_5471_ == 0)
{
lean_ctor_set_tag(v___x_5470_, 1);
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5459_, v_mkInfoTree_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v_a_5466_, v___x_5473_);
lean_dec_ref(v___x_5473_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5481_ == 0)
{
lean_object* v_unused_5482_; 
v_unused_5482_ = lean_ctor_get(v___x_5474_, 0);
lean_dec(v_unused_5482_);
v___x_5476_ = v___x_5474_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_dec(v___x_5474_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v_a_5468_);
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5468_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_a_5468_);
v_a_5483_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5474_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5474_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v_a_5493_ = lean_ctor_get(v_r_5467_, 0);
lean_inc(v_a_5493_);
lean_dec_ref(v_r_5467_);
v___x_5494_ = lean_box(0);
v___x_5495_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5459_, v_mkInfoTree_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v_a_5466_, v___x_5494_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; 
v_unused_5503_ = lean_ctor_get(v___x_5495_, 0);
lean_dec(v_unused_5503_);
v___x_5497_ = v___x_5495_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_dec(v___x_5495_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
lean_ctor_set_tag(v___x_5497_, 1);
lean_ctor_set(v___x_5497_, 0, v_a_5493_);
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5493_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v_a_5493_);
v_a_5504_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5495_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5495_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5512_, lean_object* v_mkInfoTree_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5512_, v_mkInfoTree_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
lean_dec(v___y_5515_);
lean_dec_ref(v___y_5514_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5524_, lean_object* v_trees_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
lean_object* v___x_5535_; 
lean_inc(v___y_5533_);
lean_inc_ref(v___y_5532_);
lean_inc(v___y_5531_);
lean_inc_ref(v___y_5530_);
lean_inc(v___y_5529_);
lean_inc_ref(v___y_5528_);
lean_inc(v___y_5527_);
lean_inc_ref(v___y_5526_);
v___x_5535_ = lean_apply_9(v_a_5524_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, lean_box(0));
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5544_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5544_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5544_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; lean_object* v___x_5542_; 
v___x_5540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5540_, 0, v_a_5536_);
lean_ctor_set(v___x_5540_, 1, v_trees_5525_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5540_);
v___x_5542_ = v___x_5538_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
else
{
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
lean_dec_ref(v_trees_5525_);
v_a_5545_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5535_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5535_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5553_, lean_object* v_trees_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5553_, v_trees_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec(v___y_5558_);
lean_dec_ref(v___y_5557_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5565_, lean_object* v_ref_5566_, lean_object* v_tactic_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v___x_5577_; 
v___x_5577_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5565_, v___y_5569_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v___x_5578_; 
lean_dec_ref(v___x_5577_);
v___x_5578_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v___x_5579_; 
lean_dec_ref(v___x_5578_);
v___x_5579_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5566_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v___f_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5580_);
lean_dec_ref(v___x_5579_);
v___f_5581_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5581_, 0, v_a_5580_);
v___x_5582_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5582_, 0, v_tactic_5567_);
v___x_5583_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5582_, v___f_5581_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
return v___x_5583_;
}
else
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
lean_dec(v_tactic_5567_);
v_a_5584_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5586_ = v___x_5579_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5579_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
else
{
lean_dec(v_tactic_5567_);
lean_dec(v_ref_5566_);
return v___x_5578_;
}
}
else
{
lean_dec(v_tactic_5567_);
lean_dec(v_ref_5566_);
return v___x_5577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5592_, lean_object* v_ref_5593_, lean_object* v_tactic_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5592_, v_ref_5593_, v_tactic_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
return v_res_5604_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5605_; lean_object* v___x_5606_; 
v___x_5605_ = lean_box(1);
v___x_5606_ = l_Lean_MessageData_ofFormat(v___x_5605_);
return v___x_5606_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5610_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5611_ = l_Lean_MessageData_ofFormat(v___x_5610_);
return v___x_5611_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5612_, lean_object* v_x_5613_){
_start:
{
if (lean_obj_tag(v_x_5613_) == 0)
{
return v_x_5612_;
}
else
{
lean_object* v_head_5614_; lean_object* v_tail_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5637_; 
v_head_5614_ = lean_ctor_get(v_x_5613_, 0);
v_tail_5615_ = lean_ctor_get(v_x_5613_, 1);
v_isSharedCheck_5637_ = !lean_is_exclusive(v_x_5613_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5617_ = v_x_5613_;
v_isShared_5618_ = v_isSharedCheck_5637_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_tail_5615_);
lean_inc(v_head_5614_);
lean_dec(v_x_5613_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5637_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v_before_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5635_; 
v_before_5619_ = lean_ctor_get(v_head_5614_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v_head_5614_);
if (v_isSharedCheck_5635_ == 0)
{
lean_object* v_unused_5636_; 
v_unused_5636_ = lean_ctor_get(v_head_5614_, 1);
lean_dec(v_unused_5636_);
v___x_5621_ = v_head_5614_;
v_isShared_5622_ = v_isSharedCheck_5635_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_before_5619_);
lean_dec(v_head_5614_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5635_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5623_; lean_object* v___x_5625_; 
v___x_5623_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5622_ == 0)
{
lean_ctor_set_tag(v___x_5621_, 7);
lean_ctor_set(v___x_5621_, 1, v___x_5623_);
lean_ctor_set(v___x_5621_, 0, v_x_5612_);
v___x_5625_ = v___x_5621_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_x_5612_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v___x_5623_);
v___x_5625_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5626_; lean_object* v___x_5628_; 
v___x_5626_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5618_ == 0)
{
lean_ctor_set_tag(v___x_5617_, 7);
lean_ctor_set(v___x_5617_, 1, v___x_5626_);
lean_ctor_set(v___x_5617_, 0, v___x_5625_);
v___x_5628_ = v___x_5617_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5625_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v___x_5626_);
v___x_5628_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5629_ = l_Lean_MessageData_ofSyntax(v_before_5619_);
v___x_5630_ = l_Lean_indentD(v___x_5629_);
v___x_5631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5628_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
v_x_5612_ = v___x_5631_;
v_x_5613_ = v_tail_5615_;
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
lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5641_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5642_ = l_Lean_MessageData_ofFormat(v___x_5641_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5643_, lean_object* v_macroStack_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v_options_5647_; lean_object* v___x_5648_; uint8_t v___x_5649_; 
v_options_5647_ = lean_ctor_get(v___y_5645_, 2);
v___x_5648_ = l_Lean_Elab_pp_macroStack;
v___x_5649_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_options_5647_, v___x_5648_);
if (v___x_5649_ == 0)
{
lean_object* v___x_5650_; 
lean_dec(v_macroStack_5644_);
v___x_5650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5650_, 0, v_msgData_5643_);
return v___x_5650_;
}
else
{
if (lean_obj_tag(v_macroStack_5644_) == 0)
{
lean_object* v___x_5651_; 
v___x_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5651_, 0, v_msgData_5643_);
return v___x_5651_;
}
else
{
lean_object* v_head_5652_; lean_object* v_after_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5668_; 
v_head_5652_ = lean_ctor_get(v_macroStack_5644_, 0);
lean_inc(v_head_5652_);
v_after_5653_ = lean_ctor_get(v_head_5652_, 1);
v_isSharedCheck_5668_ = !lean_is_exclusive(v_head_5652_);
if (v_isSharedCheck_5668_ == 0)
{
lean_object* v_unused_5669_; 
v_unused_5669_ = lean_ctor_get(v_head_5652_, 0);
lean_dec(v_unused_5669_);
v___x_5655_ = v_head_5652_;
v_isShared_5656_ = v_isSharedCheck_5668_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_after_5653_);
lean_dec(v_head_5652_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5668_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5657_; lean_object* v___x_5659_; 
v___x_5657_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5656_ == 0)
{
lean_ctor_set_tag(v___x_5655_, 7);
lean_ctor_set(v___x_5655_, 1, v___x_5657_);
lean_ctor_set(v___x_5655_, 0, v_msgData_5643_);
v___x_5659_ = v___x_5655_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_msgData_5643_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v___x_5657_);
v___x_5659_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v_msgData_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; 
v___x_5660_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5659_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = l_Lean_MessageData_ofSyntax(v_after_5653_);
v___x_5663_ = l_Lean_indentD(v___x_5662_);
v_msgData_5664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5664_, 0, v___x_5661_);
lean_ctor_set(v_msgData_5664_, 1, v___x_5663_);
v___x_5665_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5664_, v_macroStack_5644_);
v___x_5666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
return v___x_5666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5670_, lean_object* v_macroStack_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v_res_5674_; 
v_res_5674_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5670_, v_macroStack_5671_, v___y_5672_);
lean_dec_ref(v___y_5672_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
lean_object* v_ref_5683_; lean_object* v___x_5684_; lean_object* v_a_5685_; lean_object* v_macroStack_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5697_; 
v_ref_5683_ = lean_ctor_get(v___y_5680_, 5);
v___x_5684_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5675_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_a_5685_);
lean_dec_ref(v___x_5684_);
v_macroStack_5686_ = lean_ctor_get(v___y_5676_, 1);
lean_inc(v_macroStack_5686_);
lean_dec_ref(v___y_5676_);
lean_inc(v_macroStack_5686_);
v___x_5687_ = l_Lean_Elab_getBetterRef(v_ref_5683_, v_macroStack_5686_);
v___x_5688_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5685_, v_macroStack_5686_, v___y_5680_);
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5691_ = v___x_5688_;
v_isShared_5692_ = v_isSharedCheck_5697_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5688_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5697_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5693_; lean_object* v___x_5695_; 
v___x_5693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5687_);
lean_ctor_set(v___x_5693_, 1, v_a_5689_);
if (v_isShared_5692_ == 0)
{
lean_ctor_set_tag(v___x_5691_, 1);
lean_ctor_set(v___x_5691_, 0, v___x_5693_);
v___x_5695_ = v___x_5691_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5693_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
lean_dec(v___y_5704_);
lean_dec_ref(v___y_5703_);
lean_dec(v___y_5702_);
lean_dec_ref(v___y_5701_);
lean_dec(v___y_5700_);
return v_res_5706_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5709_ = l_Lean_stringToMessageData(v___x_5708_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5710_, size_t v_sz_5711_, size_t v_i_5712_, lean_object* v_b_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
lean_object* v_a_5722_; uint8_t v___x_5726_; 
v___x_5726_ = lean_usize_dec_lt(v_i_5712_, v_sz_5711_);
if (v___x_5726_ == 0)
{
lean_object* v___x_5727_; 
v___x_5727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5727_, 0, v_b_5713_);
return v___x_5727_;
}
else
{
lean_object* v_a_5728_; lean_object* v___x_5729_; 
v_a_5728_ = lean_array_uget_borrowed(v_as_5710_, v_i_5712_);
lean_inc(v_a_5728_);
v___x_5729_ = l_Lean_MVarId_getType(v_a_5728_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; lean_object* v___x_5731_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
lean_dec_ref(v___x_5729_);
lean_inc(v_a_5728_);
v___x_5731_ = l_Lean_MVarId_getType(v_a_5728_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
lean_dec_ref(v___x_5731_);
v___x_5733_ = lean_box(0);
v___x_5734_ = l_Lean_getRecAppSyntax_x3f(v_a_5732_);
lean_dec(v_a_5732_);
if (lean_obj_tag(v___x_5734_) == 1)
{
lean_object* v_val_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_val_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_val_5735_);
lean_dec_ref(v___x_5734_);
v___x_5736_ = l_Lean_Expr_mdataExpr_x21(v_a_5730_);
lean_dec(v_a_5730_);
lean_inc(v_a_5728_);
v___x_5737_ = l_Lean_MVarId_setType___redArg(v_a_5728_, v___x_5736_, v___y_5717_);
if (lean_obj_tag(v___x_5737_) == 0)
{
lean_object* v_fileName_5738_; lean_object* v_fileMap_5739_; lean_object* v_options_5740_; lean_object* v_currRecDepth_5741_; lean_object* v_maxRecDepth_5742_; lean_object* v_ref_5743_; lean_object* v_currNamespace_5744_; lean_object* v_openDecls_5745_; lean_object* v_initHeartbeats_5746_; lean_object* v_maxHeartbeats_5747_; lean_object* v_quotContext_5748_; lean_object* v_currMacroScope_5749_; uint8_t v_diag_5750_; lean_object* v_cancelTk_x3f_5751_; uint8_t v_suppressElabErrors_5752_; lean_object* v_inheritedTraceOptions_5753_; lean_object* v_ref_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
lean_dec_ref(v___x_5737_);
v_fileName_5738_ = lean_ctor_get(v___y_5718_, 0);
v_fileMap_5739_ = lean_ctor_get(v___y_5718_, 1);
v_options_5740_ = lean_ctor_get(v___y_5718_, 2);
v_currRecDepth_5741_ = lean_ctor_get(v___y_5718_, 3);
v_maxRecDepth_5742_ = lean_ctor_get(v___y_5718_, 4);
v_ref_5743_ = lean_ctor_get(v___y_5718_, 5);
v_currNamespace_5744_ = lean_ctor_get(v___y_5718_, 6);
v_openDecls_5745_ = lean_ctor_get(v___y_5718_, 7);
v_initHeartbeats_5746_ = lean_ctor_get(v___y_5718_, 8);
v_maxHeartbeats_5747_ = lean_ctor_get(v___y_5718_, 9);
v_quotContext_5748_ = lean_ctor_get(v___y_5718_, 10);
v_currMacroScope_5749_ = lean_ctor_get(v___y_5718_, 11);
v_diag_5750_ = lean_ctor_get_uint8(v___y_5718_, sizeof(void*)*14);
v_cancelTk_x3f_5751_ = lean_ctor_get(v___y_5718_, 12);
v_suppressElabErrors_5752_ = lean_ctor_get_uint8(v___y_5718_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5753_ = lean_ctor_get(v___y_5718_, 13);
v_ref_5754_ = l_Lean_replaceRef(v_val_5735_, v_ref_5743_);
lean_dec(v_val_5735_);
lean_inc_ref(v_inheritedTraceOptions_5753_);
lean_inc(v_cancelTk_x3f_5751_);
lean_inc(v_currMacroScope_5749_);
lean_inc(v_quotContext_5748_);
lean_inc(v_maxHeartbeats_5747_);
lean_inc(v_initHeartbeats_5746_);
lean_inc(v_openDecls_5745_);
lean_inc(v_currNamespace_5744_);
lean_inc(v_maxRecDepth_5742_);
lean_inc(v_currRecDepth_5741_);
lean_inc_ref(v_options_5740_);
lean_inc_ref(v_fileMap_5739_);
lean_inc_ref(v_fileName_5738_);
v___x_5755_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5755_, 0, v_fileName_5738_);
lean_ctor_set(v___x_5755_, 1, v_fileMap_5739_);
lean_ctor_set(v___x_5755_, 2, v_options_5740_);
lean_ctor_set(v___x_5755_, 3, v_currRecDepth_5741_);
lean_ctor_set(v___x_5755_, 4, v_maxRecDepth_5742_);
lean_ctor_set(v___x_5755_, 5, v_ref_5754_);
lean_ctor_set(v___x_5755_, 6, v_currNamespace_5744_);
lean_ctor_set(v___x_5755_, 7, v_openDecls_5745_);
lean_ctor_set(v___x_5755_, 8, v_initHeartbeats_5746_);
lean_ctor_set(v___x_5755_, 9, v_maxHeartbeats_5747_);
lean_ctor_set(v___x_5755_, 10, v_quotContext_5748_);
lean_ctor_set(v___x_5755_, 11, v_currMacroScope_5749_);
lean_ctor_set(v___x_5755_, 12, v_cancelTk_x3f_5751_);
lean_ctor_set(v___x_5755_, 13, v_inheritedTraceOptions_5753_);
lean_ctor_set_uint8(v___x_5755_, sizeof(void*)*14, v_diag_5750_);
lean_ctor_set_uint8(v___x_5755_, sizeof(void*)*14 + 1, v_suppressElabErrors_5752_);
lean_inc(v_a_5728_);
v___x_5756_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5728_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___x_5755_, v___y_5719_);
lean_dec_ref(v___x_5755_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_dec_ref(v___x_5756_);
v_a_5722_ = v___x_5733_;
goto v___jp_5721_;
}
else
{
return v___x_5756_;
}
}
else
{
lean_dec(v_val_5735_);
return v___x_5737_;
}
}
else
{
lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; 
lean_dec(v___x_5734_);
v___x_5757_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5758_ = l_Lean_indentExpr(v_a_5730_);
v___x_5759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5757_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
lean_inc_ref(v___y_5714_);
v___x_5760_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5759_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
if (lean_obj_tag(v___x_5760_) == 0)
{
lean_dec_ref(v___x_5760_);
v_a_5722_ = v___x_5733_;
goto v___jp_5721_;
}
else
{
return v___x_5760_;
}
}
}
else
{
lean_object* v_a_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5768_; 
lean_dec(v_a_5730_);
v_a_5761_ = lean_ctor_get(v___x_5731_, 0);
v_isSharedCheck_5768_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5768_ == 0)
{
v___x_5763_ = v___x_5731_;
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_a_5761_);
lean_dec(v___x_5731_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5766_; 
if (v_isShared_5764_ == 0)
{
v___x_5766_ = v___x_5763_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
v___x_5766_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
return v___x_5766_;
}
}
}
}
else
{
lean_object* v_a_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5776_; 
v_a_5769_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5771_ = v___x_5729_;
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_a_5769_);
lean_dec(v___x_5729_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5774_; 
if (v_isShared_5772_ == 0)
{
v___x_5774_ = v___x_5771_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
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
v___jp_5721_:
{
size_t v___x_5723_; size_t v___x_5724_; 
v___x_5723_ = ((size_t)1ULL);
v___x_5724_ = lean_usize_add(v_i_5712_, v___x_5723_);
v_i_5712_ = v___x_5724_;
v_b_5713_ = v_a_5722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5777_, lean_object* v_sz_5778_, lean_object* v_i_5779_, lean_object* v_b_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
size_t v_sz_boxed_5788_; size_t v_i_boxed_5789_; lean_object* v_res_5790_; 
v_sz_boxed_5788_ = lean_unbox_usize(v_sz_5778_);
lean_dec(v_sz_5778_);
v_i_boxed_5789_ = lean_unbox_usize(v_i_5779_);
lean_dec(v_i_5779_);
v_res_5790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5777_, v_sz_boxed_5788_, v_i_boxed_5789_, v_b_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5785_);
lean_dec(v___y_5784_);
lean_dec_ref(v___y_5783_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v_as_5777_);
return v_res_5790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5791_, size_t v_i_5792_, size_t v_stop_5793_, lean_object* v_b_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_){
_start:
{
uint8_t v___x_5800_; 
v___x_5800_ = lean_usize_dec_eq(v_i_5792_, v_stop_5793_);
if (v___x_5800_ == 0)
{
lean_object* v___x_5801_; lean_object* v___x_5802_; 
v___x_5801_ = lean_array_uget_borrowed(v_as_5791_, v_i_5792_);
lean_inc(v___x_5801_);
v___x_5802_ = l_Lean_MVarId_getType(v___x_5801_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref(v___x_5802_);
v___x_5804_ = l_Lean_Expr_mdataExpr_x21(v_a_5803_);
lean_dec(v_a_5803_);
lean_inc(v___x_5801_);
v___x_5805_ = l_Lean_MVarId_setType___redArg(v___x_5801_, v___x_5804_, v___y_5796_);
if (lean_obj_tag(v___x_5805_) == 0)
{
lean_object* v_a_5806_; size_t v___x_5807_; size_t v___x_5808_; 
v_a_5806_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_a_5806_);
lean_dec_ref(v___x_5805_);
v___x_5807_ = ((size_t)1ULL);
v___x_5808_ = lean_usize_add(v_i_5792_, v___x_5807_);
v_i_5792_ = v___x_5808_;
v_b_5794_ = v_a_5806_;
goto _start;
}
else
{
return v___x_5805_;
}
}
else
{
lean_object* v_a_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5817_; 
v_a_5810_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5812_ = v___x_5802_;
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_a_5810_);
lean_dec(v___x_5802_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5815_; 
if (v_isShared_5813_ == 0)
{
v___x_5815_ = v___x_5812_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_a_5810_);
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
lean_object* v___x_5818_; 
v___x_5818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5818_, 0, v_b_5794_);
return v___x_5818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5819_, lean_object* v_i_5820_, lean_object* v_stop_5821_, lean_object* v_b_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_){
_start:
{
size_t v_i_boxed_5828_; size_t v_stop_boxed_5829_; lean_object* v_res_5830_; 
v_i_boxed_5828_ = lean_unbox_usize(v_i_5820_);
lean_dec(v_i_5820_);
v_stop_boxed_5829_ = lean_unbox_usize(v_stop_5821_);
lean_dec(v_stop_5821_);
v_res_5830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5819_, v_i_boxed_5828_, v_stop_boxed_5829_, v_b_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
lean_dec(v___y_5826_);
lean_dec_ref(v___y_5825_);
lean_dec(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec_ref(v_as_5819_);
return v_res_5830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5831_, lean_object* v___x_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v___x_5840_; size_t v_sz_5841_; size_t v___x_5842_; lean_object* v___x_5843_; 
v___x_5840_ = lean_box(0);
v_sz_5841_ = lean_array_size(v___x_5832_);
v___x_5842_ = ((size_t)0ULL);
v___x_5843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5832_, v_sz_5841_, v___x_5842_, v___x_5840_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
lean_dec_ref(v___x_5832_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5850_; 
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5850_ == 0)
{
lean_object* v_unused_5851_; 
v_unused_5851_ = lean_ctor_get(v___x_5843_, 0);
lean_dec(v_unused_5851_);
v___x_5845_ = v___x_5843_;
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
else
{
lean_dec(v___x_5843_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5848_; 
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 0, v___x_5840_);
v___x_5848_ = v___x_5845_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v___x_5840_);
v___x_5848_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5847_;
}
v_reusejp_5847_:
{
return v___x_5848_;
}
}
}
else
{
return v___x_5843_;
}
}
else
{
lean_object* v_val_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5931_; 
v_val_5852_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5854_ = v___x_5831_;
v_isShared_5855_ = v_isSharedCheck_5931_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_val_5852_);
lean_dec(v___x_5831_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5931_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v_ref_5856_; lean_object* v_tactic_5857_; lean_object* v_fileName_5858_; lean_object* v_fileMap_5859_; lean_object* v_options_5860_; lean_object* v_currRecDepth_5861_; lean_object* v_maxRecDepth_5862_; lean_object* v_ref_5863_; lean_object* v_currNamespace_5864_; lean_object* v_openDecls_5865_; lean_object* v_initHeartbeats_5866_; lean_object* v_maxHeartbeats_5867_; lean_object* v_quotContext_5868_; lean_object* v_currMacroScope_5869_; uint8_t v_diag_5870_; lean_object* v_cancelTk_x3f_5871_; uint8_t v_suppressElabErrors_5872_; lean_object* v_inheritedTraceOptions_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v_ref_5876_; lean_object* v___x_5877_; lean_object* v___y_5904_; lean_object* v___y_5921_; uint8_t v___x_5922_; 
v_ref_5856_ = lean_ctor_get(v_val_5852_, 0);
lean_inc(v_ref_5856_);
v_tactic_5857_ = lean_ctor_get(v_val_5852_, 1);
lean_inc(v_tactic_5857_);
lean_dec(v_val_5852_);
v_fileName_5858_ = lean_ctor_get(v___y_5837_, 0);
v_fileMap_5859_ = lean_ctor_get(v___y_5837_, 1);
v_options_5860_ = lean_ctor_get(v___y_5837_, 2);
v_currRecDepth_5861_ = lean_ctor_get(v___y_5837_, 3);
v_maxRecDepth_5862_ = lean_ctor_get(v___y_5837_, 4);
v_ref_5863_ = lean_ctor_get(v___y_5837_, 5);
v_currNamespace_5864_ = lean_ctor_get(v___y_5837_, 6);
v_openDecls_5865_ = lean_ctor_get(v___y_5837_, 7);
v_initHeartbeats_5866_ = lean_ctor_get(v___y_5837_, 8);
v_maxHeartbeats_5867_ = lean_ctor_get(v___y_5837_, 9);
v_quotContext_5868_ = lean_ctor_get(v___y_5837_, 10);
v_currMacroScope_5869_ = lean_ctor_get(v___y_5837_, 11);
v_diag_5870_ = lean_ctor_get_uint8(v___y_5837_, sizeof(void*)*14);
v_cancelTk_x3f_5871_ = lean_ctor_get(v___y_5837_, 12);
v_suppressElabErrors_5872_ = lean_ctor_get_uint8(v___y_5837_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5873_ = lean_ctor_get(v___y_5837_, 13);
v___x_5874_ = lean_unsigned_to_nat(0u);
v___x_5875_ = lean_array_get_size(v___x_5832_);
v_ref_5876_ = l_Lean_replaceRef(v_ref_5856_, v_ref_5863_);
lean_inc_ref(v_inheritedTraceOptions_5873_);
lean_inc(v_cancelTk_x3f_5871_);
lean_inc(v_currMacroScope_5869_);
lean_inc(v_quotContext_5868_);
lean_inc(v_maxHeartbeats_5867_);
lean_inc(v_initHeartbeats_5866_);
lean_inc(v_openDecls_5865_);
lean_inc(v_currNamespace_5864_);
lean_inc(v_maxRecDepth_5862_);
lean_inc(v_currRecDepth_5861_);
lean_inc_ref(v_options_5860_);
lean_inc_ref(v_fileMap_5859_);
lean_inc_ref(v_fileName_5858_);
v___x_5877_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5877_, 0, v_fileName_5858_);
lean_ctor_set(v___x_5877_, 1, v_fileMap_5859_);
lean_ctor_set(v___x_5877_, 2, v_options_5860_);
lean_ctor_set(v___x_5877_, 3, v_currRecDepth_5861_);
lean_ctor_set(v___x_5877_, 4, v_maxRecDepth_5862_);
lean_ctor_set(v___x_5877_, 5, v_ref_5876_);
lean_ctor_set(v___x_5877_, 6, v_currNamespace_5864_);
lean_ctor_set(v___x_5877_, 7, v_openDecls_5865_);
lean_ctor_set(v___x_5877_, 8, v_initHeartbeats_5866_);
lean_ctor_set(v___x_5877_, 9, v_maxHeartbeats_5867_);
lean_ctor_set(v___x_5877_, 10, v_quotContext_5868_);
lean_ctor_set(v___x_5877_, 11, v_currMacroScope_5869_);
lean_ctor_set(v___x_5877_, 12, v_cancelTk_x3f_5871_);
lean_ctor_set(v___x_5877_, 13, v_inheritedTraceOptions_5873_);
lean_ctor_set_uint8(v___x_5877_, sizeof(void*)*14, v_diag_5870_);
lean_ctor_set_uint8(v___x_5877_, sizeof(void*)*14 + 1, v_suppressElabErrors_5872_);
v___x_5922_ = lean_nat_dec_lt(v___x_5874_, v___x_5875_);
if (v___x_5922_ == 0)
{
goto v___jp_5905_;
}
else
{
lean_object* v___x_5923_; uint8_t v___x_5924_; 
v___x_5923_ = lean_box(0);
v___x_5924_ = lean_nat_dec_le(v___x_5875_, v___x_5875_);
if (v___x_5924_ == 0)
{
if (v___x_5922_ == 0)
{
goto v___jp_5905_;
}
else
{
size_t v___x_5925_; size_t v___x_5926_; lean_object* v___x_5927_; 
v___x_5925_ = ((size_t)0ULL);
v___x_5926_ = lean_usize_of_nat(v___x_5875_);
v___x_5927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5832_, v___x_5925_, v___x_5926_, v___x_5923_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
v___y_5921_ = v___x_5927_;
goto v___jp_5920_;
}
}
else
{
size_t v___x_5928_; size_t v___x_5929_; lean_object* v___x_5930_; 
v___x_5928_ = ((size_t)0ULL);
v___x_5929_ = lean_usize_of_nat(v___x_5875_);
v___x_5930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5832_, v___x_5928_, v___x_5929_, v___x_5923_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
v___y_5921_ = v___x_5930_;
goto v___jp_5920_;
}
}
v___jp_5878_:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___f_5882_; lean_object* v___x_5883_; 
v___x_5879_ = lean_box(0);
v___x_5880_ = lean_array_get(v___x_5879_, v___x_5832_, v___x_5874_);
v___x_5881_ = lean_array_to_list(v___x_5832_);
v___f_5882_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5882_, 0, v___x_5881_);
lean_closure_set(v___f_5882_, 1, v_ref_5856_);
lean_closure_set(v___f_5882_, 2, v_tactic_5857_);
v___x_5883_ = l_Lean_Elab_Tactic_run(v___x_5880_, v___f_5882_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
if (lean_obj_tag(v___x_5883_) == 0)
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5894_; 
v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5886_ = v___x_5883_;
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5883_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
uint8_t v___x_5888_; 
v___x_5888_ = l_List_isEmpty___redArg(v_a_5884_);
if (v___x_5888_ == 0)
{
lean_object* v___x_5889_; 
lean_del_object(v___x_5886_);
v___x_5889_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5884_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
lean_dec_ref(v___x_5877_);
return v___x_5889_;
}
else
{
lean_object* v___x_5890_; lean_object* v___x_5892_; 
lean_dec(v_a_5884_);
lean_dec_ref(v___x_5877_);
v___x_5890_ = lean_box(0);
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 0, v___x_5890_);
v___x_5892_ = v___x_5886_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec_ref(v___x_5877_);
v_a_5895_ = lean_ctor_get(v___x_5883_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5883_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5883_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
v___jp_5903_:
{
if (lean_obj_tag(v___y_5904_) == 0)
{
lean_dec_ref(v___y_5904_);
goto v___jp_5878_;
}
else
{
lean_dec_ref(v___x_5877_);
lean_dec(v_tactic_5857_);
lean_dec(v_ref_5856_);
lean_dec_ref(v___x_5832_);
return v___y_5904_;
}
}
v___jp_5905_:
{
uint8_t v___x_5906_; 
v___x_5906_ = lean_nat_dec_eq(v___x_5875_, v___x_5874_);
if (v___x_5906_ == 0)
{
uint8_t v___x_5907_; 
lean_del_object(v___x_5854_);
v___x_5907_ = lean_nat_dec_lt(v___x_5874_, v___x_5875_);
if (v___x_5907_ == 0)
{
goto v___jp_5878_;
}
else
{
lean_object* v___x_5908_; uint8_t v___x_5909_; 
v___x_5908_ = lean_box(0);
v___x_5909_ = lean_nat_dec_le(v___x_5875_, v___x_5875_);
if (v___x_5909_ == 0)
{
if (v___x_5907_ == 0)
{
goto v___jp_5878_;
}
else
{
size_t v___x_5910_; size_t v___x_5911_; lean_object* v___x_5912_; 
v___x_5910_ = ((size_t)0ULL);
v___x_5911_ = lean_usize_of_nat(v___x_5875_);
v___x_5912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5832_, v___x_5910_, v___x_5911_, v___x_5908_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
v___y_5904_ = v___x_5912_;
goto v___jp_5903_;
}
}
else
{
size_t v___x_5913_; size_t v___x_5914_; lean_object* v___x_5915_; 
v___x_5913_ = ((size_t)0ULL);
v___x_5914_ = lean_usize_of_nat(v___x_5875_);
v___x_5915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5832_, v___x_5913_, v___x_5914_, v___x_5908_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___x_5877_, v___y_5838_);
v___y_5904_ = v___x_5915_;
goto v___jp_5903_;
}
}
}
else
{
lean_object* v___x_5916_; lean_object* v___x_5918_; 
lean_dec_ref(v___x_5877_);
lean_dec(v_tactic_5857_);
lean_dec(v_ref_5856_);
lean_dec_ref(v___x_5832_);
v___x_5916_ = lean_box(0);
if (v_isShared_5855_ == 0)
{
lean_ctor_set_tag(v___x_5854_, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5916_);
v___x_5918_ = v___x_5854_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v___x_5916_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
v___jp_5920_:
{
if (lean_obj_tag(v___y_5921_) == 0)
{
lean_dec_ref(v___y_5921_);
goto v___jp_5905_;
}
else
{
lean_dec_ref(v___x_5877_);
lean_dec(v_tactic_5857_);
lean_dec(v_ref_5856_);
lean_del_object(v___x_5854_);
lean_dec_ref(v___x_5832_);
return v___y_5921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5932_, lean_object* v___x_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v_res_5941_; 
v_res_5941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5932_, v___x_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_);
lean_dec(v___y_5939_);
lean_dec_ref(v___y_5938_);
lean_dec(v___y_5937_);
lean_dec_ref(v___y_5936_);
lean_dec(v___y_5935_);
lean_dec_ref(v___y_5934_);
return v_res_5941_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5942_){
_start:
{
uint8_t v___x_5943_; 
v___x_5943_ = 0;
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5944_){
_start:
{
uint8_t v_res_5945_; lean_object* v_r_5946_; 
v_res_5945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5944_);
lean_dec(v_x_5944_);
v_r_5946_ = lean_box(v_res_5945_);
return v_r_5946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5953_, size_t v_sz_5954_, size_t v_i_5955_, lean_object* v_b_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_){
_start:
{
uint8_t v___x_5962_; 
v___x_5962_ = lean_usize_dec_lt(v_i_5955_, v_sz_5954_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; 
v___x_5963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5963_, 0, v_b_5956_);
return v___x_5963_;
}
else
{
lean_object* v_snd_5964_; lean_object* v_fst_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_6036_; 
v_snd_5964_ = lean_ctor_get(v_b_5956_, 1);
v_fst_5965_ = lean_ctor_get(v_b_5956_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v_b_5956_);
if (v_isSharedCheck_6036_ == 0)
{
v___x_5967_ = v_b_5956_;
v_isShared_5968_ = v_isSharedCheck_6036_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_snd_5964_);
lean_inc(v_fst_5965_);
lean_dec(v_b_5956_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_6036_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v_array_5969_; lean_object* v_start_5970_; lean_object* v_stop_5971_; uint8_t v___x_5972_; 
v_array_5969_ = lean_ctor_get(v_snd_5964_, 0);
v_start_5970_ = lean_ctor_get(v_snd_5964_, 1);
v_stop_5971_ = lean_ctor_get(v_snd_5964_, 2);
v___x_5972_ = lean_nat_dec_lt(v_start_5970_, v_stop_5971_);
if (v___x_5972_ == 0)
{
lean_object* v___x_5974_; 
if (v_isShared_5968_ == 0)
{
v___x_5974_ = v___x_5967_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_fst_5965_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_snd_5964_);
v___x_5974_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; 
v___x_5975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
return v___x_5975_;
}
}
else
{
lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6032_; 
lean_inc(v_stop_5971_);
lean_inc(v_start_5970_);
lean_inc_ref(v_array_5969_);
v_isSharedCheck_6032_ = !lean_is_exclusive(v_snd_5964_);
if (v_isSharedCheck_6032_ == 0)
{
lean_object* v_unused_6033_; lean_object* v_unused_6034_; lean_object* v_unused_6035_; 
v_unused_6033_ = lean_ctor_get(v_snd_5964_, 2);
lean_dec(v_unused_6033_);
v_unused_6034_ = lean_ctor_get(v_snd_5964_, 1);
lean_dec(v_unused_6034_);
v_unused_6035_ = lean_ctor_get(v_snd_5964_, 0);
lean_dec(v_unused_6035_);
v___x_5978_ = v_snd_5964_;
v_isShared_5979_ = v_isSharedCheck_6032_;
goto v_resetjp_5977_;
}
else
{
lean_dec(v_snd_5964_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6032_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v_array_5980_; lean_object* v_start_5981_; lean_object* v_stop_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5987_; 
v_array_5980_ = lean_ctor_get(v_fst_5965_, 0);
v_start_5981_ = lean_ctor_get(v_fst_5965_, 1);
v_stop_5982_ = lean_ctor_get(v_fst_5965_, 2);
v___x_5983_ = lean_array_fget(v_array_5969_, v_start_5970_);
v___x_5984_ = lean_unsigned_to_nat(1u);
v___x_5985_ = lean_nat_add(v_start_5970_, v___x_5984_);
lean_dec(v_start_5970_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 1, v___x_5985_);
v___x_5987_ = v___x_5978_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_array_5969_);
lean_ctor_set(v_reuseFailAlloc_6031_, 1, v___x_5985_);
lean_ctor_set(v_reuseFailAlloc_6031_, 2, v_stop_5971_);
v___x_5987_ = v_reuseFailAlloc_6031_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
uint8_t v___x_5988_; 
v___x_5988_ = lean_nat_dec_lt(v_start_5981_, v_stop_5982_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5990_; 
lean_dec(v___x_5983_);
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 1, v___x_5987_);
v___x_5990_ = v___x_5967_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_fst_5965_);
lean_ctor_set(v_reuseFailAlloc_5992_, 1, v___x_5987_);
v___x_5990_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
lean_object* v___x_5991_; 
v___x_5991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
return v___x_5991_;
}
}
else
{
lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_6027_; 
lean_inc(v_stop_5982_);
lean_inc(v_start_5981_);
lean_inc_ref(v_array_5980_);
v_isSharedCheck_6027_ = !lean_is_exclusive(v_fst_5965_);
if (v_isSharedCheck_6027_ == 0)
{
lean_object* v_unused_6028_; lean_object* v_unused_6029_; lean_object* v_unused_6030_; 
v_unused_6028_ = lean_ctor_get(v_fst_5965_, 2);
lean_dec(v_unused_6028_);
v_unused_6029_ = lean_ctor_get(v_fst_5965_, 1);
lean_dec(v_unused_6029_);
v_unused_6030_ = lean_ctor_get(v_fst_5965_, 0);
lean_dec(v_unused_6030_);
v___x_5994_ = v_fst_5965_;
v_isShared_5995_ = v_isSharedCheck_6027_;
goto v_resetjp_5993_;
}
else
{
lean_dec(v_fst_5965_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_6027_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___f_5996_; lean_object* v_a_5997_; lean_object* v___x_5998_; lean_object* v___y_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; uint8_t v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; 
v___f_5996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5997_ = lean_array_uget_borrowed(v_as_5953_, v_i_5955_);
v___x_5998_ = lean_array_fget_borrowed(v_array_5980_, v_start_5981_);
lean_inc(v___x_5998_);
v___y_5999_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5999_, 0, v___x_5983_);
lean_closure_set(v___y_5999_, 1, v___x_5998_);
lean_inc(v_a_5997_);
v___x_6000_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_6000_, 0, lean_box(0));
lean_closure_set(v___x_6000_, 1, v_a_5997_);
lean_closure_set(v___x_6000_, 2, v___y_5999_);
v___x_6001_ = lean_box(0);
v___x_6002_ = lean_box(0);
v___x_6003_ = lean_box(1);
v___x_6004_ = 0;
v___x_6005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_6006_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_6006_, 0, v___x_6001_);
lean_ctor_set(v___x_6006_, 1, v___x_6002_);
lean_ctor_set(v___x_6006_, 2, v___x_6001_);
lean_ctor_set(v___x_6006_, 3, v___f_5996_);
lean_ctor_set(v___x_6006_, 4, v___x_6003_);
lean_ctor_set(v___x_6006_, 5, v___x_6003_);
lean_ctor_set(v___x_6006_, 6, v___x_6001_);
lean_ctor_set(v___x_6006_, 7, v___x_6005_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8, v___x_5988_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 1, v___x_5988_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 2, v___x_5988_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 3, v___x_5988_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 4, v___x_6004_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 5, v___x_6004_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 6, v___x_6004_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 7, v___x_6004_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 8, v___x_5988_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 9, v___x_6004_);
lean_ctor_set_uint8(v___x_6006_, sizeof(void*)*8 + 10, v___x_5988_);
v___x_6007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_6008_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_6000_, v___x_6006_, v___x_6007_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
if (lean_obj_tag(v___x_6008_) == 0)
{
lean_object* v___x_6009_; lean_object* v___x_6011_; 
lean_dec_ref(v___x_6008_);
v___x_6009_ = lean_nat_add(v_start_5981_, v___x_5984_);
lean_dec(v_start_5981_);
if (v_isShared_5995_ == 0)
{
lean_ctor_set(v___x_5994_, 1, v___x_6009_);
v___x_6011_ = v___x_5994_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_array_5980_);
lean_ctor_set(v_reuseFailAlloc_6018_, 1, v___x_6009_);
lean_ctor_set(v_reuseFailAlloc_6018_, 2, v_stop_5982_);
v___x_6011_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
lean_object* v___x_6013_; 
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 1, v___x_5987_);
lean_ctor_set(v___x_5967_, 0, v___x_6011_);
v___x_6013_ = v___x_5967_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v___x_5987_);
v___x_6013_ = v_reuseFailAlloc_6017_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
size_t v___x_6014_; size_t v___x_6015_; 
v___x_6014_ = ((size_t)1ULL);
v___x_6015_ = lean_usize_add(v_i_5955_, v___x_6014_);
v_i_5955_ = v___x_6015_;
v_b_5956_ = v___x_6013_;
goto _start;
}
}
}
else
{
lean_object* v_a_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6026_; 
lean_del_object(v___x_5994_);
lean_dec_ref(v___x_5987_);
lean_dec(v_stop_5982_);
lean_dec(v_start_5981_);
lean_dec_ref(v_array_5980_);
lean_del_object(v___x_5967_);
v_a_6019_ = lean_ctor_get(v___x_6008_, 0);
v_isSharedCheck_6026_ = !lean_is_exclusive(v___x_6008_);
if (v_isSharedCheck_6026_ == 0)
{
v___x_6021_ = v___x_6008_;
v_isShared_6022_ = v_isSharedCheck_6026_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_a_6019_);
lean_dec(v___x_6008_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6026_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v___x_6024_; 
if (v_isShared_6022_ == 0)
{
v___x_6024_ = v___x_6021_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_a_6019_);
v___x_6024_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
return v___x_6024_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_6037_, lean_object* v_sz_6038_, lean_object* v_i_6039_, lean_object* v_b_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_){
_start:
{
size_t v_sz_boxed_6046_; size_t v_i_boxed_6047_; lean_object* v_res_6048_; 
v_sz_boxed_6046_ = lean_unbox_usize(v_sz_6038_);
lean_dec(v_sz_6038_);
v_i_boxed_6047_ = lean_unbox_usize(v_i_6039_);
lean_dec(v_i_6039_);
v_res_6048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_6037_, v_sz_boxed_6046_, v_i_boxed_6047_, v_b_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
lean_dec(v___y_6044_);
lean_dec_ref(v___y_6043_);
lean_dec(v___y_6042_);
lean_dec_ref(v___y_6041_);
lean_dec_ref(v_as_6037_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_6049_, lean_object* v_decrTactics_6050_, lean_object* v_argsPacker_6051_, lean_object* v_funNames_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v___x_6058_; 
lean_inc_ref(v_value_6049_);
v___x_6058_ = l_Lean_Meta_getMVarsNoDelayed(v_value_6049_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_a_6059_; lean_object* v___x_6060_; 
v_a_6059_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_a_6059_);
lean_dec_ref(v___x_6058_);
v___x_6060_ = l_Lean_Elab_WF_assignSubsumed(v_a_6059_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
lean_dec(v_a_6059_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_object* v_a_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_a_6061_);
lean_dec_ref(v___x_6060_);
v___x_6062_ = lean_array_get_size(v_decrTactics_6050_);
v___x_6063_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_6051_, v___x_6062_, v_a_6061_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
lean_dec(v_a_6061_);
if (lean_obj_tag(v___x_6063_) == 0)
{
lean_object* v_a_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; size_t v_sz_6070_; size_t v___x_6071_; lean_object* v___x_6072_; 
v_a_6064_ = lean_ctor_get(v___x_6063_, 0);
lean_inc(v_a_6064_);
lean_dec_ref(v___x_6063_);
v___x_6065_ = lean_unsigned_to_nat(0u);
v___x_6066_ = lean_array_get_size(v_a_6064_);
v___x_6067_ = l_Array_toSubarray___redArg(v_a_6064_, v___x_6065_, v___x_6066_);
v___x_6068_ = l_Array_toSubarray___redArg(v_decrTactics_6050_, v___x_6065_, v___x_6062_);
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v_sz_6070_ = lean_array_size(v_funNames_6052_);
v___x_6071_ = ((size_t)0ULL);
v___x_6072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_6052_, v_sz_6070_, v___x_6071_, v___x_6069_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
if (lean_obj_tag(v___x_6072_) == 0)
{
lean_object* v___x_6073_; 
lean_dec_ref(v___x_6072_);
v___x_6073_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_6049_, v___y_6054_);
return v___x_6073_;
}
else
{
lean_object* v_a_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6081_; 
lean_dec_ref(v_value_6049_);
v_a_6074_ = lean_ctor_get(v___x_6072_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6072_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6076_ = v___x_6072_;
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_a_6074_);
lean_dec(v___x_6072_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6079_; 
if (v_isShared_6077_ == 0)
{
v___x_6079_ = v___x_6076_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
else
{
lean_object* v_a_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6089_; 
lean_dec_ref(v_decrTactics_6050_);
lean_dec_ref(v_value_6049_);
v_a_6082_ = lean_ctor_get(v___x_6063_, 0);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6063_);
if (v_isSharedCheck_6089_ == 0)
{
v___x_6084_ = v___x_6063_;
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_a_6082_);
lean_dec(v___x_6063_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6087_; 
if (v_isShared_6085_ == 0)
{
v___x_6087_ = v___x_6084_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
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
else
{
lean_object* v_a_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6097_; 
lean_dec_ref(v_decrTactics_6050_);
lean_dec_ref(v_value_6049_);
v_a_6090_ = lean_ctor_get(v___x_6060_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6092_ = v___x_6060_;
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_a_6090_);
lean_dec(v___x_6060_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6095_; 
if (v_isShared_6093_ == 0)
{
v___x_6095_ = v___x_6092_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_a_6090_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
return v___x_6095_;
}
}
}
}
else
{
lean_object* v_a_6098_; lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6105_; 
lean_dec_ref(v_decrTactics_6050_);
lean_dec_ref(v_value_6049_);
v_a_6098_ = lean_ctor_get(v___x_6058_, 0);
v_isSharedCheck_6105_ = !lean_is_exclusive(v___x_6058_);
if (v_isSharedCheck_6105_ == 0)
{
v___x_6100_ = v___x_6058_;
v_isShared_6101_ = v_isSharedCheck_6105_;
goto v_resetjp_6099_;
}
else
{
lean_inc(v_a_6098_);
lean_dec(v___x_6058_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6105_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
lean_object* v___x_6103_; 
if (v_isShared_6101_ == 0)
{
v___x_6103_ = v___x_6100_;
goto v_reusejp_6102_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_a_6098_);
v___x_6103_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6102_;
}
v_reusejp_6102_:
{
return v___x_6103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6106_, lean_object* v_decrTactics_6107_, lean_object* v_argsPacker_6108_, lean_object* v_funNames_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6106_, v_decrTactics_6107_, v_argsPacker_6108_, v_funNames_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_);
lean_dec(v___y_6113_);
lean_dec_ref(v___y_6112_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec_ref(v_funNames_6109_);
lean_dec_ref(v_argsPacker_6108_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6116_, uint8_t v_isExporting_6117_, lean_object* v___x_6118_, lean_object* v___y_6119_, lean_object* v___x_6120_, lean_object* v_a_x3f_6121_){
_start:
{
lean_object* v___x_6123_; lean_object* v_env_6124_; lean_object* v_nextMacroScope_6125_; lean_object* v_ngen_6126_; lean_object* v_auxDeclNGen_6127_; lean_object* v_traceState_6128_; lean_object* v_messages_6129_; lean_object* v_infoState_6130_; lean_object* v_snapshotTasks_6131_; lean_object* v___x_6133_; uint8_t v_isShared_6134_; uint8_t v_isSharedCheck_6156_; 
v___x_6123_ = lean_st_ref_take(v___y_6116_);
v_env_6124_ = lean_ctor_get(v___x_6123_, 0);
v_nextMacroScope_6125_ = lean_ctor_get(v___x_6123_, 1);
v_ngen_6126_ = lean_ctor_get(v___x_6123_, 2);
v_auxDeclNGen_6127_ = lean_ctor_get(v___x_6123_, 3);
v_traceState_6128_ = lean_ctor_get(v___x_6123_, 4);
v_messages_6129_ = lean_ctor_get(v___x_6123_, 6);
v_infoState_6130_ = lean_ctor_get(v___x_6123_, 7);
v_snapshotTasks_6131_ = lean_ctor_get(v___x_6123_, 8);
v_isSharedCheck_6156_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6156_ == 0)
{
lean_object* v_unused_6157_; 
v_unused_6157_ = lean_ctor_get(v___x_6123_, 5);
lean_dec(v_unused_6157_);
v___x_6133_ = v___x_6123_;
v_isShared_6134_ = v_isSharedCheck_6156_;
goto v_resetjp_6132_;
}
else
{
lean_inc(v_snapshotTasks_6131_);
lean_inc(v_infoState_6130_);
lean_inc(v_messages_6129_);
lean_inc(v_traceState_6128_);
lean_inc(v_auxDeclNGen_6127_);
lean_inc(v_ngen_6126_);
lean_inc(v_nextMacroScope_6125_);
lean_inc(v_env_6124_);
lean_dec(v___x_6123_);
v___x_6133_ = lean_box(0);
v_isShared_6134_ = v_isSharedCheck_6156_;
goto v_resetjp_6132_;
}
v_resetjp_6132_:
{
lean_object* v___x_6135_; lean_object* v___x_6137_; 
v___x_6135_ = l_Lean_Environment_setExporting(v_env_6124_, v_isExporting_6117_);
if (v_isShared_6134_ == 0)
{
lean_ctor_set(v___x_6133_, 5, v___x_6118_);
lean_ctor_set(v___x_6133_, 0, v___x_6135_);
v___x_6137_ = v___x_6133_;
goto v_reusejp_6136_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6135_);
lean_ctor_set(v_reuseFailAlloc_6155_, 1, v_nextMacroScope_6125_);
lean_ctor_set(v_reuseFailAlloc_6155_, 2, v_ngen_6126_);
lean_ctor_set(v_reuseFailAlloc_6155_, 3, v_auxDeclNGen_6127_);
lean_ctor_set(v_reuseFailAlloc_6155_, 4, v_traceState_6128_);
lean_ctor_set(v_reuseFailAlloc_6155_, 5, v___x_6118_);
lean_ctor_set(v_reuseFailAlloc_6155_, 6, v_messages_6129_);
lean_ctor_set(v_reuseFailAlloc_6155_, 7, v_infoState_6130_);
lean_ctor_set(v_reuseFailAlloc_6155_, 8, v_snapshotTasks_6131_);
v___x_6137_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6136_;
}
v_reusejp_6136_:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v_mctx_6140_; lean_object* v_zetaDeltaFVarIds_6141_; lean_object* v_postponed_6142_; lean_object* v_diag_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6153_; 
v___x_6138_ = lean_st_ref_set(v___y_6116_, v___x_6137_);
v___x_6139_ = lean_st_ref_take(v___y_6119_);
v_mctx_6140_ = lean_ctor_get(v___x_6139_, 0);
v_zetaDeltaFVarIds_6141_ = lean_ctor_get(v___x_6139_, 2);
v_postponed_6142_ = lean_ctor_get(v___x_6139_, 3);
v_diag_6143_ = lean_ctor_get(v___x_6139_, 4);
v_isSharedCheck_6153_ = !lean_is_exclusive(v___x_6139_);
if (v_isSharedCheck_6153_ == 0)
{
lean_object* v_unused_6154_; 
v_unused_6154_ = lean_ctor_get(v___x_6139_, 1);
lean_dec(v_unused_6154_);
v___x_6145_ = v___x_6139_;
v_isShared_6146_ = v_isSharedCheck_6153_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_diag_6143_);
lean_inc(v_postponed_6142_);
lean_inc(v_zetaDeltaFVarIds_6141_);
lean_inc(v_mctx_6140_);
lean_dec(v___x_6139_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6153_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
lean_ctor_set(v___x_6145_, 1, v___x_6120_);
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v_mctx_6140_);
lean_ctor_set(v_reuseFailAlloc_6152_, 1, v___x_6120_);
lean_ctor_set(v_reuseFailAlloc_6152_, 2, v_zetaDeltaFVarIds_6141_);
lean_ctor_set(v_reuseFailAlloc_6152_, 3, v_postponed_6142_);
lean_ctor_set(v_reuseFailAlloc_6152_, 4, v_diag_6143_);
v___x_6148_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; 
v___x_6149_ = lean_st_ref_set(v___y_6119_, v___x_6148_);
v___x_6150_ = lean_box(0);
v___x_6151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
return v___x_6151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6158_, lean_object* v_isExporting_6159_, lean_object* v___x_6160_, lean_object* v___y_6161_, lean_object* v___x_6162_, lean_object* v_a_x3f_6163_, lean_object* v___y_6164_){
_start:
{
uint8_t v_isExporting_boxed_6165_; lean_object* v_res_6166_; 
v_isExporting_boxed_6165_ = lean_unbox(v_isExporting_6159_);
v_res_6166_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6158_, v_isExporting_boxed_6165_, v___x_6160_, v___y_6161_, v___x_6162_, v_a_x3f_6163_);
lean_dec(v_a_x3f_6163_);
lean_dec(v___y_6161_);
lean_dec(v___y_6158_);
return v_res_6166_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6167_; 
v___x_6167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6167_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
return v___x_6169_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6170_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set(v___x_6171_, 1, v___x_6170_);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6172_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
lean_ctor_set(v___x_6173_, 2, v___x_6172_);
lean_ctor_set(v___x_6173_, 3, v___x_6172_);
lean_ctor_set(v___x_6173_, 4, v___x_6172_);
lean_ctor_set(v___x_6173_, 5, v___x_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6174_, uint8_t v_isExporting_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_){
_start:
{
lean_object* v___x_6181_; lean_object* v_env_6182_; uint8_t v_isExporting_6183_; lean_object* v___x_6184_; lean_object* v_env_6185_; lean_object* v_nextMacroScope_6186_; lean_object* v_ngen_6187_; lean_object* v_auxDeclNGen_6188_; lean_object* v_traceState_6189_; lean_object* v_messages_6190_; lean_object* v_infoState_6191_; lean_object* v_snapshotTasks_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6246_; 
v___x_6181_ = lean_st_ref_get(v___y_6179_);
v_env_6182_ = lean_ctor_get(v___x_6181_, 0);
lean_inc_ref(v_env_6182_);
lean_dec(v___x_6181_);
v_isExporting_6183_ = lean_ctor_get_uint8(v_env_6182_, sizeof(void*)*8);
lean_dec_ref(v_env_6182_);
v___x_6184_ = lean_st_ref_take(v___y_6179_);
v_env_6185_ = lean_ctor_get(v___x_6184_, 0);
v_nextMacroScope_6186_ = lean_ctor_get(v___x_6184_, 1);
v_ngen_6187_ = lean_ctor_get(v___x_6184_, 2);
v_auxDeclNGen_6188_ = lean_ctor_get(v___x_6184_, 3);
v_traceState_6189_ = lean_ctor_get(v___x_6184_, 4);
v_messages_6190_ = lean_ctor_get(v___x_6184_, 6);
v_infoState_6191_ = lean_ctor_get(v___x_6184_, 7);
v_snapshotTasks_6192_ = lean_ctor_get(v___x_6184_, 8);
v_isSharedCheck_6246_ = !lean_is_exclusive(v___x_6184_);
if (v_isSharedCheck_6246_ == 0)
{
lean_object* v_unused_6247_; 
v_unused_6247_ = lean_ctor_get(v___x_6184_, 5);
lean_dec(v_unused_6247_);
v___x_6194_ = v___x_6184_;
v_isShared_6195_ = v_isSharedCheck_6246_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_snapshotTasks_6192_);
lean_inc(v_infoState_6191_);
lean_inc(v_messages_6190_);
lean_inc(v_traceState_6189_);
lean_inc(v_auxDeclNGen_6188_);
lean_inc(v_ngen_6187_);
lean_inc(v_nextMacroScope_6186_);
lean_inc(v_env_6185_);
lean_dec(v___x_6184_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6246_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6199_; 
v___x_6196_ = l_Lean_Environment_setExporting(v_env_6185_, v_isExporting_6175_);
v___x_6197_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6195_ == 0)
{
lean_ctor_set(v___x_6194_, 5, v___x_6197_);
lean_ctor_set(v___x_6194_, 0, v___x_6196_);
v___x_6199_ = v___x_6194_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v___x_6196_);
lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_nextMacroScope_6186_);
lean_ctor_set(v_reuseFailAlloc_6245_, 2, v_ngen_6187_);
lean_ctor_set(v_reuseFailAlloc_6245_, 3, v_auxDeclNGen_6188_);
lean_ctor_set(v_reuseFailAlloc_6245_, 4, v_traceState_6189_);
lean_ctor_set(v_reuseFailAlloc_6245_, 5, v___x_6197_);
lean_ctor_set(v_reuseFailAlloc_6245_, 6, v_messages_6190_);
lean_ctor_set(v_reuseFailAlloc_6245_, 7, v_infoState_6191_);
lean_ctor_set(v_reuseFailAlloc_6245_, 8, v_snapshotTasks_6192_);
v___x_6199_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v_mctx_6202_; lean_object* v_zetaDeltaFVarIds_6203_; lean_object* v_postponed_6204_; lean_object* v_diag_6205_; lean_object* v___x_6207_; uint8_t v_isShared_6208_; uint8_t v_isSharedCheck_6243_; 
v___x_6200_ = lean_st_ref_set(v___y_6179_, v___x_6199_);
v___x_6201_ = lean_st_ref_take(v___y_6177_);
v_mctx_6202_ = lean_ctor_get(v___x_6201_, 0);
v_zetaDeltaFVarIds_6203_ = lean_ctor_get(v___x_6201_, 2);
v_postponed_6204_ = lean_ctor_get(v___x_6201_, 3);
v_diag_6205_ = lean_ctor_get(v___x_6201_, 4);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6201_);
if (v_isSharedCheck_6243_ == 0)
{
lean_object* v_unused_6244_; 
v_unused_6244_ = lean_ctor_get(v___x_6201_, 1);
lean_dec(v_unused_6244_);
v___x_6207_ = v___x_6201_;
v_isShared_6208_ = v_isSharedCheck_6243_;
goto v_resetjp_6206_;
}
else
{
lean_inc(v_diag_6205_);
lean_inc(v_postponed_6204_);
lean_inc(v_zetaDeltaFVarIds_6203_);
lean_inc(v_mctx_6202_);
lean_dec(v___x_6201_);
v___x_6207_ = lean_box(0);
v_isShared_6208_ = v_isSharedCheck_6243_;
goto v_resetjp_6206_;
}
v_resetjp_6206_:
{
lean_object* v___x_6209_; lean_object* v___x_6211_; 
v___x_6209_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6208_ == 0)
{
lean_ctor_set(v___x_6207_, 1, v___x_6209_);
v___x_6211_ = v___x_6207_;
goto v_reusejp_6210_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_mctx_6202_);
lean_ctor_set(v_reuseFailAlloc_6242_, 1, v___x_6209_);
lean_ctor_set(v_reuseFailAlloc_6242_, 2, v_zetaDeltaFVarIds_6203_);
lean_ctor_set(v_reuseFailAlloc_6242_, 3, v_postponed_6204_);
lean_ctor_set(v_reuseFailAlloc_6242_, 4, v_diag_6205_);
v___x_6211_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6210_;
}
v_reusejp_6210_:
{
lean_object* v___x_6212_; lean_object* v_r_6213_; 
v___x_6212_ = lean_st_ref_set(v___y_6177_, v___x_6211_);
lean_inc(v___y_6179_);
lean_inc_ref(v___y_6178_);
lean_inc(v___y_6177_);
lean_inc_ref(v___y_6176_);
v_r_6213_ = lean_apply_5(v_x_6174_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, lean_box(0));
if (lean_obj_tag(v_r_6213_) == 0)
{
lean_object* v_a_6214_; lean_object* v___x_6216_; uint8_t v_isShared_6217_; uint8_t v_isSharedCheck_6230_; 
v_a_6214_ = lean_ctor_get(v_r_6213_, 0);
v_isSharedCheck_6230_ = !lean_is_exclusive(v_r_6213_);
if (v_isSharedCheck_6230_ == 0)
{
v___x_6216_ = v_r_6213_;
v_isShared_6217_ = v_isSharedCheck_6230_;
goto v_resetjp_6215_;
}
else
{
lean_inc(v_a_6214_);
lean_dec(v_r_6213_);
v___x_6216_ = lean_box(0);
v_isShared_6217_ = v_isSharedCheck_6230_;
goto v_resetjp_6215_;
}
v_resetjp_6215_:
{
lean_object* v___x_6219_; 
lean_inc(v_a_6214_);
if (v_isShared_6217_ == 0)
{
lean_ctor_set_tag(v___x_6216_, 1);
v___x_6219_ = v___x_6216_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6229_; 
v_reuseFailAlloc_6229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6229_, 0, v_a_6214_);
v___x_6219_ = v_reuseFailAlloc_6229_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
lean_object* v___x_6220_; lean_object* v___x_6222_; uint8_t v_isShared_6223_; uint8_t v_isSharedCheck_6227_; 
v___x_6220_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6179_, v_isExporting_6183_, v___x_6197_, v___y_6177_, v___x_6209_, v___x_6219_);
lean_dec_ref(v___x_6219_);
v_isSharedCheck_6227_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6227_ == 0)
{
lean_object* v_unused_6228_; 
v_unused_6228_ = lean_ctor_get(v___x_6220_, 0);
lean_dec(v_unused_6228_);
v___x_6222_ = v___x_6220_;
v_isShared_6223_ = v_isSharedCheck_6227_;
goto v_resetjp_6221_;
}
else
{
lean_dec(v___x_6220_);
v___x_6222_ = lean_box(0);
v_isShared_6223_ = v_isSharedCheck_6227_;
goto v_resetjp_6221_;
}
v_resetjp_6221_:
{
lean_object* v___x_6225_; 
if (v_isShared_6223_ == 0)
{
lean_ctor_set(v___x_6222_, 0, v_a_6214_);
v___x_6225_ = v___x_6222_;
goto v_reusejp_6224_;
}
else
{
lean_object* v_reuseFailAlloc_6226_; 
v_reuseFailAlloc_6226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6226_, 0, v_a_6214_);
v___x_6225_ = v_reuseFailAlloc_6226_;
goto v_reusejp_6224_;
}
v_reusejp_6224_:
{
return v___x_6225_;
}
}
}
}
}
else
{
lean_object* v_a_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6235_; uint8_t v_isShared_6236_; uint8_t v_isSharedCheck_6240_; 
v_a_6231_ = lean_ctor_get(v_r_6213_, 0);
lean_inc(v_a_6231_);
lean_dec_ref(v_r_6213_);
v___x_6232_ = lean_box(0);
v___x_6233_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6179_, v_isExporting_6183_, v___x_6197_, v___y_6177_, v___x_6209_, v___x_6232_);
v_isSharedCheck_6240_ = !lean_is_exclusive(v___x_6233_);
if (v_isSharedCheck_6240_ == 0)
{
lean_object* v_unused_6241_; 
v_unused_6241_ = lean_ctor_get(v___x_6233_, 0);
lean_dec(v_unused_6241_);
v___x_6235_ = v___x_6233_;
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
else
{
lean_dec(v___x_6233_);
v___x_6235_ = lean_box(0);
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
v_resetjp_6234_:
{
lean_object* v___x_6238_; 
if (v_isShared_6236_ == 0)
{
lean_ctor_set_tag(v___x_6235_, 1);
lean_ctor_set(v___x_6235_, 0, v_a_6231_);
v___x_6238_ = v___x_6235_;
goto v_reusejp_6237_;
}
else
{
lean_object* v_reuseFailAlloc_6239_; 
v_reuseFailAlloc_6239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6239_, 0, v_a_6231_);
v___x_6238_ = v_reuseFailAlloc_6239_;
goto v_reusejp_6237_;
}
v_reusejp_6237_:
{
return v___x_6238_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6248_, lean_object* v_isExporting_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_){
_start:
{
uint8_t v_isExporting_boxed_6255_; lean_object* v_res_6256_; 
v_isExporting_boxed_6255_ = lean_unbox(v_isExporting_6249_);
v_res_6256_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6248_, v_isExporting_boxed_6255_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6257_, uint8_t v_when_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_){
_start:
{
if (v_when_6258_ == 0)
{
lean_object* v___x_6264_; 
lean_inc(v___y_6262_);
lean_inc_ref(v___y_6261_);
lean_inc(v___y_6260_);
lean_inc_ref(v___y_6259_);
v___x_6264_ = lean_apply_5(v_x_6257_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_, lean_box(0));
return v___x_6264_;
}
else
{
uint8_t v___x_6265_; lean_object* v___x_6266_; 
v___x_6265_ = 0;
v___x_6266_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6257_, v___x_6265_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
return v___x_6266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6267_, lean_object* v_when_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
uint8_t v_when_boxed_6274_; lean_object* v_res_6275_; 
v_when_boxed_6274_ = lean_unbox(v_when_6268_);
v_res_6275_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6267_, v_when_boxed_6274_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
return v_res_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6276_, lean_object* v_argsPacker_6277_, lean_object* v_decrTactics_6278_, lean_object* v_value_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_, lean_object* v_a_6282_, lean_object* v_a_6283_){
_start:
{
lean_object* v___f_6285_; uint8_t v___x_6286_; lean_object* v___x_6287_; 
v___f_6285_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6285_, 0, v_value_6279_);
lean_closure_set(v___f_6285_, 1, v_decrTactics_6278_);
lean_closure_set(v___f_6285_, 2, v_argsPacker_6277_);
lean_closure_set(v___f_6285_, 3, v_funNames_6276_);
v___x_6286_ = 1;
v___x_6287_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6285_, v___x_6286_, v_a_6280_, v_a_6281_, v_a_6282_, v_a_6283_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6288_, lean_object* v_argsPacker_6289_, lean_object* v_decrTactics_6290_, lean_object* v_value_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_){
_start:
{
lean_object* v_res_6297_; 
v_res_6297_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6288_, v_argsPacker_6289_, v_decrTactics_6290_, v_value_6291_, v_a_6292_, v_a_6293_, v_a_6294_, v_a_6295_);
lean_dec(v_a_6295_);
lean_dec_ref(v_a_6294_);
lean_dec(v_a_6293_);
lean_dec_ref(v_a_6292_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6298_, lean_object* v_msg_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v___x_6307_; 
lean_inc_ref(v___y_6300_);
v___x_6307_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6308_, lean_object* v_msg_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_){
_start:
{
lean_object* v_res_6317_; 
v_res_6317_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6308_, v_msg_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
lean_dec(v___y_6315_);
lean_dec_ref(v___y_6314_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_){
_start:
{
lean_object* v___x_6327_; 
v___x_6327_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6325_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_){
_start:
{
lean_object* v_res_6337_; 
v_res_6337_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_);
lean_dec(v___y_6335_);
lean_dec_ref(v___y_6334_);
lean_dec(v___y_6333_);
lean_dec_ref(v___y_6332_);
lean_dec(v___y_6331_);
lean_dec_ref(v___y_6330_);
lean_dec(v___y_6329_);
lean_dec_ref(v___y_6328_);
return v_res_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6338_, lean_object* v_x_6339_, lean_object* v_mkInfoTree_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_){
_start:
{
lean_object* v___x_6350_; 
v___x_6350_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6339_, v_mkInfoTree_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
return v___x_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6351_, lean_object* v_x_6352_, lean_object* v_mkInfoTree_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_){
_start:
{
lean_object* v_res_6363_; 
v_res_6363_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6351_, v_x_6352_, v_mkInfoTree_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_, v___y_6361_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec(v___y_6359_);
lean_dec_ref(v___y_6358_);
lean_dec(v___y_6357_);
lean_dec_ref(v___y_6356_);
lean_dec(v___y_6355_);
lean_dec_ref(v___y_6354_);
return v_res_6363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6364_, size_t v_i_6365_, size_t v_stop_6366_, lean_object* v_b_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_){
_start:
{
lean_object* v___x_6375_; 
v___x_6375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6364_, v_i_6365_, v_stop_6366_, v_b_6367_, v___y_6370_, v___y_6371_, v___y_6372_, v___y_6373_);
return v___x_6375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6376_, lean_object* v_i_6377_, lean_object* v_stop_6378_, lean_object* v_b_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_, lean_object* v___y_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_){
_start:
{
size_t v_i_boxed_6387_; size_t v_stop_boxed_6388_; lean_object* v_res_6389_; 
v_i_boxed_6387_ = lean_unbox_usize(v_i_6377_);
lean_dec(v_i_6377_);
v_stop_boxed_6388_ = lean_unbox_usize(v_stop_6378_);
lean_dec(v_stop_6378_);
v_res_6389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6376_, v_i_boxed_6387_, v_stop_boxed_6388_, v_b_6379_, v___y_6380_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_, v___y_6385_);
lean_dec(v___y_6385_);
lean_dec_ref(v___y_6384_);
lean_dec(v___y_6383_);
lean_dec_ref(v___y_6382_);
lean_dec(v___y_6381_);
lean_dec_ref(v___y_6380_);
lean_dec_ref(v_as_6376_);
return v_res_6389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6390_, lean_object* v_x_6391_, uint8_t v_isExporting_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_){
_start:
{
lean_object* v___x_6398_; 
v___x_6398_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6391_, v_isExporting_6392_, v___y_6393_, v___y_6394_, v___y_6395_, v___y_6396_);
return v___x_6398_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6399_, lean_object* v_x_6400_, lean_object* v_isExporting_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_){
_start:
{
uint8_t v_isExporting_boxed_6407_; lean_object* v_res_6408_; 
v_isExporting_boxed_6407_ = lean_unbox(v_isExporting_6401_);
v_res_6408_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6399_, v_x_6400_, v_isExporting_boxed_6407_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
lean_dec(v___y_6405_);
lean_dec_ref(v___y_6404_);
lean_dec(v___y_6403_);
lean_dec_ref(v___y_6402_);
return v_res_6408_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6409_, lean_object* v_x_6410_, uint8_t v_when_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_){
_start:
{
lean_object* v___x_6417_; 
v___x_6417_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6410_, v_when_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
return v___x_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6418_, lean_object* v_x_6419_, lean_object* v_when_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_, lean_object* v___y_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_){
_start:
{
uint8_t v_when_boxed_6426_; lean_object* v_res_6427_; 
v_when_boxed_6426_ = lean_unbox(v_when_6420_);
v_res_6427_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6418_, v_x_6419_, v_when_boxed_6426_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec(v___y_6422_);
lean_dec_ref(v___y_6421_);
return v_res_6427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6428_, lean_object* v_macroStack_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_){
_start:
{
lean_object* v___x_6437_; 
v___x_6437_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6428_, v_macroStack_6429_, v___y_6434_);
return v___x_6437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6438_, lean_object* v_macroStack_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v_res_6447_; 
v_res_6447_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6438_, v_macroStack_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
lean_dec(v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec(v___y_6443_);
lean_dec_ref(v___y_6442_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
return v_res_6447_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6454_ = lean_box(0);
v___x_6455_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6456_ = l_Lean_mkConst(v___x_6455_, v___x_6454_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; 
v___x_6461_ = lean_box(0);
v___x_6462_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6463_ = l_Lean_mkConst(v___x_6462_, v___x_6461_);
return v___x_6463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_){
_start:
{
lean_object* v___x_6470_; 
v___x_6470_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6464_, v_a_6466_);
if (lean_obj_tag(v___x_6470_) == 0)
{
lean_object* v_a_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6538_; 
v_a_6471_ = lean_ctor_get(v___x_6470_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6470_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6473_ = v___x_6470_;
v_isShared_6474_ = v_isSharedCheck_6538_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_a_6471_);
lean_dec(v___x_6470_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6538_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v___x_6480_; uint8_t v___x_6481_; 
v___x_6480_ = l_Lean_Expr_cleanupAnnotations(v_a_6471_);
v___x_6481_ = l_Lean_Expr_isApp(v___x_6480_);
if (v___x_6481_ == 0)
{
lean_dec_ref(v___x_6480_);
goto v___jp_6475_;
}
else
{
lean_object* v_arg_6482_; lean_object* v___x_6483_; uint8_t v___x_6484_; 
v_arg_6482_ = lean_ctor_get(v___x_6480_, 1);
lean_inc_ref(v_arg_6482_);
v___x_6483_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6480_);
v___x_6484_ = l_Lean_Expr_isApp(v___x_6483_);
if (v___x_6484_ == 0)
{
lean_dec_ref(v___x_6483_);
lean_dec_ref(v_arg_6482_);
goto v___jp_6475_;
}
else
{
lean_object* v_arg_6485_; lean_object* v___x_6486_; uint8_t v___x_6487_; 
v_arg_6485_ = lean_ctor_get(v___x_6483_, 1);
lean_inc_ref(v_arg_6485_);
v___x_6486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6483_);
v___x_6487_ = l_Lean_Expr_isApp(v___x_6486_);
if (v___x_6487_ == 0)
{
lean_dec_ref(v___x_6486_);
lean_dec_ref(v_arg_6485_);
lean_dec_ref(v_arg_6482_);
goto v___jp_6475_;
}
else
{
lean_object* v_arg_6488_; lean_object* v___x_6489_; uint8_t v___x_6490_; 
v_arg_6488_ = lean_ctor_get(v___x_6486_, 1);
lean_inc_ref(v_arg_6488_);
v___x_6489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6486_);
v___x_6490_ = l_Lean_Expr_isApp(v___x_6489_);
if (v___x_6490_ == 0)
{
lean_dec_ref(v___x_6489_);
lean_dec_ref(v_arg_6488_);
lean_dec_ref(v_arg_6485_);
lean_dec_ref(v_arg_6482_);
goto v___jp_6475_;
}
else
{
lean_object* v___x_6491_; lean_object* v___x_6492_; uint8_t v___x_6493_; 
v___x_6491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6489_);
v___x_6492_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6493_ = l_Lean_Expr_isConstOf(v___x_6491_, v___x_6492_);
lean_dec_ref(v___x_6491_);
if (v___x_6493_ == 0)
{
lean_dec_ref(v_arg_6488_);
lean_dec_ref(v_arg_6485_);
lean_dec_ref(v_arg_6482_);
goto v___jp_6475_;
}
else
{
lean_object* v___x_6494_; lean_object* v___x_6495_; 
lean_del_object(v___x_6473_);
v___x_6494_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6495_ = l_Lean_Meta_isExprDefEq(v_arg_6488_, v___x_6494_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_);
if (lean_obj_tag(v___x_6495_) == 0)
{
lean_object* v_a_6496_; lean_object* v___x_6498_; uint8_t v_isShared_6499_; uint8_t v_isSharedCheck_6529_; 
v_a_6496_ = lean_ctor_get(v___x_6495_, 0);
v_isSharedCheck_6529_ = !lean_is_exclusive(v___x_6495_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6498_ = v___x_6495_;
v_isShared_6499_ = v_isSharedCheck_6529_;
goto v_resetjp_6497_;
}
else
{
lean_inc(v_a_6496_);
lean_dec(v___x_6495_);
v___x_6498_ = lean_box(0);
v_isShared_6499_ = v_isSharedCheck_6529_;
goto v_resetjp_6497_;
}
v_resetjp_6497_:
{
uint8_t v___x_6500_; 
v___x_6500_ = lean_unbox(v_a_6496_);
lean_dec(v_a_6496_);
if (v___x_6500_ == 0)
{
lean_object* v___x_6501_; lean_object* v___x_6503_; 
lean_dec_ref(v_arg_6485_);
lean_dec_ref(v_arg_6482_);
v___x_6501_ = lean_box(0);
if (v_isShared_6499_ == 0)
{
lean_ctor_set(v___x_6498_, 0, v___x_6501_);
v___x_6503_ = v___x_6498_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v___x_6501_);
v___x_6503_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
return v___x_6503_;
}
}
else
{
lean_object* v___x_6505_; lean_object* v___x_6506_; 
lean_del_object(v___x_6498_);
v___x_6505_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6506_ = l_Lean_Meta_isExprDefEq(v_arg_6482_, v___x_6505_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_);
if (lean_obj_tag(v___x_6506_) == 0)
{
lean_object* v_a_6507_; lean_object* v___x_6509_; uint8_t v_isShared_6510_; uint8_t v_isSharedCheck_6520_; 
v_a_6507_ = lean_ctor_get(v___x_6506_, 0);
v_isSharedCheck_6520_ = !lean_is_exclusive(v___x_6506_);
if (v_isSharedCheck_6520_ == 0)
{
v___x_6509_ = v___x_6506_;
v_isShared_6510_ = v_isSharedCheck_6520_;
goto v_resetjp_6508_;
}
else
{
lean_inc(v_a_6507_);
lean_dec(v___x_6506_);
v___x_6509_ = lean_box(0);
v_isShared_6510_ = v_isSharedCheck_6520_;
goto v_resetjp_6508_;
}
v_resetjp_6508_:
{
uint8_t v___x_6511_; 
v___x_6511_ = lean_unbox(v_a_6507_);
lean_dec(v_a_6507_);
if (v___x_6511_ == 0)
{
lean_object* v___x_6512_; lean_object* v___x_6514_; 
lean_dec_ref(v_arg_6485_);
v___x_6512_ = lean_box(0);
if (v_isShared_6510_ == 0)
{
lean_ctor_set(v___x_6509_, 0, v___x_6512_);
v___x_6514_ = v___x_6509_;
goto v_reusejp_6513_;
}
else
{
lean_object* v_reuseFailAlloc_6515_; 
v_reuseFailAlloc_6515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6515_, 0, v___x_6512_);
v___x_6514_ = v_reuseFailAlloc_6515_;
goto v_reusejp_6513_;
}
v_reusejp_6513_:
{
return v___x_6514_;
}
}
else
{
lean_object* v___x_6516_; lean_object* v___x_6518_; 
v___x_6516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6516_, 0, v_arg_6485_);
if (v_isShared_6510_ == 0)
{
lean_ctor_set(v___x_6509_, 0, v___x_6516_);
v___x_6518_ = v___x_6509_;
goto v_reusejp_6517_;
}
else
{
lean_object* v_reuseFailAlloc_6519_; 
v_reuseFailAlloc_6519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6519_, 0, v___x_6516_);
v___x_6518_ = v_reuseFailAlloc_6519_;
goto v_reusejp_6517_;
}
v_reusejp_6517_:
{
return v___x_6518_;
}
}
}
}
else
{
lean_object* v_a_6521_; lean_object* v___x_6523_; uint8_t v_isShared_6524_; uint8_t v_isSharedCheck_6528_; 
lean_dec_ref(v_arg_6485_);
v_a_6521_ = lean_ctor_get(v___x_6506_, 0);
v_isSharedCheck_6528_ = !lean_is_exclusive(v___x_6506_);
if (v_isSharedCheck_6528_ == 0)
{
v___x_6523_ = v___x_6506_;
v_isShared_6524_ = v_isSharedCheck_6528_;
goto v_resetjp_6522_;
}
else
{
lean_inc(v_a_6521_);
lean_dec(v___x_6506_);
v___x_6523_ = lean_box(0);
v_isShared_6524_ = v_isSharedCheck_6528_;
goto v_resetjp_6522_;
}
v_resetjp_6522_:
{
lean_object* v___x_6526_; 
if (v_isShared_6524_ == 0)
{
v___x_6526_ = v___x_6523_;
goto v_reusejp_6525_;
}
else
{
lean_object* v_reuseFailAlloc_6527_; 
v_reuseFailAlloc_6527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
v___x_6526_ = v_reuseFailAlloc_6527_;
goto v_reusejp_6525_;
}
v_reusejp_6525_:
{
return v___x_6526_;
}
}
}
}
}
}
else
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6537_; 
lean_dec_ref(v_arg_6485_);
lean_dec_ref(v_arg_6482_);
v_a_6530_ = lean_ctor_get(v___x_6495_, 0);
v_isSharedCheck_6537_ = !lean_is_exclusive(v___x_6495_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6532_ = v___x_6495_;
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6495_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6535_; 
if (v_isShared_6533_ == 0)
{
v___x_6535_ = v___x_6532_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
v___x_6535_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
return v___x_6535_;
}
}
}
}
}
}
}
}
v___jp_6475_:
{
lean_object* v___x_6476_; lean_object* v___x_6478_; 
v___x_6476_ = lean_box(0);
if (v_isShared_6474_ == 0)
{
lean_ctor_set(v___x_6473_, 0, v___x_6476_);
v___x_6478_ = v___x_6473_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v___x_6476_);
v___x_6478_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
return v___x_6478_;
}
}
}
}
else
{
lean_object* v_a_6539_; lean_object* v___x_6541_; uint8_t v_isShared_6542_; uint8_t v_isSharedCheck_6546_; 
v_a_6539_ = lean_ctor_get(v___x_6470_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___x_6470_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6541_ = v___x_6470_;
v_isShared_6542_ = v_isSharedCheck_6546_;
goto v_resetjp_6540_;
}
else
{
lean_inc(v_a_6539_);
lean_dec(v___x_6470_);
v___x_6541_ = lean_box(0);
v_isShared_6542_ = v_isSharedCheck_6546_;
goto v_resetjp_6540_;
}
v_resetjp_6540_:
{
lean_object* v___x_6544_; 
if (v_isShared_6542_ == 0)
{
v___x_6544_ = v___x_6541_;
goto v_reusejp_6543_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_a_6539_);
v___x_6544_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6543_;
}
v_reusejp_6543_:
{
return v___x_6544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6547_, lean_object* v_a_6548_, lean_object* v_a_6549_, lean_object* v_a_6550_, lean_object* v_a_6551_, lean_object* v_a_6552_){
_start:
{
lean_object* v_res_6553_; 
v_res_6553_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6547_, v_a_6548_, v_a_6549_, v_a_6550_, v_a_6551_);
lean_dec(v_a_6551_);
lean_dec_ref(v_a_6550_);
lean_dec(v_a_6549_);
lean_dec_ref(v_a_6548_);
return v_res_6553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6554_, lean_object* v_maxFVars_x3f_6555_, lean_object* v_k_6556_, uint8_t v_cleanupAnnotations_6557_, uint8_t v_whnfType_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_){
_start:
{
lean_object* v___f_6566_; lean_object* v___x_6567_; 
lean_inc(v___y_6560_);
lean_inc_ref(v___y_6559_);
v___f_6566_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6566_, 0, v_k_6556_);
lean_closure_set(v___f_6566_, 1, v___y_6559_);
lean_closure_set(v___f_6566_, 2, v___y_6560_);
v___x_6567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6554_, v_maxFVars_x3f_6555_, v___f_6566_, v_cleanupAnnotations_6557_, v_whnfType_6558_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6567_) == 0)
{
return v___x_6567_;
}
else
{
lean_object* v_a_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6575_; 
v_a_6568_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6570_ = v___x_6567_;
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_a_6568_);
lean_dec(v___x_6567_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v___x_6573_; 
if (v_isShared_6571_ == 0)
{
v___x_6573_ = v___x_6570_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v_a_6568_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6576_, lean_object* v_maxFVars_x3f_6577_, lean_object* v_k_6578_, lean_object* v_cleanupAnnotations_6579_, lean_object* v_whnfType_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_, lean_object* v___y_6584_, lean_object* v___y_6585_, lean_object* v___y_6586_, lean_object* v___y_6587_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6588_; uint8_t v_whnfType_boxed_6589_; lean_object* v_res_6590_; 
v_cleanupAnnotations_boxed_6588_ = lean_unbox(v_cleanupAnnotations_6579_);
v_whnfType_boxed_6589_ = lean_unbox(v_whnfType_6580_);
v_res_6590_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6576_, v_maxFVars_x3f_6577_, v_k_6578_, v_cleanupAnnotations_boxed_6588_, v_whnfType_boxed_6589_, v___y_6581_, v___y_6582_, v___y_6583_, v___y_6584_, v___y_6585_, v___y_6586_);
lean_dec(v___y_6586_);
lean_dec_ref(v___y_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec(v___y_6582_);
lean_dec_ref(v___y_6581_);
return v_res_6590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6591_, lean_object* v_type_6592_, lean_object* v_maxFVars_x3f_6593_, lean_object* v_k_6594_, uint8_t v_cleanupAnnotations_6595_, uint8_t v_whnfType_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_){
_start:
{
lean_object* v___x_6604_; 
v___x_6604_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6592_, v_maxFVars_x3f_6593_, v_k_6594_, v_cleanupAnnotations_6595_, v_whnfType_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_);
return v___x_6604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6605_, lean_object* v_type_6606_, lean_object* v_maxFVars_x3f_6607_, lean_object* v_k_6608_, lean_object* v_cleanupAnnotations_6609_, lean_object* v_whnfType_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6618_; uint8_t v_whnfType_boxed_6619_; lean_object* v_res_6620_; 
v_cleanupAnnotations_boxed_6618_ = lean_unbox(v_cleanupAnnotations_6609_);
v_whnfType_boxed_6619_ = lean_unbox(v_whnfType_6610_);
v_res_6620_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6605_, v_type_6606_, v_maxFVars_x3f_6607_, v_k_6608_, v_cleanupAnnotations_boxed_6618_, v_whnfType_boxed_6619_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_);
lean_dec(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v___y_6613_);
lean_dec(v___y_6612_);
lean_dec_ref(v___y_6611_);
return v_res_6620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6621_, lean_object* v_x_6622_, lean_object* v___y_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_){
_start:
{
lean_object* v_keyedConfig_6630_; uint8_t v_trackZetaDelta_6631_; lean_object* v_zetaDeltaSet_6632_; lean_object* v_localInstances_6633_; lean_object* v_defEqCtx_x3f_6634_; lean_object* v_synthPendingDepth_6635_; lean_object* v_canUnfold_x3f_6636_; uint8_t v_univApprox_6637_; uint8_t v_inTypeClassResolution_6638_; uint8_t v_cacheInferType_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v_keyedConfig_6630_ = lean_ctor_get(v___y_6625_, 0);
v_trackZetaDelta_6631_ = lean_ctor_get_uint8(v___y_6625_, sizeof(void*)*7);
v_zetaDeltaSet_6632_ = lean_ctor_get(v___y_6625_, 1);
v_localInstances_6633_ = lean_ctor_get(v___y_6625_, 3);
v_defEqCtx_x3f_6634_ = lean_ctor_get(v___y_6625_, 4);
v_synthPendingDepth_6635_ = lean_ctor_get(v___y_6625_, 5);
v_canUnfold_x3f_6636_ = lean_ctor_get(v___y_6625_, 6);
v_univApprox_6637_ = lean_ctor_get_uint8(v___y_6625_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6638_ = lean_ctor_get_uint8(v___y_6625_, sizeof(void*)*7 + 2);
v_cacheInferType_6639_ = lean_ctor_get_uint8(v___y_6625_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_6636_);
lean_inc(v_synthPendingDepth_6635_);
lean_inc(v_defEqCtx_x3f_6634_);
lean_inc_ref(v_localInstances_6633_);
lean_inc(v_zetaDeltaSet_6632_);
lean_inc_ref(v_keyedConfig_6630_);
v___x_6640_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6640_, 0, v_keyedConfig_6630_);
lean_ctor_set(v___x_6640_, 1, v_zetaDeltaSet_6632_);
lean_ctor_set(v___x_6640_, 2, v_lctx_6621_);
lean_ctor_set(v___x_6640_, 3, v_localInstances_6633_);
lean_ctor_set(v___x_6640_, 4, v_defEqCtx_x3f_6634_);
lean_ctor_set(v___x_6640_, 5, v_synthPendingDepth_6635_);
lean_ctor_set(v___x_6640_, 6, v_canUnfold_x3f_6636_);
lean_ctor_set_uint8(v___x_6640_, sizeof(void*)*7, v_trackZetaDelta_6631_);
lean_ctor_set_uint8(v___x_6640_, sizeof(void*)*7 + 1, v_univApprox_6637_);
lean_ctor_set_uint8(v___x_6640_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6638_);
lean_ctor_set_uint8(v___x_6640_, sizeof(void*)*7 + 3, v_cacheInferType_6639_);
lean_inc(v___y_6628_);
lean_inc_ref(v___y_6627_);
lean_inc(v___y_6626_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
v___x_6641_ = lean_apply_7(v_x_6622_, v___y_6623_, v___y_6624_, v___x_6640_, v___y_6626_, v___y_6627_, v___y_6628_, lean_box(0));
if (lean_obj_tag(v___x_6641_) == 0)
{
lean_object* v_a_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6649_; 
v_a_6642_ = lean_ctor_get(v___x_6641_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v___x_6641_);
if (v_isSharedCheck_6649_ == 0)
{
v___x_6644_ = v___x_6641_;
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_a_6642_);
lean_dec(v___x_6641_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v___x_6647_; 
if (v_isShared_6645_ == 0)
{
v___x_6647_ = v___x_6644_;
goto v_reusejp_6646_;
}
else
{
lean_object* v_reuseFailAlloc_6648_; 
v_reuseFailAlloc_6648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
v___x_6647_ = v_reuseFailAlloc_6648_;
goto v_reusejp_6646_;
}
v_reusejp_6646_:
{
return v___x_6647_;
}
}
}
else
{
return v___x_6641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6650_, lean_object* v_x_6651_, lean_object* v___y_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_){
_start:
{
lean_object* v_res_6659_; 
v_res_6659_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6650_, v_x_6651_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_, v___y_6656_, v___y_6657_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec(v___y_6655_);
lean_dec_ref(v___y_6654_);
lean_dec(v___y_6653_);
lean_dec_ref(v___y_6652_);
return v_res_6659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6660_, lean_object* v_lctx_6661_, lean_object* v_x_6662_, lean_object* v___y_6663_, lean_object* v___y_6664_, lean_object* v___y_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_){
_start:
{
lean_object* v___x_6670_; 
v___x_6670_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6661_, v_x_6662_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_, v___y_6668_);
return v___x_6670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6671_, lean_object* v_lctx_6672_, lean_object* v_x_6673_, lean_object* v___y_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_){
_start:
{
lean_object* v_res_6681_; 
v_res_6681_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6671_, v_lctx_6672_, v_x_6673_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_, v___y_6679_);
lean_dec(v___y_6679_);
lean_dec_ref(v___y_6678_);
lean_dec(v___y_6677_);
lean_dec_ref(v___y_6676_);
lean_dec(v___y_6675_);
lean_dec_ref(v___y_6674_);
return v_res_6681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6698_, lean_object* v___x_6699_, lean_object* v_wfRel_6700_, lean_object* v_x_6701_, lean_object* v_type_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_, lean_object* v___y_6708_){
_start:
{
lean_object* v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; 
v___x_6710_ = lean_unsigned_to_nat(0u);
v___x_6711_ = lean_array_get_borrowed(v___x_6698_, v_x_6701_, v___x_6710_);
v___x_6712_ = l_Lean_Expr_fvarId_x21(v___x_6711_);
v___x_6713_ = l_Lean_FVarId_getUserName___redArg(v___x_6712_, v___y_6705_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6713_) == 0)
{
lean_object* v_a_6714_; lean_object* v___x_6715_; 
v_a_6714_ = lean_ctor_get(v___x_6713_, 0);
lean_inc(v_a_6714_);
lean_dec_ref(v___x_6713_);
lean_inc(v___y_6708_);
lean_inc_ref(v___y_6707_);
lean_inc(v___y_6706_);
lean_inc_ref(v___y_6705_);
lean_inc(v___x_6711_);
v___x_6715_ = lean_infer_type(v___x_6711_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6715_) == 0)
{
lean_object* v_a_6716_; lean_object* v___x_6717_; 
v_a_6716_ = lean_ctor_get(v___x_6715_, 0);
lean_inc(v_a_6716_);
lean_dec_ref(v___x_6715_);
lean_inc(v_a_6716_);
v___x_6717_ = l_Lean_Meta_getLevel(v_a_6716_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6717_) == 0)
{
lean_object* v_a_6718_; lean_object* v___x_6719_; 
v_a_6718_ = lean_ctor_get(v___x_6717_, 0);
lean_inc(v_a_6718_);
lean_dec_ref(v___x_6717_);
lean_inc_ref(v_type_6702_);
v___x_6719_ = l_Lean_Meta_getLevel(v_type_6702_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6719_) == 0)
{
lean_object* v_a_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; uint8_t v___x_6723_; uint8_t v___x_6724_; uint8_t v___x_6725_; lean_object* v___x_6726_; 
v_a_6720_ = lean_ctor_get(v___x_6719_, 0);
lean_inc(v_a_6720_);
lean_dec_ref(v___x_6719_);
v___x_6721_ = lean_mk_empty_array_with_capacity(v___x_6699_);
lean_inc(v___x_6711_);
lean_inc_ref(v___x_6721_);
v___x_6722_ = lean_array_push(v___x_6721_, v___x_6711_);
v___x_6723_ = 0;
v___x_6724_ = 1;
v___x_6725_ = 1;
v___x_6726_ = l_Lean_Meta_mkLambdaFVars(v___x_6722_, v_type_6702_, v___x_6723_, v___x_6724_, v___x_6723_, v___x_6724_, v___x_6725_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
lean_dec_ref(v___x_6722_);
if (lean_obj_tag(v___x_6726_) == 0)
{
lean_object* v_a_6727_; lean_object* v___x_6728_; 
v_a_6727_ = lean_ctor_get(v___x_6726_, 0);
lean_inc(v_a_6727_);
lean_dec_ref(v___x_6726_);
lean_inc_ref(v_wfRel_6700_);
v___x_6728_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6700_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6728_) == 0)
{
lean_object* v_a_6729_; lean_object* v___x_6731_; uint8_t v_isShared_6732_; uint8_t v_isSharedCheck_6773_; 
v_a_6729_ = lean_ctor_get(v___x_6728_, 0);
v_isSharedCheck_6773_ = !lean_is_exclusive(v___x_6728_);
if (v_isSharedCheck_6773_ == 0)
{
v___x_6731_ = v___x_6728_;
v_isShared_6732_ = v_isSharedCheck_6773_;
goto v_resetjp_6730_;
}
else
{
lean_inc(v_a_6729_);
lean_dec(v___x_6728_);
v___x_6731_ = lean_box(0);
v_isShared_6732_ = v_isSharedCheck_6773_;
goto v_resetjp_6730_;
}
v_resetjp_6730_:
{
if (lean_obj_tag(v_a_6729_) == 1)
{
lean_object* v_val_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6742_; 
lean_dec_ref(v___x_6721_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_val_6733_ = lean_ctor_get(v_a_6729_, 0);
lean_inc(v_val_6733_);
lean_dec_ref(v_a_6729_);
v___x_6734_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6735_ = lean_box(0);
v___x_6736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6736_, 0, v_a_6720_);
lean_ctor_set(v___x_6736_, 1, v___x_6735_);
v___x_6737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6737_, 0, v_a_6718_);
lean_ctor_set(v___x_6737_, 1, v___x_6736_);
v___x_6738_ = l_Lean_mkConst(v___x_6734_, v___x_6737_);
v___x_6739_ = l_Lean_mkApp3(v___x_6738_, v_a_6716_, v_a_6727_, v_val_6733_);
v___x_6740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6740_, 0, v___x_6739_);
lean_ctor_set(v___x_6740_, 1, v_a_6714_);
if (v_isShared_6732_ == 0)
{
lean_ctor_set(v___x_6731_, 0, v___x_6740_);
v___x_6742_ = v___x_6731_;
goto v_reusejp_6741_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6740_);
v___x_6742_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6741_;
}
v_reusejp_6741_:
{
return v___x_6742_;
}
}
else
{
lean_object* v___x_6744_; lean_object* v___x_6745_; lean_object* v___x_6746_; lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; 
lean_del_object(v___x_6731_);
lean_dec(v_a_6729_);
v___x_6744_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6700_);
v___x_6745_ = l_Lean_mkProj(v___x_6744_, v___x_6710_, v_wfRel_6700_);
v___x_6746_ = l_Lean_mkProj(v___x_6744_, v___x_6699_, v_wfRel_6700_);
v___x_6747_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6748_ = lean_array_push(v___x_6721_, v___x_6746_);
v___x_6749_ = l_Lean_Meta_mkAppM(v___x_6747_, v___x_6748_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
if (lean_obj_tag(v___x_6749_) == 0)
{
lean_object* v_a_6750_; lean_object* v___x_6752_; uint8_t v_isShared_6753_; uint8_t v_isSharedCheck_6764_; 
v_a_6750_ = lean_ctor_get(v___x_6749_, 0);
v_isSharedCheck_6764_ = !lean_is_exclusive(v___x_6749_);
if (v_isSharedCheck_6764_ == 0)
{
v___x_6752_ = v___x_6749_;
v_isShared_6753_ = v_isSharedCheck_6764_;
goto v_resetjp_6751_;
}
else
{
lean_inc(v_a_6750_);
lean_dec(v___x_6749_);
v___x_6752_ = lean_box(0);
v_isShared_6753_ = v_isSharedCheck_6764_;
goto v_resetjp_6751_;
}
v_resetjp_6751_:
{
lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6762_; 
v___x_6754_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6755_ = lean_box(0);
v___x_6756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6756_, 0, v_a_6720_);
lean_ctor_set(v___x_6756_, 1, v___x_6755_);
v___x_6757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6757_, 0, v_a_6718_);
lean_ctor_set(v___x_6757_, 1, v___x_6756_);
v___x_6758_ = l_Lean_mkConst(v___x_6754_, v___x_6757_);
v___x_6759_ = l_Lean_mkApp4(v___x_6758_, v_a_6716_, v_a_6727_, v___x_6745_, v_a_6750_);
v___x_6760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6760_, 0, v___x_6759_);
lean_ctor_set(v___x_6760_, 1, v_a_6714_);
if (v_isShared_6753_ == 0)
{
lean_ctor_set(v___x_6752_, 0, v___x_6760_);
v___x_6762_ = v___x_6752_;
goto v_reusejp_6761_;
}
else
{
lean_object* v_reuseFailAlloc_6763_; 
v_reuseFailAlloc_6763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6763_, 0, v___x_6760_);
v___x_6762_ = v_reuseFailAlloc_6763_;
goto v_reusejp_6761_;
}
v_reusejp_6761_:
{
return v___x_6762_;
}
}
}
else
{
lean_object* v_a_6765_; lean_object* v___x_6767_; uint8_t v_isShared_6768_; uint8_t v_isSharedCheck_6772_; 
lean_dec_ref(v___x_6745_);
lean_dec(v_a_6727_);
lean_dec(v_a_6720_);
lean_dec(v_a_6718_);
lean_dec(v_a_6716_);
lean_dec(v_a_6714_);
v_a_6765_ = lean_ctor_get(v___x_6749_, 0);
v_isSharedCheck_6772_ = !lean_is_exclusive(v___x_6749_);
if (v_isSharedCheck_6772_ == 0)
{
v___x_6767_ = v___x_6749_;
v_isShared_6768_ = v_isSharedCheck_6772_;
goto v_resetjp_6766_;
}
else
{
lean_inc(v_a_6765_);
lean_dec(v___x_6749_);
v___x_6767_ = lean_box(0);
v_isShared_6768_ = v_isSharedCheck_6772_;
goto v_resetjp_6766_;
}
v_resetjp_6766_:
{
lean_object* v___x_6770_; 
if (v_isShared_6768_ == 0)
{
v___x_6770_ = v___x_6767_;
goto v_reusejp_6769_;
}
else
{
lean_object* v_reuseFailAlloc_6771_; 
v_reuseFailAlloc_6771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6765_);
v___x_6770_ = v_reuseFailAlloc_6771_;
goto v_reusejp_6769_;
}
v_reusejp_6769_:
{
return v___x_6770_;
}
}
}
}
}
}
else
{
lean_object* v_a_6774_; lean_object* v___x_6776_; uint8_t v_isShared_6777_; uint8_t v_isSharedCheck_6781_; 
lean_dec(v_a_6727_);
lean_dec_ref(v___x_6721_);
lean_dec(v_a_6720_);
lean_dec(v_a_6718_);
lean_dec(v_a_6716_);
lean_dec(v_a_6714_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6774_ = lean_ctor_get(v___x_6728_, 0);
v_isSharedCheck_6781_ = !lean_is_exclusive(v___x_6728_);
if (v_isSharedCheck_6781_ == 0)
{
v___x_6776_ = v___x_6728_;
v_isShared_6777_ = v_isSharedCheck_6781_;
goto v_resetjp_6775_;
}
else
{
lean_inc(v_a_6774_);
lean_dec(v___x_6728_);
v___x_6776_ = lean_box(0);
v_isShared_6777_ = v_isSharedCheck_6781_;
goto v_resetjp_6775_;
}
v_resetjp_6775_:
{
lean_object* v___x_6779_; 
if (v_isShared_6777_ == 0)
{
v___x_6779_ = v___x_6776_;
goto v_reusejp_6778_;
}
else
{
lean_object* v_reuseFailAlloc_6780_; 
v_reuseFailAlloc_6780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6780_, 0, v_a_6774_);
v___x_6779_ = v_reuseFailAlloc_6780_;
goto v_reusejp_6778_;
}
v_reusejp_6778_:
{
return v___x_6779_;
}
}
}
}
else
{
lean_object* v_a_6782_; lean_object* v___x_6784_; uint8_t v_isShared_6785_; uint8_t v_isSharedCheck_6789_; 
lean_dec_ref(v___x_6721_);
lean_dec(v_a_6720_);
lean_dec(v_a_6718_);
lean_dec(v_a_6716_);
lean_dec(v_a_6714_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6782_ = lean_ctor_get(v___x_6726_, 0);
v_isSharedCheck_6789_ = !lean_is_exclusive(v___x_6726_);
if (v_isSharedCheck_6789_ == 0)
{
v___x_6784_ = v___x_6726_;
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
else
{
lean_inc(v_a_6782_);
lean_dec(v___x_6726_);
v___x_6784_ = lean_box(0);
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
v_resetjp_6783_:
{
lean_object* v___x_6787_; 
if (v_isShared_6785_ == 0)
{
v___x_6787_ = v___x_6784_;
goto v_reusejp_6786_;
}
else
{
lean_object* v_reuseFailAlloc_6788_; 
v_reuseFailAlloc_6788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6788_, 0, v_a_6782_);
v___x_6787_ = v_reuseFailAlloc_6788_;
goto v_reusejp_6786_;
}
v_reusejp_6786_:
{
return v___x_6787_;
}
}
}
}
else
{
lean_object* v_a_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6797_; 
lean_dec(v_a_6718_);
lean_dec(v_a_6716_);
lean_dec(v_a_6714_);
lean_dec_ref(v_type_6702_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6790_ = lean_ctor_get(v___x_6719_, 0);
v_isSharedCheck_6797_ = !lean_is_exclusive(v___x_6719_);
if (v_isSharedCheck_6797_ == 0)
{
v___x_6792_ = v___x_6719_;
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_a_6790_);
lean_dec(v___x_6719_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v___x_6795_; 
if (v_isShared_6793_ == 0)
{
v___x_6795_ = v___x_6792_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6796_; 
v_reuseFailAlloc_6796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6796_, 0, v_a_6790_);
v___x_6795_ = v_reuseFailAlloc_6796_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
return v___x_6795_;
}
}
}
}
else
{
lean_object* v_a_6798_; lean_object* v___x_6800_; uint8_t v_isShared_6801_; uint8_t v_isSharedCheck_6805_; 
lean_dec(v_a_6716_);
lean_dec(v_a_6714_);
lean_dec_ref(v_type_6702_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6798_ = lean_ctor_get(v___x_6717_, 0);
v_isSharedCheck_6805_ = !lean_is_exclusive(v___x_6717_);
if (v_isSharedCheck_6805_ == 0)
{
v___x_6800_ = v___x_6717_;
v_isShared_6801_ = v_isSharedCheck_6805_;
goto v_resetjp_6799_;
}
else
{
lean_inc(v_a_6798_);
lean_dec(v___x_6717_);
v___x_6800_ = lean_box(0);
v_isShared_6801_ = v_isSharedCheck_6805_;
goto v_resetjp_6799_;
}
v_resetjp_6799_:
{
lean_object* v___x_6803_; 
if (v_isShared_6801_ == 0)
{
v___x_6803_ = v___x_6800_;
goto v_reusejp_6802_;
}
else
{
lean_object* v_reuseFailAlloc_6804_; 
v_reuseFailAlloc_6804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6804_, 0, v_a_6798_);
v___x_6803_ = v_reuseFailAlloc_6804_;
goto v_reusejp_6802_;
}
v_reusejp_6802_:
{
return v___x_6803_;
}
}
}
}
else
{
lean_object* v_a_6806_; lean_object* v___x_6808_; uint8_t v_isShared_6809_; uint8_t v_isSharedCheck_6813_; 
lean_dec(v_a_6714_);
lean_dec_ref(v_type_6702_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6806_ = lean_ctor_get(v___x_6715_, 0);
v_isSharedCheck_6813_ = !lean_is_exclusive(v___x_6715_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6808_ = v___x_6715_;
v_isShared_6809_ = v_isSharedCheck_6813_;
goto v_resetjp_6807_;
}
else
{
lean_inc(v_a_6806_);
lean_dec(v___x_6715_);
v___x_6808_ = lean_box(0);
v_isShared_6809_ = v_isSharedCheck_6813_;
goto v_resetjp_6807_;
}
v_resetjp_6807_:
{
lean_object* v___x_6811_; 
if (v_isShared_6809_ == 0)
{
v___x_6811_ = v___x_6808_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6812_; 
v_reuseFailAlloc_6812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6812_, 0, v_a_6806_);
v___x_6811_ = v_reuseFailAlloc_6812_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
return v___x_6811_;
}
}
}
}
else
{
lean_object* v_a_6814_; lean_object* v___x_6816_; uint8_t v_isShared_6817_; uint8_t v_isSharedCheck_6821_; 
lean_dec_ref(v_type_6702_);
lean_dec_ref(v_wfRel_6700_);
lean_dec(v___x_6699_);
v_a_6814_ = lean_ctor_get(v___x_6713_, 0);
v_isSharedCheck_6821_ = !lean_is_exclusive(v___x_6713_);
if (v_isSharedCheck_6821_ == 0)
{
v___x_6816_ = v___x_6713_;
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
else
{
lean_inc(v_a_6814_);
lean_dec(v___x_6713_);
v___x_6816_ = lean_box(0);
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
v_resetjp_6815_:
{
lean_object* v___x_6819_; 
if (v_isShared_6817_ == 0)
{
v___x_6819_ = v___x_6816_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v_a_6814_);
v___x_6819_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
return v___x_6819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6822_, lean_object* v___x_6823_, lean_object* v_wfRel_6824_, lean_object* v_x_6825_, lean_object* v_type_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6822_, v___x_6823_, v_wfRel_6824_, v_x_6825_, v_type_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec_ref(v_x_6825_);
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6835_, lean_object* v_declName_6836_, lean_object* v_x_6837_, lean_object* v_F_6838_, lean_object* v_val_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_){
_start:
{
lean_object* v___x_6847_; lean_object* v___x_6848_; lean_object* v___x_6849_; 
v___x_6847_ = lean_array_get_size(v_prefixArgs_6835_);
v___x_6848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6848_, 0, v_declName_6836_);
lean_closure_set(v___x_6848_, 1, v___x_6847_);
v___x_6849_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6837_, v_F_6838_, v_val_6839_, v___x_6848_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_);
return v___x_6849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6850_, lean_object* v_declName_6851_, lean_object* v_x_6852_, lean_object* v_F_6853_, lean_object* v_val_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_){
_start:
{
lean_object* v_res_6862_; 
v_res_6862_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6850_, v_declName_6851_, v_x_6852_, v_F_6853_, v_val_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_);
lean_dec(v___y_6860_);
lean_dec_ref(v___y_6859_);
lean_dec(v___y_6858_);
lean_dec_ref(v___y_6857_);
lean_dec(v___y_6856_);
lean_dec_ref(v___y_6855_);
lean_dec_ref(v_prefixArgs_6850_);
return v_res_6862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6863_, lean_object* v___x_6864_, lean_object* v___x_6865_, lean_object* v___f_6866_, lean_object* v_funNames_6867_, lean_object* v_argsPacker_6868_, lean_object* v_decrTactics_6869_, uint8_t v___x_6870_, lean_object* v_fst_6871_, lean_object* v_prefixArgs_6872_, lean_object* v___y_6873_, lean_object* v___y_6874_, lean_object* v___y_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_){
_start:
{
lean_object* v___x_6880_; 
lean_inc_ref(v___x_6864_);
lean_inc_ref(v___x_6863_);
v___x_6880_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6863_, v___x_6864_, v___x_6865_, v___f_6866_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
if (lean_obj_tag(v___x_6880_) == 0)
{
lean_object* v_a_6881_; lean_object* v___x_6882_; 
v_a_6881_ = lean_ctor_get(v___x_6880_, 0);
lean_inc(v_a_6881_);
lean_dec_ref(v___x_6880_);
v___x_6882_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6867_, v_argsPacker_6868_, v_decrTactics_6869_, v_a_6881_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
if (lean_obj_tag(v___x_6882_) == 0)
{
lean_object* v_a_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; uint8_t v___x_6888_; uint8_t v___x_6889_; lean_object* v___x_6890_; 
v_a_6883_ = lean_ctor_get(v___x_6882_, 0);
lean_inc(v_a_6883_);
lean_dec_ref(v___x_6882_);
v___x_6884_ = lean_unsigned_to_nat(2u);
v___x_6885_ = lean_mk_empty_array_with_capacity(v___x_6884_);
v___x_6886_ = lean_array_push(v___x_6885_, v___x_6863_);
v___x_6887_ = lean_array_push(v___x_6886_, v___x_6864_);
v___x_6888_ = 1;
v___x_6889_ = 1;
v___x_6890_ = l_Lean_Meta_mkLambdaFVars(v___x_6887_, v_a_6883_, v___x_6870_, v___x_6888_, v___x_6870_, v___x_6888_, v___x_6889_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
lean_dec_ref(v___x_6887_);
if (lean_obj_tag(v___x_6890_) == 0)
{
lean_object* v_a_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; 
v_a_6891_ = lean_ctor_get(v___x_6890_, 0);
lean_inc(v_a_6891_);
lean_dec_ref(v___x_6890_);
v___x_6892_ = l_Lean_Expr_app___override(v_fst_6871_, v_a_6891_);
v___x_6893_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6872_, v___x_6892_, v___x_6870_, v___x_6888_, v___x_6870_, v___x_6888_, v___x_6889_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
return v___x_6893_;
}
else
{
lean_dec_ref(v_fst_6871_);
return v___x_6890_;
}
}
else
{
lean_dec_ref(v_fst_6871_);
lean_dec_ref(v___x_6864_);
lean_dec_ref(v___x_6863_);
return v___x_6882_;
}
}
else
{
lean_dec_ref(v_fst_6871_);
lean_dec_ref(v_decrTactics_6869_);
lean_dec_ref(v_argsPacker_6868_);
lean_dec_ref(v_funNames_6867_);
lean_dec_ref(v___x_6864_);
lean_dec_ref(v___x_6863_);
return v___x_6880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6894_ = _args[0];
lean_object* v___x_6895_ = _args[1];
lean_object* v___x_6896_ = _args[2];
lean_object* v___f_6897_ = _args[3];
lean_object* v_funNames_6898_ = _args[4];
lean_object* v_argsPacker_6899_ = _args[5];
lean_object* v_decrTactics_6900_ = _args[6];
lean_object* v___x_6901_ = _args[7];
lean_object* v_fst_6902_ = _args[8];
lean_object* v_prefixArgs_6903_ = _args[9];
lean_object* v___y_6904_ = _args[10];
lean_object* v___y_6905_ = _args[11];
lean_object* v___y_6906_ = _args[12];
lean_object* v___y_6907_ = _args[13];
lean_object* v___y_6908_ = _args[14];
lean_object* v___y_6909_ = _args[15];
lean_object* v___y_6910_ = _args[16];
_start:
{
uint8_t v___x_5940__boxed_6911_; lean_object* v_res_6912_; 
v___x_5940__boxed_6911_ = lean_unbox(v___x_6901_);
v_res_6912_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6894_, v___x_6895_, v___x_6896_, v___f_6897_, v_funNames_6898_, v_argsPacker_6899_, v_decrTactics_6900_, v___x_5940__boxed_6911_, v_fst_6902_, v_prefixArgs_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
lean_dec(v___y_6909_);
lean_dec_ref(v___y_6908_);
lean_dec(v___y_6907_);
lean_dec_ref(v___y_6906_);
lean_dec(v___y_6905_);
lean_dec_ref(v___y_6904_);
lean_dec_ref(v_prefixArgs_6903_);
return v_res_6912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6913_, lean_object* v_snd_6914_, lean_object* v___x_6915_, lean_object* v_prefixArgs_6916_, lean_object* v_value_6917_, lean_object* v___f_6918_, lean_object* v_funNames_6919_, lean_object* v_argsPacker_6920_, lean_object* v_decrTactics_6921_, uint8_t v___x_6922_, lean_object* v_fst_6923_, lean_object* v_xs_6924_, lean_object* v_x_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_){
_start:
{
lean_object* v_lctx_6933_; lean_object* v___x_6934_; lean_object* v___x_6935_; lean_object* v___x_6936_; lean_object* v___x_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; lean_object* v___x_6941_; lean_object* v___f_6942_; lean_object* v___x_6943_; 
v_lctx_6933_ = lean_ctor_get(v___y_6928_, 2);
v___x_6934_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_6913_);
v___x_6935_ = lean_array_get_borrowed(v___x_6913_, v_xs_6924_, v___x_6934_);
v___x_6936_ = l_Lean_Expr_fvarId_x21(v___x_6935_);
lean_inc_ref(v_lctx_6933_);
v___x_6937_ = l_Lean_LocalContext_setUserName(v_lctx_6933_, v___x_6936_, v_snd_6914_);
v___x_6938_ = lean_array_get_borrowed(v___x_6913_, v_xs_6924_, v___x_6915_);
lean_inc(v___x_6935_);
lean_inc_ref(v_prefixArgs_6916_);
v___x_6939_ = lean_array_push(v_prefixArgs_6916_, v___x_6935_);
v___x_6940_ = l_Lean_Expr_beta(v_value_6917_, v___x_6939_);
v___x_6941_ = lean_box(v___x_6922_);
lean_inc(v___x_6938_);
lean_inc(v___x_6935_);
v___f_6942_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6942_, 0, v___x_6935_);
lean_closure_set(v___f_6942_, 1, v___x_6938_);
lean_closure_set(v___f_6942_, 2, v___x_6940_);
lean_closure_set(v___f_6942_, 3, v___f_6918_);
lean_closure_set(v___f_6942_, 4, v_funNames_6919_);
lean_closure_set(v___f_6942_, 5, v_argsPacker_6920_);
lean_closure_set(v___f_6942_, 6, v_decrTactics_6921_);
lean_closure_set(v___f_6942_, 7, v___x_6941_);
lean_closure_set(v___f_6942_, 8, v_fst_6923_);
lean_closure_set(v___f_6942_, 9, v_prefixArgs_6916_);
v___x_6943_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6937_, v___f_6942_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_);
lean_dec_ref(v___y_6928_);
return v___x_6943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6944_ = _args[0];
lean_object* v_snd_6945_ = _args[1];
lean_object* v___x_6946_ = _args[2];
lean_object* v_prefixArgs_6947_ = _args[3];
lean_object* v_value_6948_ = _args[4];
lean_object* v___f_6949_ = _args[5];
lean_object* v_funNames_6950_ = _args[6];
lean_object* v_argsPacker_6951_ = _args[7];
lean_object* v_decrTactics_6952_ = _args[8];
lean_object* v___x_6953_ = _args[9];
lean_object* v_fst_6954_ = _args[10];
lean_object* v_xs_6955_ = _args[11];
lean_object* v_x_6956_ = _args[12];
lean_object* v___y_6957_ = _args[13];
lean_object* v___y_6958_ = _args[14];
lean_object* v___y_6959_ = _args[15];
lean_object* v___y_6960_ = _args[16];
lean_object* v___y_6961_ = _args[17];
lean_object* v___y_6962_ = _args[18];
lean_object* v___y_6963_ = _args[19];
_start:
{
uint8_t v___x_6010__boxed_6964_; lean_object* v_res_6965_; 
v___x_6010__boxed_6964_ = lean_unbox(v___x_6953_);
v_res_6965_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6944_, v_snd_6945_, v___x_6946_, v_prefixArgs_6947_, v_value_6948_, v___f_6949_, v_funNames_6950_, v_argsPacker_6951_, v_decrTactics_6952_, v___x_6010__boxed_6964_, v_fst_6954_, v_xs_6955_, v_x_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_, v___y_6962_);
lean_dec(v___y_6962_);
lean_dec_ref(v___y_6961_);
lean_dec(v___y_6960_);
lean_dec(v___y_6958_);
lean_dec_ref(v___y_6957_);
lean_dec_ref(v_x_6956_);
lean_dec_ref(v_xs_6955_);
lean_dec(v___x_6946_);
return v_res_6965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6970_, lean_object* v_prefixArgs_6971_, lean_object* v_argsPacker_6972_, lean_object* v_wfRel_6973_, lean_object* v_funNames_6974_, lean_object* v_decrTactics_6975_, lean_object* v_a_6976_, lean_object* v_a_6977_, lean_object* v_a_6978_, lean_object* v_a_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_){
_start:
{
lean_object* v_declName_6983_; lean_object* v_type_6984_; lean_object* v_value_6985_; lean_object* v___x_6986_; 
v_declName_6983_ = lean_ctor_get(v_preDef_6970_, 3);
lean_inc(v_declName_6983_);
v_type_6984_ = lean_ctor_get(v_preDef_6970_, 6);
lean_inc_ref(v_type_6984_);
v_value_6985_ = lean_ctor_get(v_preDef_6970_, 7);
lean_inc_ref(v_value_6985_);
lean_dec_ref(v_preDef_6970_);
v___x_6986_ = l_Lean_Meta_instantiateForall(v_type_6984_, v_prefixArgs_6971_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
if (lean_obj_tag(v___x_6986_) == 0)
{
lean_object* v_a_6987_; lean_object* v___x_6988_; lean_object* v___x_6989_; lean_object* v___f_6990_; lean_object* v___x_6991_; uint8_t v___x_6992_; lean_object* v___x_6993_; 
v_a_6987_ = lean_ctor_get(v___x_6986_, 0);
lean_inc(v_a_6987_);
lean_dec_ref(v___x_6986_);
v___x_6988_ = l_Lean_instInhabitedExpr;
v___x_6989_ = lean_unsigned_to_nat(1u);
v___f_6990_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6990_, 0, v___x_6988_);
lean_closure_set(v___f_6990_, 1, v___x_6989_);
lean_closure_set(v___f_6990_, 2, v_wfRel_6973_);
v___x_6991_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6992_ = 0;
v___x_6993_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6987_, v___x_6991_, v___f_6990_, v___x_6992_, v___x_6992_, v_a_6976_, v_a_6977_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
if (lean_obj_tag(v___x_6993_) == 0)
{
lean_object* v_a_6994_; lean_object* v_fst_6995_; lean_object* v_snd_6996_; lean_object* v___x_6997_; 
v_a_6994_ = lean_ctor_get(v___x_6993_, 0);
lean_inc(v_a_6994_);
lean_dec_ref(v___x_6993_);
v_fst_6995_ = lean_ctor_get(v_a_6994_, 0);
lean_inc(v_fst_6995_);
v_snd_6996_ = lean_ctor_get(v_a_6994_, 1);
lean_inc(v_snd_6996_);
lean_dec(v_a_6994_);
lean_inc(v_a_6981_);
lean_inc_ref(v_a_6980_);
lean_inc(v_a_6979_);
lean_inc_ref(v_a_6978_);
lean_inc(v_fst_6995_);
v___x_6997_ = lean_infer_type(v_fst_6995_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
if (lean_obj_tag(v___x_6997_) == 0)
{
lean_object* v_a_6998_; lean_object* v___x_6999_; 
v_a_6998_ = lean_ctor_get(v___x_6997_, 0);
lean_inc(v_a_6998_);
lean_dec_ref(v___x_6997_);
lean_inc(v_a_6981_);
lean_inc_ref(v_a_6980_);
lean_inc(v_a_6979_);
lean_inc_ref(v_a_6978_);
v___x_6999_ = lean_whnf(v_a_6998_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
if (lean_obj_tag(v___x_6999_) == 0)
{
lean_object* v_a_7000_; lean_object* v___f_7001_; lean_object* v___x_7002_; lean_object* v___f_7003_; lean_object* v___x_7004_; lean_object* v___x_7005_; lean_object* v___x_7006_; 
v_a_7000_ = lean_ctor_get(v___x_6999_, 0);
lean_inc(v_a_7000_);
lean_dec_ref(v___x_6999_);
lean_inc_ref(v_prefixArgs_6971_);
v___f_7001_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_7001_, 0, v_prefixArgs_6971_);
lean_closure_set(v___f_7001_, 1, v_declName_6983_);
v___x_7002_ = lean_box(v___x_6992_);
v___f_7003_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_7003_, 0, v___x_6988_);
lean_closure_set(v___f_7003_, 1, v_snd_6996_);
lean_closure_set(v___f_7003_, 2, v___x_6989_);
lean_closure_set(v___f_7003_, 3, v_prefixArgs_6971_);
lean_closure_set(v___f_7003_, 4, v_value_6985_);
lean_closure_set(v___f_7003_, 5, v___f_7001_);
lean_closure_set(v___f_7003_, 6, v_funNames_6974_);
lean_closure_set(v___f_7003_, 7, v_argsPacker_6972_);
lean_closure_set(v___f_7003_, 8, v_decrTactics_6975_);
lean_closure_set(v___f_7003_, 9, v___x_7002_);
lean_closure_set(v___f_7003_, 10, v_fst_6995_);
v___x_7004_ = l_Lean_Expr_bindingDomain_x21(v_a_7000_);
lean_dec(v_a_7000_);
v___x_7005_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_7006_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_7004_, v___x_7005_, v___f_7003_, v___x_6992_, v___x_6992_, v_a_6976_, v_a_6977_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
return v___x_7006_;
}
else
{
lean_dec(v_snd_6996_);
lean_dec(v_fst_6995_);
lean_dec_ref(v_value_6985_);
lean_dec(v_declName_6983_);
lean_dec_ref(v_decrTactics_6975_);
lean_dec_ref(v_funNames_6974_);
lean_dec_ref(v_argsPacker_6972_);
lean_dec_ref(v_prefixArgs_6971_);
return v___x_6999_;
}
}
else
{
lean_dec(v_snd_6996_);
lean_dec(v_fst_6995_);
lean_dec_ref(v_value_6985_);
lean_dec(v_declName_6983_);
lean_dec_ref(v_decrTactics_6975_);
lean_dec_ref(v_funNames_6974_);
lean_dec_ref(v_argsPacker_6972_);
lean_dec_ref(v_prefixArgs_6971_);
return v___x_6997_;
}
}
else
{
lean_object* v_a_7007_; lean_object* v___x_7009_; uint8_t v_isShared_7010_; uint8_t v_isSharedCheck_7014_; 
lean_dec_ref(v_value_6985_);
lean_dec(v_declName_6983_);
lean_dec_ref(v_decrTactics_6975_);
lean_dec_ref(v_funNames_6974_);
lean_dec_ref(v_argsPacker_6972_);
lean_dec_ref(v_prefixArgs_6971_);
v_a_7007_ = lean_ctor_get(v___x_6993_, 0);
v_isSharedCheck_7014_ = !lean_is_exclusive(v___x_6993_);
if (v_isSharedCheck_7014_ == 0)
{
v___x_7009_ = v___x_6993_;
v_isShared_7010_ = v_isSharedCheck_7014_;
goto v_resetjp_7008_;
}
else
{
lean_inc(v_a_7007_);
lean_dec(v___x_6993_);
v___x_7009_ = lean_box(0);
v_isShared_7010_ = v_isSharedCheck_7014_;
goto v_resetjp_7008_;
}
v_resetjp_7008_:
{
lean_object* v___x_7012_; 
if (v_isShared_7010_ == 0)
{
v___x_7012_ = v___x_7009_;
goto v_reusejp_7011_;
}
else
{
lean_object* v_reuseFailAlloc_7013_; 
v_reuseFailAlloc_7013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7013_, 0, v_a_7007_);
v___x_7012_ = v_reuseFailAlloc_7013_;
goto v_reusejp_7011_;
}
v_reusejp_7011_:
{
return v___x_7012_;
}
}
}
}
else
{
lean_dec_ref(v_value_6985_);
lean_dec(v_declName_6983_);
lean_dec_ref(v_decrTactics_6975_);
lean_dec_ref(v_funNames_6974_);
lean_dec_ref(v_wfRel_6973_);
lean_dec_ref(v_argsPacker_6972_);
lean_dec_ref(v_prefixArgs_6971_);
return v___x_6986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_7015_, lean_object* v_prefixArgs_7016_, lean_object* v_argsPacker_7017_, lean_object* v_wfRel_7018_, lean_object* v_funNames_7019_, lean_object* v_decrTactics_7020_, lean_object* v_a_7021_, lean_object* v_a_7022_, lean_object* v_a_7023_, lean_object* v_a_7024_, lean_object* v_a_7025_, lean_object* v_a_7026_, lean_object* v_a_7027_){
_start:
{
lean_object* v_res_7028_; 
v_res_7028_ = l_Lean_Elab_WF_mkFix(v_preDef_7015_, v_prefixArgs_7016_, v_argsPacker_7017_, v_wfRel_7018_, v_funNames_7019_, v_decrTactics_7020_, v_a_7021_, v_a_7022_, v_a_7023_, v_a_7024_, v_a_7025_, v_a_7026_);
lean_dec(v_a_7026_);
lean_dec_ref(v_a_7025_);
lean_dec(v_a_7024_);
lean_dec_ref(v_a_7023_);
lean_dec(v_a_7022_);
lean_dec_ref(v_a_7021_);
return v_res_7028_;
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
