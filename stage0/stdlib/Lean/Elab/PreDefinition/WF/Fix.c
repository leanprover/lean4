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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* l_Lean_LocalContext_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isEmpty(lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 249, 30, 71, 49, 108, 60, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "WellFounded"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 126, 194, 128, 117, 36, 224, 78)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 0, 160, 225, 119, 146, 123, 62)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "opaqueId"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 89, 34, 148, 92, 203, 118, 146)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 133, 211, 204, 28, 206, 53, 233)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__7_value;
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
v___x_212_ = l_Lean_LocalContext_isEmpty(v_lctx_201_);
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
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v_recFnName_270_);
v___x_277_ = lean_st_ref_take(v_a_272_);
v___x_278_ = l_Lean_HasConstCache_containsUnsafe(v___x_276_, v_e_271_, v___x_277_);
lean_dec_ref(v___x_276_);
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
lean_object* v_ref_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_371_; 
v_ref_324_ = lean_ctor_get(v___y_321_, 2);
v___x_325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_371_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_371_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_371_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v_traceState_331_; lean_object* v_env_332_; lean_object* v_nextMacroScope_333_; lean_object* v_ngen_334_; lean_object* v_auxDeclNGen_335_; lean_object* v_cache_336_; lean_object* v_recordedDeps_337_; lean_object* v_messages_338_; lean_object* v_infoState_339_; lean_object* v_snapshotTasks_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_370_; 
v___x_330_ = lean_st_ref_take(v___y_322_);
v_traceState_331_ = lean_ctor_get(v___x_330_, 4);
v_env_332_ = lean_ctor_get(v___x_330_, 0);
v_nextMacroScope_333_ = lean_ctor_get(v___x_330_, 1);
v_ngen_334_ = lean_ctor_get(v___x_330_, 2);
v_auxDeclNGen_335_ = lean_ctor_get(v___x_330_, 3);
v_cache_336_ = lean_ctor_get(v___x_330_, 5);
v_recordedDeps_337_ = lean_ctor_get(v___x_330_, 6);
v_messages_338_ = lean_ctor_get(v___x_330_, 7);
v_infoState_339_ = lean_ctor_get(v___x_330_, 8);
v_snapshotTasks_340_ = lean_ctor_get(v___x_330_, 9);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_370_ == 0)
{
v___x_342_ = v___x_330_;
v_isShared_343_ = v_isSharedCheck_370_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snapshotTasks_340_);
lean_inc(v_infoState_339_);
lean_inc(v_messages_338_);
lean_inc(v_recordedDeps_337_);
lean_inc(v_cache_336_);
lean_inc(v_traceState_331_);
lean_inc(v_auxDeclNGen_335_);
lean_inc(v_ngen_334_);
lean_inc(v_nextMacroScope_333_);
lean_inc(v_env_332_);
lean_dec(v___x_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_370_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint64_t v_tid_344_; lean_object* v_traces_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_369_; 
v_tid_344_ = lean_ctor_get_uint64(v_traceState_331_, sizeof(void*)*1);
v_traces_345_ = lean_ctor_get(v_traceState_331_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_traceState_331_);
if (v_isSharedCheck_369_ == 0)
{
v___x_347_ = v_traceState_331_;
v_isShared_348_ = v_isSharedCheck_369_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_traces_345_);
lean_dec(v_traceState_331_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_369_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; double v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_box(0);
v___x_351_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_352_ = 0;
v___x_353_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_354_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_354_, 0, v_cls_317_);
lean_ctor_set(v___x_354_, 1, v___x_350_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
lean_ctor_set_float(v___x_354_, sizeof(void*)*3, v___x_351_);
lean_ctor_set_float(v___x_354_, sizeof(void*)*3 + 8, v___x_351_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3 + 16, v___x_352_);
v___x_355_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_356_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v_a_326_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
lean_inc(v_ref_324_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_ref_324_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_PersistentArray_push___redArg(v_traces_345_, v___x_357_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_358_);
v___x_360_ = v___x_347_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_358_);
lean_ctor_set_uint64(v_reuseFailAlloc_368_, sizeof(void*)*1, v_tid_344_);
v___x_360_ = v_reuseFailAlloc_368_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_360_);
v___x_362_ = v___x_342_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_env_332_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_nextMacroScope_333_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_ngen_334_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_auxDeclNGen_335_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v_cache_336_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_recordedDeps_337_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v_messages_338_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v_infoState_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 9, v_snapshotTasks_340_);
v___x_362_ = v_reuseFailAlloc_367_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_st_ref_put(v___y_322_, v___x_362_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_349_);
v___x_365_ = v___x_328_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_349_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object* v_cls_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_372_, v_msg_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
return v_x_380_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_407_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_407_ == 0)
{
v___x_386_ = v_x_381_;
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_tail_384_);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
lean_dec(v_x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v_fold_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_388_ = lean_array_get_size(v_x_380_);
v___x_389_ = l_Lean_Expr_hash(v_key_382_);
v___x_390_ = 32ULL;
v___x_391_ = lean_uint64_shift_right(v___x_389_, v___x_390_);
v_fold_392_ = lean_uint64_xor(v___x_389_, v___x_391_);
v___x_393_ = 16ULL;
v___x_394_ = lean_uint64_shift_right(v_fold_392_, v___x_393_);
v___x_395_ = lean_uint64_xor(v_fold_392_, v___x_394_);
v___x_396_ = lean_uint64_to_usize(v___x_395_);
v___x_397_ = lean_usize_of_nat(v___x_388_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_sub(v___x_397_, v___x_398_);
v___x_400_ = lean_usize_land(v___x_396_, v___x_399_);
v___x_401_ = lean_array_uget_borrowed(v_x_380_, v___x_400_);
lean_inc(v___x_401_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_401_);
v___x_403_ = v___x_386_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_key_382_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_value_383_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_array_uset(v_x_380_, v___x_400_, v___x_403_);
v_x_380_ = v___x_404_;
v_x_381_ = v_tail_384_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(lean_object* v_i_408_, lean_object* v_source_409_, lean_object* v_target_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_source_409_);
v___x_412_ = lean_nat_dec_lt(v_i_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_source_409_);
lean_dec(v_i_408_);
return v_target_410_;
}
else
{
lean_object* v_es_413_; lean_object* v___x_414_; lean_object* v_source_415_; lean_object* v_target_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_es_413_ = lean_array_fget(v_source_409_, v_i_408_);
v___x_414_ = lean_box(0);
v_source_415_ = lean_array_fset(v_source_409_, v_i_408_, v___x_414_);
v_target_416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_target_410_, v_es_413_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_i_408_, v___x_417_);
lean_dec(v_i_408_);
v_i_408_ = v___x_418_;
v_source_409_ = v_source_415_;
v_target_410_ = v_target_416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(lean_object* v_data_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_nbuckets_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_421_ = lean_array_get_size(v_data_420_);
v___x_422_ = lean_unsigned_to_nat(2u);
v_nbuckets_423_ = lean_nat_mul(v___x_421_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_box(0);
v___x_426_ = lean_mk_array(v_nbuckets_423_, v___x_425_);
v___x_427_ = lean_array_propagate_mark(v_data_420_, v___x_426_);
v___x_428_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_424_, v_data_420_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
else
{
lean_object* v_key_432_; lean_object* v_tail_433_; uint8_t v___x_434_; 
v_key_432_ = lean_ctor_get(v_x_430_, 0);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v___x_434_ = lean_expr_eqv(v_key_432_, v_a_429_);
if (v___x_434_ == 0)
{
v_x_430_ = v_tail_433_;
goto _start;
}
else
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec_ref(v_a_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_440_, lean_object* v_b_441_, lean_object* v_x_442_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_dec(v_b_441_);
lean_dec_ref(v_a_440_);
return v_x_442_;
}
else
{
lean_object* v_key_443_; lean_object* v_value_444_; lean_object* v_tail_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_457_; 
v_key_443_ = lean_ctor_get(v_x_442_, 0);
v_value_444_ = lean_ctor_get(v_x_442_, 1);
v_tail_445_ = lean_ctor_get(v_x_442_, 2);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_442_);
if (v_isSharedCheck_457_ == 0)
{
v___x_447_ = v_x_442_;
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_tail_445_);
lean_inc(v_value_444_);
lean_inc(v_key_443_);
lean_dec(v_x_442_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
uint8_t v___x_449_; 
v___x_449_ = lean_expr_eqv(v_key_443_, v_a_440_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_440_, v_b_441_, v_tail_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_key_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_value_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_455_; 
lean_dec(v_value_444_);
lean_dec(v_key_443_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_b_441_);
lean_ctor_set(v___x_447_, 0, v_a_440_);
v___x_455_ = v___x_447_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_440_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_b_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_tail_445_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_458_, lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
lean_object* v_size_461_; lean_object* v_buckets_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_505_; 
v_size_461_ = lean_ctor_get(v_m_458_, 0);
v_buckets_462_ = lean_ctor_get(v_m_458_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_m_458_);
if (v_isSharedCheck_505_ == 0)
{
v___x_464_ = v_m_458_;
v_isShared_465_ = v_isSharedCheck_505_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_buckets_462_);
lean_inc(v_size_461_);
lean_dec(v_m_458_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_505_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v_fold_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; lean_object* v_bkt_479_; uint8_t v___x_480_; 
v___x_466_ = lean_array_get_size(v_buckets_462_);
v___x_467_ = l_Lean_Expr_hash(v_a_459_);
v___x_468_ = 32ULL;
v___x_469_ = lean_uint64_shift_right(v___x_467_, v___x_468_);
v_fold_470_ = lean_uint64_xor(v___x_467_, v___x_469_);
v___x_471_ = 16ULL;
v___x_472_ = lean_uint64_shift_right(v_fold_470_, v___x_471_);
v___x_473_ = lean_uint64_xor(v_fold_470_, v___x_472_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = lean_usize_of_nat(v___x_466_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_usize_land(v___x_474_, v___x_477_);
v_bkt_479_ = lean_array_uget_borrowed(v_buckets_462_, v___x_478_);
v___x_480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_459_, v_bkt_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v_size_x27_482_; lean_object* v___x_483_; lean_object* v_buckets_x27_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v_size_x27_482_ = lean_nat_add(v_size_461_, v___x_481_);
lean_dec(v_size_461_);
lean_inc(v_bkt_479_);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v_a_459_);
lean_ctor_set(v___x_483_, 1, v_b_460_);
lean_ctor_set(v___x_483_, 2, v_bkt_479_);
v_buckets_x27_484_ = lean_array_uset(v_buckets_462_, v___x_478_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(4u);
v___x_486_ = lean_nat_mul(v_size_x27_482_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_div(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_array_get_size(v_buckets_x27_484_);
v___x_490_ = lean_nat_dec_le(v___x_488_, v___x_489_);
lean_dec(v___x_488_);
if (v___x_490_ == 0)
{
lean_object* v_val_491_; lean_object* v___x_493_; 
v_val_491_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_484_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_val_491_);
lean_ctor_set(v___x_464_, 0, v_size_x27_482_);
v___x_493_ = v___x_464_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_val_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_496_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_buckets_x27_484_);
lean_ctor_set(v___x_464_, 0, v_size_x27_482_);
v___x_496_ = v___x_464_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_size_x27_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_buckets_x27_484_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v___x_498_; lean_object* v_buckets_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_inc(v_bkt_479_);
v___x_498_ = lean_box(0);
v_buckets_x27_499_ = lean_array_uset(v_buckets_462_, v___x_478_, v___x_498_);
v___x_500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_459_, v_b_460_, v_bkt_479_);
v___x_501_ = lean_array_uset(v_buckets_x27_499_, v___x_478_, v___x_500_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_501_);
v___x_503_ = v___x_464_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_size_461_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_ref_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_ref_512_ = lean_ctor_get(v___y_509_, 2);
v___x_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_ref_512_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_ref_512_);
lean_ctor_set(v___x_518_, 1, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_e_545_, lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_630_; 
lean_inc_ref(v_a_546_);
v___x_630_ = l_Lean_Meta_isTypeCorrect(v_a_546_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; uint8_t v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = lean_unbox(v_a_631_);
lean_dec(v_a_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_545_);
v___x_634_ = l_Lean_indentExpr(v_e_545_);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
lean_inc_ref(v_a_546_);
v___x_638_ = l_Lean_indentExpr(v_a_546_);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_639_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
goto v___jp_556_;
}
else
{
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
return v___x_640_;
}
}
else
{
goto v___jp_556_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v_a_641_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_630_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_630_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
v___jp_556_:
{
lean_object* v___x_557_; 
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc_ref(v_e_545_);
v___x_557_ = lean_infer_type(v_e_545_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc_ref(v_a_546_);
v___x_559_ = lean_infer_type(v_a_546_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc_n(v_a_560_, 2);
lean_dec_ref_known(v___x_559_, 1);
lean_inc(v_a_558_);
v___x_561_ = l_Lean_Meta_isExprDefEq(v_a_558_, v_a_560_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_605_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_605_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_605_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_605_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_unbox(v_a_562_);
lean_dec(v_a_562_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_del_object(v___x_564_);
v___x_567_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_558_, v_a_560_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_592_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v_fst_569_ = lean_ctor_get(v_a_568_, 0);
v_snd_570_ = lean_ctor_get(v_a_568_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_a_568_);
if (v_isSharedCheck_592_ == 0)
{
v___x_572_ = v_a_568_;
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v_a_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_575_ = l_Lean_indentExpr(v_e_545_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 7);
lean_ctor_set(v___x_572_, 1, v___x_575_);
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_591_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_578_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_indentExpr(v_a_546_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_indentExpr(v_fst_569_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_indentExpr(v_snd_570_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_589_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_590_;
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v_a_593_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_567_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_567_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v_a_560_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v___x_601_ = lean_box(0);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_601_);
v___x_603_ = v___x_564_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
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
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_560_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v_a_606_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_561_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_561_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_558_);
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v_a_614_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_559_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_559_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_a_546_);
lean_dec_ref(v_e_545_);
v_a_622_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_557_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_557_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_e_649_, v_a_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec(v___y_651_);
return v_res_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_ctor_set(v___x_666_, 2, v___x_665_);
lean_ctor_set(v___x_666_, 3, v___x_665_);
lean_ctor_set(v___x_666_, 4, v___x_664_);
lean_ctor_set(v___x_666_, 5, v___x_664_);
lean_ctor_set(v___x_666_, 6, v___x_664_);
lean_ctor_set(v___x_666_, 7, v___x_664_);
lean_ctor_set(v___x_666_, 8, v___x_664_);
lean_ctor_set(v___x_666_, 9, v___x_664_);
lean_ctor_set(v___x_666_, 10, v___x_664_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(32u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = ((size_t)5ULL);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_unsigned_to_nat(32u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_675_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_671_);
lean_ctor_set(v___x_675_, 3, v___x_671_);
lean_ctor_set_usize(v___x_675_, 4, v___x_670_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_box(1);
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v___x_676_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_701_, lean_object* v_declHint_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_env_707_; uint8_t v___x_708_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_st_ref_get(v___y_703_);
v_env_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_706_);
v___x_708_ = l_Lean_Name_isAnonymous(v_declHint_702_);
if (v___x_708_ == 0)
{
uint8_t v_isExporting_709_; 
v_isExporting_709_ = lean_ctor_get_uint8(v_env_707_, sizeof(void*)*8);
if (v_isExporting_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v_env_707_);
lean_dec(v_declHint_702_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_msg_701_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc_ref(v_env_707_);
v___x_711_ = l_Lean_Environment_setExporting(v_env_707_, v___x_708_);
lean_inc(v_declHint_702_);
lean_inc_ref(v___x_711_);
v___x_712_ = l_Lean_Environment_contains(v___x_711_, v_declHint_702_, v_isExporting_709_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v___x_711_);
lean_dec_ref(v_env_707_);
lean_dec(v_declHint_702_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_msg_701_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_c_719_; lean_object* v___x_720_; 
v___x_714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_716_ = l_Lean_Options_empty;
v___x_717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_717_, 0, v___x_711_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
lean_ctor_set(v___x_717_, 2, v___x_715_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
lean_inc(v_declHint_702_);
v___x_718_ = l_Lean_MessageData_ofConstName(v_declHint_702_, v___x_708_);
v_c_719_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_719_, 0, v___x_717_);
lean_ctor_set(v_c_719_, 1, v___x_718_);
v___x_720_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_707_, v_declHint_702_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_env_707_);
lean_dec(v_declHint_702_);
v___x_721_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v_c_719_);
v___x_723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_MessageData_note(v___x_724_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v_msg_701_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_762_; 
v_val_728_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_762_ == 0)
{
v___x_730_ = v___x_720_;
v_isShared_731_ = v_isSharedCheck_762_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v___x_720_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_762_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_mod_734_; uint8_t v___x_735_; 
v___x_732_ = l_Lean_Environment_header(v_env_707_);
lean_dec_ref(v_env_707_);
v___x_733_ = l_Lean_EnvironmentHeader_moduleNames(v___x_732_);
v_mod_734_ = lean_array_get(v___x_705_, v___x_733_, v_val_728_);
lean_dec(v_val_728_);
lean_dec_ref(v___x_733_);
v___x_735_ = l_Lean_isPrivateName(v_declHint_702_);
lean_dec(v_declHint_702_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v_c_719_);
v___x_738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_MessageData_ofName(v_mod_734_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_MessageData_note(v___x_743_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v_msg_701_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 0);
lean_ctor_set(v___x_730_, 0, v___x_745_);
v___x_747_ = v___x_730_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_c_719_);
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_MessageData_ofName(v_mod_734_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_MessageData_note(v___x_756_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v_msg_701_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 0);
lean_ctor_set(v___x_730_, 0, v___x_758_);
v___x_760_ = v___x_730_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_763_; 
lean_dec_ref(v_env_707_);
lean_dec(v_declHint_702_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_msg_701_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_764_, lean_object* v_declHint_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_764_, v_declHint_765_, v___y_766_);
lean_dec(v___y_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_769_, lean_object* v_declHint_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v___x_780_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_769_, v_declHint_770_, v___y_778_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = l_Lean_unknownIdentifierMessageTag;
v___x_786_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_a_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_791_, lean_object* v_declHint_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_791_, v_declHint_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_toCold_814_; lean_object* v_currRecDepth_815_; lean_object* v_ref_816_; uint16_t v_optionFlags_817_; uint8_t v_suppressElabErrors_818_; uint8_t v_isRecordingDeps_819_; lean_object* v_ref_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_toCold_814_ = lean_ctor_get(v___y_811_, 0);
v_currRecDepth_815_ = lean_ctor_get(v___y_811_, 1);
v_ref_816_ = lean_ctor_get(v___y_811_, 2);
v_optionFlags_817_ = lean_ctor_get_uint16(v___y_811_, sizeof(void*)*3);
v_suppressElabErrors_818_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*3 + 2);
v_isRecordingDeps_819_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*3 + 3);
v_ref_820_ = l_Lean_replaceRef(v_ref_803_, v_ref_816_);
lean_inc(v_currRecDepth_815_);
lean_inc_ref(v_toCold_814_);
v___x_821_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_821_, 0, v_toCold_814_);
lean_ctor_set(v___x_821_, 1, v_currRecDepth_815_);
lean_ctor_set(v___x_821_, 2, v_ref_820_);
lean_ctor_set_uint16(v___x_821_, sizeof(void*)*3, v_optionFlags_817_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*3 + 2, v_suppressElabErrors_818_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*3 + 3, v_isRecordingDeps_819_);
v___x_822_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_804_, v___y_809_, v___y_810_, v___x_821_, v___y_812_);
lean_dec_ref_known(v___x_821_, 3);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_823_, v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec(v___y_825_);
lean_dec(v_ref_823_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_835_, lean_object* v_msg_836_, lean_object* v_declHint_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_849_; 
v___x_847_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_836_, v_declHint_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_835_, v_a_848_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_850_, lean_object* v_msg_851_, lean_object* v_declHint_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_850_, v_msg_851_, v_declHint_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v_ref_850_);
return v_res_862_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_869_, lean_object* v_constName_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_880_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_881_ = 0;
lean_inc(v_constName_870_);
v___x_882_ = l_Lean_MessageData_ofConstName(v_constName_870_, v___x_881_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_880_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_869_, v___x_885_, v_constName_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_887_, lean_object* v_constName_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_887_, v_constName_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec(v___y_889_);
lean_dec(v_ref_887_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_ref_909_; lean_object* v___x_910_; 
v_ref_909_ = lean_ctor_get(v___y_906_, 2);
v___x_910_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_909_, v_constName_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; lean_object* v_env_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_932_ = lean_st_ref_get(v___y_930_);
v_env_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc_ref(v_env_933_);
lean_dec(v___x_932_);
v___x_934_ = 0;
lean_inc(v_constName_922_);
v___x_935_ = l_Lean_Environment_find_x3f(v_env_933_, v_constName_922_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_936_;
}
else
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_constName_922_);
v_val_937_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 0);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_val_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_env_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_960_, v_declName_956_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_963_, v___y_964_);
lean_dec(v___y_964_);
return v_res_966_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_instMonadEIO___redArg();
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_toApplicative_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1079_; 
v___x_984_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_985_ = l_StateRefT_x27_instMonad___redArg(v___x_984_);
v_toApplicative_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_985_, 1);
lean_dec(v_unused_1080_);
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1079_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_toApplicative_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1079_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_toFunctor_990_; lean_object* v_toSeq_991_; lean_object* v_toSeqLeft_992_; lean_object* v_toSeqRight_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1077_; 
v_toFunctor_990_ = lean_ctor_get(v_toApplicative_986_, 0);
v_toSeq_991_ = lean_ctor_get(v_toApplicative_986_, 2);
v_toSeqLeft_992_ = lean_ctor_get(v_toApplicative_986_, 3);
v_toSeqRight_993_ = lean_ctor_get(v_toApplicative_986_, 4);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_toApplicative_986_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_dec(v_unused_1078_);
v___x_995_ = v_toApplicative_986_;
v_isShared_996_ = v_isSharedCheck_1077_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_toSeqRight_993_);
lean_inc(v_toSeqLeft_992_);
lean_inc(v_toSeq_991_);
lean_inc(v_toFunctor_990_);
lean_dec(v_toApplicative_986_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1077_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___x_1006_; 
v___f_997_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_998_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_990_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_999_, 0, v_toFunctor_990_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toFunctor_990_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___f_999_);
lean_ctor_set(v___x_1001_, 1, v___f_1000_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toSeqRight_993_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toSeqLeft_992_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toSeq_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___f_1002_);
lean_ctor_set(v___x_995_, 3, v___f_1003_);
lean_ctor_set(v___x_995_, 2, v___f_1004_);
lean_ctor_set(v___x_995_, 1, v___f_997_);
lean_ctor_set(v___x_995_, 0, v___x_1001_);
v___x_1006_ = v___x_995_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_997_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v___f_1004_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___f_1002_);
v___x_1006_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___f_998_);
lean_ctor_set(v___x_988_, 0, v___x_1006_);
v___x_1008_ = v___x_988_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_998_);
v___x_1008_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v_toApplicative_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1073_; 
v___x_1009_ = l_StateRefT_x27_instMonad___redArg(v___x_1008_);
v_toApplicative_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1009_, 1);
lean_dec(v_unused_1074_);
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1073_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_toApplicative_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1073_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_toFunctor_1014_; lean_object* v_toSeq_1015_; lean_object* v_toSeqLeft_1016_; lean_object* v_toSeqRight_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1071_; 
v_toFunctor_1014_ = lean_ctor_get(v_toApplicative_1010_, 0);
v_toSeq_1015_ = lean_ctor_get(v_toApplicative_1010_, 2);
v_toSeqLeft_1016_ = lean_ctor_get(v_toApplicative_1010_, 3);
v_toSeqRight_1017_ = lean_ctor_get(v_toApplicative_1010_, 4);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_toApplicative_1010_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_toApplicative_1010_, 1);
lean_dec(v_unused_1072_);
v___x_1019_ = v_toApplicative_1010_;
v_isShared_1020_ = v_isSharedCheck_1071_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_toSeqRight_1017_);
lean_inc(v_toSeqLeft_1016_);
lean_inc(v_toSeq_1015_);
lean_inc(v_toFunctor_1014_);
lean_dec(v_toApplicative_1010_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1071_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___x_1030_; 
v___f_1021_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1022_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1014_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toFunctor_1014_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toFunctor_1014_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___f_1023_);
lean_ctor_set(v___x_1025_, 1, v___f_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeqRight_1017_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeqLeft_1016_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeq_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v___f_1026_);
lean_ctor_set(v___x_1019_, 3, v___f_1027_);
lean_ctor_set(v___x_1019_, 2, v___f_1028_);
lean_ctor_set(v___x_1019_, 1, v___f_1021_);
lean_ctor_set(v___x_1019_, 0, v___x_1025_);
v___x_1030_ = v___x_1019_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1021_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___f_1028_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___f_1027_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___f_1026_);
v___x_1030_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v___f_1022_);
lean_ctor_set(v___x_1012_, 0, v___x_1030_);
v___x_1032_ = v___x_1012_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1022_);
v___x_1032_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v_toApplicative_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1067_; 
v___x_1033_ = l_StateRefT_x27_instMonad___redArg(v___x_1032_);
v_toApplicative_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1033_, 1);
lean_dec(v_unused_1068_);
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1067_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_toApplicative_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1067_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_toFunctor_1038_; lean_object* v_toSeq_1039_; lean_object* v_toSeqLeft_1040_; lean_object* v_toSeqRight_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1065_; 
v_toFunctor_1038_ = lean_ctor_get(v_toApplicative_1034_, 0);
v_toSeq_1039_ = lean_ctor_get(v_toApplicative_1034_, 2);
v_toSeqLeft_1040_ = lean_ctor_get(v_toApplicative_1034_, 3);
v_toSeqRight_1041_ = lean_ctor_get(v_toApplicative_1034_, 4);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_toApplicative_1034_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_toApplicative_1034_, 1);
lean_dec(v_unused_1066_);
v___x_1043_ = v_toApplicative_1034_;
v_isShared_1044_ = v_isSharedCheck_1065_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_toSeqRight_1041_);
lean_inc(v_toSeqLeft_1040_);
lean_inc(v_toSeq_1039_);
lean_inc(v_toFunctor_1038_);
lean_dec(v_toApplicative_1034_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1065_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1054_; 
v___f_1045_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1046_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1038_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toFunctor_1038_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toFunctor_1038_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___f_1047_);
lean_ctor_set(v___x_1049_, 1, v___f_1048_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeqRight_1041_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toSeqLeft_1040_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toSeq_1039_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 4, v___f_1050_);
lean_ctor_set(v___x_1043_, 3, v___f_1051_);
lean_ctor_set(v___x_1043_, 2, v___f_1052_);
lean_ctor_set(v___x_1043_, 1, v___f_1045_);
lean_ctor_set(v___x_1043_, 0, v___x_1049_);
v___x_1054_ = v___x_1043_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___f_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v___f_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v___f_1051_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___f_1050_);
v___x_1054_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___f_1046_);
lean_ctor_set(v___x_1036_, 0, v___x_1054_);
v___x_1056_ = v___x_1036_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___f_1046_);
v___x_1056_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_49754__overap_1061_; lean_object* v___x_1062_; 
v___x_1057_ = l_StateRefT_x27_instMonad___redArg(v___x_1056_);
v___x_1058_ = l_StateRefT_x27_instMonad___redArg(v___x_1057_);
v___x_1059_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1060_ = l_instInhabitedOfMonad___redArg(v___x_1058_, v___x_1059_);
v___x_49754__overap_1061_ = lean_panic_fn_borrowed(v___x_1060_, v_msg_974_);
lean_dec(v___x_1060_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc(v___y_975_);
v___x_1062_ = lean_apply_9(v___x_49754__overap_1061_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_1062_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec(v___y_1082_);
return v_res_1091_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1096_ = lean_unsigned_to_nat(53u);
v___x_1097_ = lean_unsigned_to_nat(62u);
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1100_ = l_mkPanicMessageWithDecl(v___x_1099_, v___x_1098_, v___x_1097_, v___x_1096_, v___x_1095_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1101_, size_t v_i_1102_, lean_object* v_bs_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_lt(v_i_1102_, v_sz_1101_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_bs_1103_);
return v___x_1114_;
}
else
{
lean_object* v_v_1115_; lean_object* v___x_1116_; lean_object* v_bs_x27_1117_; lean_object* v_a_1119_; lean_object* v___x_1124_; 
v_v_1115_ = lean_array_uget(v_bs_1103_, v_i_1102_);
v___x_1116_ = lean_unsigned_to_nat(0u);
v_bs_x27_1117_ = lean_array_uset(v_bs_1103_, v_i_1102_, v___x_1116_);
v___x_1124_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1115_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
if (lean_obj_tag(v_a_1125_) == 6)
{
lean_object* v_val_1126_; lean_object* v_numFields_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; 
v_val_1126_ = lean_ctor_get(v_a_1125_, 0);
lean_inc_ref(v_val_1126_);
lean_dec_ref_known(v_a_1125_, 1);
v_numFields_1127_ = lean_ctor_get(v_val_1126_, 4);
lean_inc(v_numFields_1127_);
lean_dec_ref(v_val_1126_);
v___x_1128_ = 0;
v___x_1129_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1129_, 0, v_numFields_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1116_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*2, v___x_1128_);
v_a_1119_ = v___x_1129_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_a_1125_);
v___x_1130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1131_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1130_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v_a_1119_ = v_a_1132_;
goto v___jp_1118_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_bs_x27_1117_);
v_a_1133_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_bs_x27_1117_);
v_a_1141_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1124_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1124_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
v___jp_1118_:
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1102_, v___x_1120_);
v___x_1122_ = lean_array_uset(v_bs_x27_1117_, v_i_1102_, v_a_1119_);
v_i_1102_ = v___x_1121_;
v_bs_1103_ = v___x_1122_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_bs_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1161_, v_i_boxed_1162_, v_bs_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
return v_res_1163_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1164_; lean_object* v_dummy_1165_; 
v___x_1164_ = lean_box(0);
v_dummy_1165_ = l_Lean_Expr_sort___override(v___x_1164_);
return v_dummy_1165_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_unsigned_to_nat(16u);
v___x_1168_ = lean_mk_array(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___x_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1174_, uint8_t v_alsoCasesOn_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_Lean_Expr_isApp(v_e_1174_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec_ref(v_e_1174_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Expr_getAppFn(v_e_1174_);
if (lean_obj_tag(v___x_1191_) == 4)
{
lean_object* v_declName_1192_; lean_object* v_us_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1348_; 
v_declName_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_n(v_declName_1192_, 2);
v_us_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_us_1193_);
lean_dec_ref_known(v___x_1191_, 2);
v___x_1194_ = l_Lean_instInhabitedExpr;
v___x_1195_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1192_, v___y_1183_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1348_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1348_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
if (lean_obj_tag(v_a_1196_) == 1)
{
lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1241_; 
v_val_1200_ = lean_ctor_get(v_a_1196_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_a_1196_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1202_ = v_a_1196_;
v_isShared_1203_ = v_isSharedCheck_1241_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_dec(v_a_1196_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1241_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_dummy_1204_; lean_object* v_nargs_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_args_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_dummy_1204_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1205_ = l_Lean_Expr_getAppNumArgs(v_e_1174_);
lean_inc(v_nargs_1205_);
v___x_1206_ = lean_mk_array(v_nargs_1205_, v_dummy_1204_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_sub(v_nargs_1205_, v___x_1207_);
lean_dec(v_nargs_1205_);
v_args_1209_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1174_, v___x_1206_, v___x_1208_);
v___x_1210_ = lean_array_get_size(v_args_1209_);
v___x_1211_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1200_);
v___x_1212_ = lean_nat_dec_lt(v___x_1210_, v___x_1211_);
lean_dec(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v_numParams_1213_; lean_object* v_numDiscrs_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_numParams_1213_ = lean_ctor_get(v_val_1200_, 0);
v_numDiscrs_1214_ = lean_ctor_get(v_val_1200_, 1);
v___x_1215_ = lean_array_mk(v_us_1193_);
v___x_1216_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1213_);
v___x_1217_ = l_Array_extract___redArg(v_args_1209_, v___x_1216_, v_numParams_1213_);
v___x_1218_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1200_);
v___x_1219_ = lean_array_get(v___x_1194_, v_args_1209_, v___x_1218_);
lean_dec(v___x_1218_);
v___x_1220_ = lean_nat_add(v_numParams_1213_, v___x_1207_);
v___x_1221_ = lean_nat_add(v___x_1220_, v_numDiscrs_1214_);
lean_inc(v___x_1221_);
lean_inc_ref_n(v_args_1209_, 2);
v___x_1222_ = l_Array_toSubarray___redArg(v_args_1209_, v___x_1220_, v___x_1221_);
v___x_1223_ = l_Subarray_copy___redArg(v___x_1222_);
v___x_1224_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1200_);
v___x_1225_ = lean_nat_add(v___x_1221_, v___x_1224_);
lean_dec(v___x_1224_);
lean_inc(v___x_1225_);
v___x_1226_ = l_Array_toSubarray___redArg(v_args_1209_, v___x_1221_, v___x_1225_);
v___x_1227_ = l_Subarray_copy___redArg(v___x_1226_);
v___x_1228_ = l_Array_toSubarray___redArg(v_args_1209_, v___x_1225_, v___x_1210_);
v___x_1229_ = l_Subarray_copy___redArg(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1230_, 0, v_val_1200_);
lean_ctor_set(v___x_1230_, 1, v_declName_1192_);
lean_ctor_set(v___x_1230_, 2, v___x_1215_);
lean_ctor_set(v___x_1230_, 3, v___x_1217_);
lean_ctor_set(v___x_1230_, 4, v___x_1219_);
lean_ctor_set(v___x_1230_, 5, v___x_1223_);
lean_ctor_set(v___x_1230_, 6, v___x_1227_);
lean_ctor_set(v___x_1230_, 7, v___x_1229_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1230_);
v___x_1232_ = v___x_1202_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1232_);
v___x_1234_ = v___x_1198_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec_ref(v_args_1209_);
lean_del_object(v___x_1202_);
lean_dec(v_val_1200_);
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
v___x_1237_ = lean_box(0);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1237_);
v___x_1239_ = v___x_1198_;
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
}
else
{
lean_object* v___x_1242_; 
lean_del_object(v___x_1198_);
lean_dec(v_a_1196_);
v___x_1242_ = lean_st_ref_get(v___y_1183_);
if (v_alsoCasesOn_1175_ == 0)
{
lean_dec(v___x_1242_);
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
lean_dec_ref(v_e_1174_);
goto v___jp_1185_;
}
else
{
lean_object* v_env_1243_; uint8_t v___x_1244_; 
v_env_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_env_1243_);
lean_dec(v___x_1242_);
lean_inc(v_declName_1192_);
v___x_1244_ = l_Lean_isCasesOnRecursor(v_env_1243_, v_declName_1192_);
if (v___x_1244_ == 0)
{
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
lean_dec_ref(v_e_1174_);
goto v___jp_1185_;
}
else
{
lean_object* v_indName_1245_; lean_object* v___x_1246_; 
v_indName_1245_ = l_Lean_Name_getPrefix(v_declName_1192_);
v___x_1246_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1245_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1339_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1339_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1339_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
if (lean_obj_tag(v_a_1247_) == 5)
{
lean_object* v_val_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1334_; 
v_val_1251_ = lean_ctor_get(v_a_1247_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_a_1247_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1253_ = v_a_1247_;
v_isShared_1254_ = v_isSharedCheck_1334_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_val_1251_);
lean_dec(v_a_1247_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1334_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_toConstantVal_1255_; lean_object* v_numParams_1256_; lean_object* v_numIndices_1257_; lean_object* v_ctors_1258_; lean_object* v_nargs_1259_; lean_object* v_dummy_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_args_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_toConstantVal_1255_ = lean_ctor_get(v_val_1251_, 0);
lean_inc_ref(v_toConstantVal_1255_);
v_numParams_1256_ = lean_ctor_get(v_val_1251_, 1);
lean_inc(v_numParams_1256_);
v_numIndices_1257_ = lean_ctor_get(v_val_1251_, 2);
lean_inc(v_numIndices_1257_);
v_ctors_1258_ = lean_ctor_get(v_val_1251_, 4);
lean_inc(v_ctors_1258_);
v_nargs_1259_ = l_Lean_Expr_getAppNumArgs(v_e_1174_);
v_dummy_1260_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1259_);
v___x_1261_ = lean_mk_array(v_nargs_1259_, v_dummy_1260_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_sub(v_nargs_1259_, v___x_1262_);
lean_dec(v_nargs_1259_);
v_args_1264_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1174_, v___x_1261_, v___x_1263_);
v___x_1265_ = lean_nat_add(v_numParams_1256_, v___x_1262_);
v___x_1266_ = lean_nat_add(v___x_1265_, v_numIndices_1257_);
v___x_1267_ = lean_nat_add(v___x_1266_, v___x_1262_);
lean_dec(v___x_1266_);
v___x_1268_ = l_Lean_InductiveVal_numCtors(v_val_1251_);
lean_dec_ref(v_val_1251_);
v___x_1269_ = lean_nat_add(v___x_1267_, v___x_1268_);
lean_dec(v___x_1268_);
v___x_1270_ = lean_array_get_size(v_args_1264_);
v___x_1271_ = lean_nat_dec_le(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_dec(v___x_1269_);
lean_dec(v___x_1267_);
lean_dec(v___x_1265_);
lean_dec_ref(v_args_1264_);
lean_dec(v_ctors_1258_);
lean_dec(v_numIndices_1257_);
lean_dec(v_numParams_1256_);
lean_dec_ref(v_toConstantVal_1255_);
lean_del_object(v___x_1253_);
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
v___x_1272_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1272_);
v___x_1274_ = v___x_1249_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
else
{
lean_object* v___x_1276_; lean_object* v_params_1277_; lean_object* v_motive_1278_; lean_object* v_discrs_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_discrInfos_1282_; lean_object* v_alts_1283_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v_lower_1325_; lean_object* v_upper_1326_; uint8_t v___x_1333_; 
lean_del_object(v___x_1249_);
v___x_1276_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1256_);
lean_inc_ref_n(v_args_1264_, 3);
v_params_1277_ = l_Array_toSubarray___redArg(v_args_1264_, v___x_1276_, v_numParams_1256_);
v_motive_1278_ = lean_array_get(v___x_1194_, v_args_1264_, v_numParams_1256_);
lean_dec(v_numParams_1256_);
lean_inc(v___x_1267_);
v_discrs_1279_ = l_Array_toSubarray___redArg(v_args_1264_, v___x_1265_, v___x_1267_);
v___x_1280_ = lean_nat_add(v_numIndices_1257_, v___x_1262_);
lean_dec(v_numIndices_1257_);
v___x_1281_ = lean_box(0);
v_discrInfos_1282_ = lean_mk_array(v___x_1280_, v___x_1281_);
lean_inc(v___x_1269_);
v_alts_1283_ = l_Array_toSubarray___redArg(v_args_1264_, v___x_1267_, v___x_1269_);
v___x_1333_ = lean_nat_dec_le(v___x_1269_, v___x_1276_);
if (v___x_1333_ == 0)
{
v_lower_1325_ = v___x_1269_;
v_upper_1326_ = v___x_1270_;
goto v___jp_1324_;
}
else
{
lean_dec(v___x_1269_);
v_lower_1325_ = v___x_1276_;
v_upper_1326_ = v___x_1270_;
goto v___jp_1324_;
}
v___jp_1284_:
{
lean_object* v___x_1287_; size_t v_sz_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_array_mk(v_ctors_1258_);
v_sz_1288_ = lean_array_size(v___x_1287_);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1288_, v___x_1289_, v___x_1287_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1315_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_start_1295_; lean_object* v_stop_1296_; lean_object* v_start_1297_; lean_object* v_stop_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v_start_1295_ = lean_ctor_get(v_params_1277_, 1);
lean_inc(v_start_1295_);
v_stop_1296_ = lean_ctor_get(v_params_1277_, 2);
lean_inc(v_stop_1296_);
v_start_1297_ = lean_ctor_get(v_discrs_1279_, 1);
lean_inc(v_start_1297_);
v_stop_1298_ = lean_ctor_get(v_discrs_1279_, 2);
lean_inc(v_stop_1298_);
v___x_1299_ = lean_nat_sub(v_stop_1296_, v_start_1295_);
lean_dec(v_start_1295_);
lean_dec(v_stop_1296_);
v___x_1300_ = lean_nat_sub(v_stop_1298_, v_start_1297_);
lean_dec(v_start_1297_);
lean_dec(v_stop_1298_);
v___x_1301_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1299_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v_a_1291_);
lean_ctor_set(v___x_1302_, 3, v___y_1286_);
lean_ctor_set(v___x_1302_, 4, v_discrInfos_1282_);
lean_ctor_set(v___x_1302_, 5, v___x_1301_);
v___x_1303_ = lean_array_mk(v_us_1193_);
v___x_1304_ = l_Subarray_copy___redArg(v_params_1277_);
v___x_1305_ = l_Subarray_copy___redArg(v_discrs_1279_);
v___x_1306_ = l_Subarray_copy___redArg(v_alts_1283_);
v___x_1307_ = l_Subarray_copy___redArg(v___y_1285_);
v___x_1308_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1302_);
lean_ctor_set(v___x_1308_, 1, v_declName_1192_);
lean_ctor_set(v___x_1308_, 2, v___x_1303_);
lean_ctor_set(v___x_1308_, 3, v___x_1304_);
lean_ctor_set(v___x_1308_, 4, v_motive_1278_);
lean_ctor_set(v___x_1308_, 5, v___x_1305_);
lean_ctor_set(v___x_1308_, 6, v___x_1306_);
lean_ctor_set(v___x_1308_, 7, v___x_1307_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1308_);
v___x_1310_ = v___x_1253_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1310_);
v___x_1312_ = v___x_1293_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
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
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_alts_1283_);
lean_dec_ref(v_discrInfos_1282_);
lean_dec_ref(v_discrs_1279_);
lean_dec(v_motive_1278_);
lean_dec_ref(v_params_1277_);
lean_del_object(v___x_1253_);
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
v_a_1316_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1290_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1290_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
v___jp_1324_:
{
lean_object* v_levelParams_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_levelParams_1327_ = lean_ctor_get(v_toConstantVal_1255_, 1);
lean_inc(v_levelParams_1327_);
lean_dec_ref(v_toConstantVal_1255_);
v___x_1328_ = l_Array_toSubarray___redArg(v_args_1264_, v_lower_1325_, v_upper_1326_);
v___x_1329_ = l_List_lengthTR___redArg(v_levelParams_1327_);
lean_dec(v_levelParams_1327_);
v___x_1330_ = l_List_lengthTR___redArg(v_us_1193_);
v___x_1331_ = lean_nat_dec_eq(v___x_1329_, v___x_1330_);
lean_dec(v___x_1330_);
lean_dec(v___x_1329_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1285_ = v___x_1328_;
v___y_1286_ = v___x_1332_;
goto v___jp_1284_;
}
else
{
v___y_1285_ = v___x_1328_;
v___y_1286_ = v___x_1281_;
goto v___jp_1284_;
}
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_a_1247_);
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
lean_dec_ref(v_e_1174_);
v___x_1335_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1335_);
v___x_1337_ = v___x_1249_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
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
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v_us_1193_);
lean_dec(v_declName_1192_);
lean_dec_ref(v_e_1174_);
v_a_1340_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1246_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1246_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
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
lean_dec_ref(v___x_1191_);
lean_dec_ref(v_e_1174_);
goto v___jp_1185_;
}
}
v___jp_1185_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1349_, lean_object* v_alsoCasesOn_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1360_; lean_object* v_res_1361_; 
v_alsoCasesOn_boxed_1360_ = lean_unbox(v_alsoCasesOn_1350_);
v_res_1361_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1349_, v_alsoCasesOn_boxed_1360_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v_b_1367_, lean_object* v_c_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc(v___y_1363_);
v___x_1374_ = lean_apply_11(v_k_1362_, v_b_1367_, v_c_1368_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v_b_1380_, lean_object* v_c_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v_b_1380_, v_c_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec(v___y_1376_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1388_, lean_object* v_maxFVars_1389_, lean_object* v_k_1390_, uint8_t v_cleanupAnnotations_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___f_1401_; uint8_t v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc(v___y_1392_);
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1401_, 0, v_k_1390_);
lean_closure_set(v___f_1401_, 1, v___y_1392_);
lean_closure_set(v___f_1401_, 2, v___y_1393_);
lean_closure_set(v___f_1401_, 3, v___y_1394_);
lean_closure_set(v___f_1401_, 4, v___y_1395_);
v___x_1402_ = 1;
v___x_1403_ = 0;
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_maxFVars_1389_);
v___x_1405_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1388_, v___x_1402_, v___x_1403_, v___x_1402_, v___x_1403_, v___x_1404_, v___f_1401_, v_cleanupAnnotations_1391_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref_known(v___x_1404_, 1);
if (lean_obj_tag(v___x_1405_) == 0)
{
return v___x_1405_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1414_, lean_object* v_maxFVars_1415_, lean_object* v_k_1416_, lean_object* v_cleanupAnnotations_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1427_; lean_object* v_res_1428_; 
v_cleanupAnnotations_boxed_1427_ = lean_unbox(v_cleanupAnnotations_1417_);
v_res_1428_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1414_, v_maxFVars_1415_, v_k_1416_, v_cleanupAnnotations_boxed_1427_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec(v___y_1418_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1431_);
lean_inc(v___y_1430_);
v___x_1440_ = lean_apply_10(v_k_1429_, v_b_1434_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, lean_box(0));
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v_b_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec(v___y_1442_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1453_, lean_object* v_type_1454_, lean_object* v_val_1455_, lean_object* v_k_1456_, uint8_t v_nondep_1457_, uint8_t v_kind_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___f_1468_; lean_object* v___x_1469_; 
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc(v___y_1459_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1468_, 0, v_k_1456_);
lean_closure_set(v___f_1468_, 1, v___y_1459_);
lean_closure_set(v___f_1468_, 2, v___y_1460_);
lean_closure_set(v___f_1468_, 3, v___y_1461_);
lean_closure_set(v___f_1468_, 4, v___y_1462_);
v___x_1469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1453_, v_type_1454_, v_val_1455_, v___f_1468_, v_nondep_1457_, v_kind_1458_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1469_) == 0)
{
return v___x_1469_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1478_, lean_object* v_type_1479_, lean_object* v_val_1480_, lean_object* v_k_1481_, lean_object* v_nondep_1482_, lean_object* v_kind_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v_nondep_boxed_1493_; uint8_t v_kind_boxed_1494_; lean_object* v_res_1495_; 
v_nondep_boxed_1493_ = lean_unbox(v_nondep_1482_);
v_kind_boxed_1494_ = lean_unbox(v_kind_1483_);
v_res_1495_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1478_, v_type_1479_, v_val_1480_, v_k_1481_, v_nondep_boxed_1493_, v_kind_boxed_1494_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1496_, uint8_t v_usedLetOnly_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v_x_1498_);
v___x_1508_ = lean_apply_10(v_k_1496_, v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_mk_empty_array_with_capacity(v___x_1510_);
v___x_1512_ = lean_array_push(v___x_1511_, v_x_1498_);
v___x_1513_ = 0;
v___x_1514_ = 1;
v___x_1515_ = l_Lean_Meta_mkLetFVars(v___x_1512_, v_a_1509_, v_usedLetOnly_1497_, v___x_1513_, v___x_1514_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec_ref(v___x_1512_);
return v___x_1515_;
}
else
{
lean_dec_ref(v_x_1498_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1516_, lean_object* v_usedLetOnly_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v_usedLetOnly_boxed_1528_; lean_object* v_res_1529_; 
v_usedLetOnly_boxed_1528_ = lean_unbox(v_usedLetOnly_1517_);
v_res_1529_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1516_, v_usedLetOnly_boxed_1528_, v_x_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1530_, lean_object* v_type_1531_, lean_object* v_val_1532_, lean_object* v_k_1533_, uint8_t v_nondep_1534_, uint8_t v_kind_1535_, uint8_t v_usedLetOnly_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_box(v_usedLetOnly_1536_);
v___f_1547_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1547_, 0, v_k_1533_);
lean_closure_set(v___f_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1530_, v_type_1531_, v_val_1532_, v___f_1547_, v_nondep_1534_, v_kind_1535_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1549_, lean_object* v_type_1550_, lean_object* v_val_1551_, lean_object* v_k_1552_, lean_object* v_nondep_1553_, lean_object* v_kind_1554_, lean_object* v_usedLetOnly_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_nondep_boxed_1565_; uint8_t v_kind_boxed_1566_; uint8_t v_usedLetOnly_boxed_1567_; lean_object* v_res_1568_; 
v_nondep_boxed_1565_ = lean_unbox(v_nondep_1553_);
v_kind_boxed_1566_ = lean_unbox(v_kind_1554_);
v_usedLetOnly_boxed_1567_ = lean_unbox(v_usedLetOnly_1555_);
v_res_1568_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1549_, v_type_1550_, v_val_1551_, v_k_1552_, v_nondep_boxed_1565_, v_kind_boxed_1566_, v_usedLetOnly_boxed_1567_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1569_, uint8_t v_bi_1570_, lean_object* v_type_1571_, lean_object* v_k_1572_, uint8_t v_kind_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___f_1583_; lean_object* v___x_1584_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc(v___y_1574_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1583_, 0, v_k_1572_);
lean_closure_set(v___f_1583_, 1, v___y_1574_);
lean_closure_set(v___f_1583_, 2, v___y_1575_);
lean_closure_set(v___f_1583_, 3, v___y_1576_);
lean_closure_set(v___f_1583_, 4, v___y_1577_);
v___x_1584_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1569_, v_bi_1570_, v_type_1571_, v___f_1583_, v_kind_1573_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
return v___x_1584_;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1593_, lean_object* v_bi_1594_, lean_object* v_type_1595_, lean_object* v_k_1596_, lean_object* v_kind_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v_bi_boxed_1607_; uint8_t v_kind_boxed_1608_; lean_object* v_res_1609_; 
v_bi_boxed_1607_ = lean_unbox(v_bi_1594_);
v_kind_boxed_1608_ = lean_unbox(v_kind_1597_);
v_res_1609_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1593_, v_bi_boxed_1607_, v_type_1595_, v_k_1596_, v_kind_boxed_1608_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec(v___y_1598_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc(v___y_1611_);
v___x_1620_ = lean_apply_9(v_k_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, lean_box(0));
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1622_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1632_, uint8_t v_allowLevelAssignments_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___f_1643_; lean_object* v___x_1644_; 
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc(v___y_1634_);
v___f_1643_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1643_, 0, v_k_1632_);
lean_closure_set(v___f_1643_, 1, v___y_1634_);
lean_closure_set(v___f_1643_, 2, v___y_1635_);
lean_closure_set(v___f_1643_, 3, v___y_1636_);
lean_closure_set(v___f_1643_, 4, v___y_1637_);
v___x_1644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1633_, v___f_1643_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1644_) == 0)
{
return v___x_1644_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1653_, lean_object* v_allowLevelAssignments_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1664_; lean_object* v_res_1665_; 
v_allowLevelAssignments_boxed_1664_ = lean_unbox(v_allowLevelAssignments_1654_);
v_res_1665_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1653_, v_allowLevelAssignments_boxed_1664_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec(v___y_1655_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_box(0);
return v___x_1668_;
}
else
{
lean_object* v_key_1669_; lean_object* v_value_1670_; lean_object* v_tail_1671_; uint8_t v___x_1672_; 
v_key_1669_ = lean_ctor_get(v_x_1667_, 0);
v_value_1670_ = lean_ctor_get(v_x_1667_, 1);
v_tail_1671_ = lean_ctor_get(v_x_1667_, 2);
v___x_1672_ = lean_expr_eqv(v_key_1669_, v_a_1666_);
if (v___x_1672_ == 0)
{
v_x_1667_ = v_tail_1671_;
goto _start;
}
else
{
lean_object* v___x_1674_; 
lean_inc(v_value_1670_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_value_1670_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1675_, v_x_1676_);
lean_dec(v_x_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_buckets_1680_; lean_object* v___x_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; uint64_t v_fold_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; size_t v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_buckets_1680_ = lean_ctor_get(v_m_1678_, 1);
v___x_1681_ = lean_array_get_size(v_buckets_1680_);
v___x_1682_ = l_Lean_Expr_hash(v_a_1679_);
v___x_1683_ = 32ULL;
v___x_1684_ = lean_uint64_shift_right(v___x_1682_, v___x_1683_);
v_fold_1685_ = lean_uint64_xor(v___x_1682_, v___x_1684_);
v___x_1686_ = 16ULL;
v___x_1687_ = lean_uint64_shift_right(v_fold_1685_, v___x_1686_);
v___x_1688_ = lean_uint64_xor(v_fold_1685_, v___x_1687_);
v___x_1689_ = lean_uint64_to_usize(v___x_1688_);
v___x_1690_ = lean_usize_of_nat(v___x_1681_);
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_sub(v___x_1690_, v___x_1691_);
v___x_1693_ = lean_usize_land(v___x_1689_, v___x_1692_);
v___x_1694_ = lean_array_uget_borrowed(v_buckets_1680_, v___x_1693_);
v___x_1695_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1679_, v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1696_, v_a_1697_);
lean_dec_ref(v_a_1697_);
lean_dec_ref(v_m_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1699_, lean_object* v_opt_1700_){
_start:
{
lean_object* v_name_1701_; lean_object* v_defValue_1702_; lean_object* v_map_1703_; lean_object* v___x_1704_; 
v_name_1701_ = lean_ctor_get(v_opt_1700_, 0);
v_defValue_1702_ = lean_ctor_get(v_opt_1700_, 1);
v_map_1703_ = lean_ctor_get(v_opts_1699_, 0);
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1703_, v_name_1701_);
if (lean_obj_tag(v___x_1704_) == 0)
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_unbox(v_defValue_1702_);
return v___x_1705_;
}
else
{
lean_object* v_val_1706_; 
v_val_1706_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1706_);
lean_dec_ref_known(v___x_1704_, 1);
if (lean_obj_tag(v_val_1706_) == 1)
{
uint8_t v_v_1707_; 
v_v_1707_ = lean_ctor_get_uint8(v_val_1706_, 0);
lean_dec_ref_known(v_val_1706_, 0);
return v_v_1707_;
}
else
{
uint8_t v___x_1708_; 
lean_dec(v_val_1706_);
v___x_1708_ = lean_unbox(v_defValue_1702_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1709_, lean_object* v_opt_1710_){
_start:
{
uint8_t v_res_1711_; lean_object* v_r_1712_; 
v_res_1711_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1709_, v_opt_1710_);
lean_dec_ref(v_opt_1710_);
lean_dec_ref(v_opts_1709_);
v_r_1712_ = lean_box(v_res_1711_);
return v_r_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1713_, lean_object* v_b_1714_){
_start:
{
lean_object* v_array_1715_; lean_object* v_start_1716_; lean_object* v_stop_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1730_; 
v_array_1715_ = lean_ctor_get(v_a_1713_, 0);
v_start_1716_ = lean_ctor_get(v_a_1713_, 1);
v_stop_1717_ = lean_ctor_get(v_a_1713_, 2);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1719_ = v_a_1713_;
v_isShared_1720_ = v_isSharedCheck_1730_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_stop_1717_);
lean_inc(v_start_1716_);
lean_inc(v_array_1715_);
lean_dec(v_a_1713_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1730_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_nat_dec_lt(v_start_1716_, v_stop_1717_);
if (v___x_1721_ == 0)
{
lean_del_object(v___x_1719_);
lean_dec(v_stop_1717_);
lean_dec(v_start_1716_);
lean_dec_ref(v_array_1715_);
return v_b_1714_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_add(v_start_1716_, v___x_1722_);
lean_inc_ref(v_array_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1723_);
v___x_1725_ = v___x_1719_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_array_1715_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_stop_1717_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_array_fget(v_array_1715_, v_start_1716_);
lean_dec(v_start_1716_);
lean_dec_ref(v_array_1715_);
v___x_1727_ = lean_array_push(v_b_1714_, v___x_1726_);
v_a_1713_ = v___x_1725_;
v_b_1714_ = v___x_1727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1731_, lean_object* v_recFnName_1732_, lean_object* v_fixedPrefixSize_1733_, lean_object* v_F_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_expr_instantiate1(v_body_1731_, v_x_1735_);
v___x_1746_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1732_, v_fixedPrefixSize_1733_, v_F_1734_, v___x_1745_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_mk_empty_array_with_capacity(v___x_1748_);
v___x_1750_ = lean_array_push(v___x_1749_, v_x_1735_);
v___x_1751_ = 0;
v___x_1752_ = 1;
v___x_1753_ = 1;
v___x_1754_ = l_Lean_Meta_mkLambdaFVars(v___x_1750_, v_a_1747_, v___x_1751_, v___x_1752_, v___x_1751_, v___x_1752_, v___x_1753_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec_ref(v___x_1750_);
return v___x_1754_;
}
else
{
lean_dec_ref(v_x_1735_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1755_, lean_object* v_recFnName_1756_, lean_object* v_fixedPrefixSize_1757_, lean_object* v_F_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1755_, v_recFnName_1756_, v_fixedPrefixSize_1757_, v_F_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v_body_1755_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1770_, lean_object* v_recFnName_1771_, lean_object* v_fixedPrefixSize_1772_, lean_object* v_F_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_expr_instantiate1(v_body_1770_, v_x_1774_);
v___x_1785_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1771_, v_fixedPrefixSize_1772_, v_F_1773_, v___x_1784_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
v___x_1789_ = lean_array_push(v___x_1788_, v_x_1774_);
v___x_1790_ = 0;
v___x_1791_ = 1;
v___x_1792_ = 1;
v___x_1793_ = l_Lean_Meta_mkForallFVars(v___x_1789_, v_a_1786_, v___x_1790_, v___x_1791_, v___x_1791_, v___x_1792_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec_ref(v___x_1789_);
return v___x_1793_;
}
else
{
lean_dec_ref(v_x_1774_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1794_, lean_object* v_recFnName_1795_, lean_object* v_fixedPrefixSize_1796_, lean_object* v_F_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1794_, v_recFnName_1795_, v_fixedPrefixSize_1796_, v_F_1797_, v_x_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v_body_1794_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1809_, lean_object* v_recFnName_1810_, lean_object* v_fixedPrefixSize_1811_, lean_object* v_F_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1809_, v_recFnName_1810_, v_fixedPrefixSize_1811_, v_F_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v_x_1813_);
lean_dec_ref(v_body_1809_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1826_, lean_object* v_fixedPrefixSize_1827_, lean_object* v_F_1828_, size_t v_sz_1829_, size_t v_i_1830_, lean_object* v_bs_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_usize_dec_lt(v_i_1830_, v_sz_1829_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v_F_1828_);
lean_dec(v_fixedPrefixSize_1827_);
lean_dec(v_recFnName_1826_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_bs_1831_);
return v___x_1842_;
}
else
{
lean_object* v_v_1843_; lean_object* v___x_1844_; lean_object* v_bs_x27_1845_; lean_object* v___x_1846_; 
v_v_1843_ = lean_array_uget(v_bs_1831_, v_i_1830_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v_bs_x27_1845_ = lean_array_uset(v_bs_1831_, v_i_1830_, v___x_1844_);
lean_inc_ref(v_F_1828_);
lean_inc(v_fixedPrefixSize_1827_);
lean_inc(v_recFnName_1826_);
v___x_1846_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1826_, v_fixedPrefixSize_1827_, v_F_1828_, v_v_1843_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1830_, v___x_1848_);
v___x_1850_ = lean_array_uset(v_bs_x27_1845_, v_i_1830_, v_a_1847_);
v_i_1830_ = v___x_1849_;
v_bs_1831_ = v___x_1850_;
goto _start;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_bs_x27_1845_);
lean_dec_ref(v_F_1828_);
lean_dec(v_fixedPrefixSize_1827_);
lean_dec(v_recFnName_1826_);
v_a_1852_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1846_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1846_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_cls_1867_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1869_ = l_Lean_Name_append(v___x_1868_, v_cls_1867_);
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1873_, lean_object* v_fixedPrefixSize_1874_, lean_object* v_F_1875_, lean_object* v_e_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1898_ = l_Lean_Expr_getAppNumArgs(v_e_1876_);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_fixedPrefixSize_1874_, v___x_1899_);
v___x_1901_ = lean_nat_dec_lt(v___x_1898_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v_dummy_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_args_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1902_ = l_Lean_instInhabitedExpr;
v_dummy_1903_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1898_);
v___x_1904_ = lean_mk_array(v___x_1898_, v_dummy_1903_);
v___x_1905_ = lean_nat_sub(v___x_1898_, v___x_1899_);
lean_dec(v___x_1898_);
v_args_1906_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1876_, v___x_1904_, v___x_1905_);
v___x_1907_ = lean_array_get(v___x_1902_, v_args_1906_, v_fixedPrefixSize_1874_);
lean_inc_ref(v_F_1875_);
lean_inc(v_fixedPrefixSize_1874_);
lean_inc(v_recFnName_1873_);
v___x_1908_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1873_, v_fixedPrefixSize_1874_, v_F_1875_, v___x_1907_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
lean_inc_ref(v_F_1875_);
v___x_1910_ = l_Lean_Expr_app___override(v_F_1875_, v_a_1909_);
lean_inc(v_a_1884_);
lean_inc_ref(v_a_1883_);
lean_inc(v_a_1882_);
lean_inc_ref(v_a_1881_);
lean_inc_ref(v___x_1910_);
v___x_1911_ = lean_infer_type(v___x_1910_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
lean_inc(v_a_1884_);
lean_inc_ref(v_a_1883_);
lean_inc(v_a_1882_);
lean_inc_ref(v_a_1881_);
v___x_1913_ = lean_whnf(v_a_1912_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Expr_bindingDomain_x21(v_a_1914_);
lean_dec(v_a_1914_);
v___x_1916_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1915_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v_lower_1920_; lean_object* v_upper_1921_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l_Lean_Expr_app___override(v___x_1910_, v_a_1917_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_array_get_size(v_args_1906_);
v___x_1947_ = lean_nat_dec_le(v___x_1900_, v___x_1945_);
if (v___x_1947_ == 0)
{
v_lower_1920_ = v___x_1900_;
v_upper_1921_ = v___x_1946_;
goto v___jp_1919_;
}
else
{
lean_dec(v___x_1900_);
v_lower_1920_ = v___x_1945_;
v_upper_1921_ = v___x_1946_;
goto v___jp_1919_;
}
v___jp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; size_t v_sz_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1922_ = l_Array_toSubarray___redArg(v_args_1906_, v_lower_1920_, v_upper_1921_);
v___x_1923_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1924_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1922_, v___x_1923_);
v_sz_1925_ = lean_array_size(v___x_1924_);
v___x_1926_ = ((size_t)0ULL);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1873_, v_fixedPrefixSize_1874_, v_F_1875_, v_sz_1925_, v___x_1926_, v___x_1924_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_mkAppN(v___x_1918_, v_a_1928_);
lean_dec(v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v___x_1918_);
v_a_1937_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1927_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_args_1906_);
lean_dec(v___x_1900_);
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
return v___x_1916_;
}
}
else
{
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_args_1906_);
lean_dec(v___x_1900_);
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
return v___x_1913_;
}
}
else
{
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_args_1906_);
lean_dec(v___x_1900_);
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
return v___x_1911_;
}
}
else
{
lean_dec_ref(v_args_1906_);
lean_dec(v___x_1900_);
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
return v___x_1908_;
}
}
else
{
lean_object* v_toCold_1948_; lean_object* v_options_1949_; uint8_t v_hasTrace_1950_; 
lean_dec(v___x_1900_);
lean_dec(v___x_1898_);
v_toCold_1948_ = lean_ctor_get(v_a_1883_, 0);
v_options_1949_ = lean_ctor_get(v_toCold_1948_, 2);
v_hasTrace_1950_ = lean_ctor_get_uint8(v_options_1949_, sizeof(void*)*1);
if (v_hasTrace_1950_ == 0)
{
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
goto v___jp_1886_;
}
else
{
lean_object* v_inheritedTraceOptions_1951_; lean_object* v_cls_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_inheritedTraceOptions_1951_ = lean_ctor_get(v_toCold_1948_, 11);
v_cls_1952_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1953_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1954_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1951_, v_options_1949_, v___x_1953_);
if (v___x_1954_ == 0)
{
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1955_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1876_);
v___x_1956_ = l_Lean_indentExpr(v_e_1876_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1952_, v___x_1957_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
goto v___jp_1886_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_e_1876_);
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_etaExpand(v_e_1876_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1873_, v_fixedPrefixSize_1874_, v_F_1875_, v_a_1896_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1897_;
}
else
{
lean_dec_ref(v_F_1875_);
lean_dec(v_fixedPrefixSize_1874_);
lean_dec(v_recFnName_1873_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1967_, lean_object* v_fixedPrefixSize_1968_, lean_object* v_F_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 5)
{
lean_object* v_fn_1982_; lean_object* v_arg_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_fn_1982_ = lean_ctor_get(v_x_1970_, 0);
lean_inc_ref(v_fn_1982_);
v_arg_1983_ = lean_ctor_get(v_x_1970_, 1);
lean_inc_ref(v_arg_1983_);
lean_dec_ref_known(v_x_1970_, 2);
v___x_1984_ = lean_array_set(v_x_1971_, v_x_1972_, v_arg_1983_);
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = lean_nat_sub(v_x_1972_, v___x_1985_);
lean_dec(v_x_1972_);
v_x_1970_ = v_fn_1982_;
v_x_1971_ = v___x_1984_;
v_x_1972_ = v___x_1986_;
goto _start;
}
else
{
lean_object* v___x_1988_; 
lean_dec(v_x_1972_);
lean_inc_ref(v_F_1969_);
lean_inc(v_fixedPrefixSize_1968_);
lean_inc(v_recFnName_1967_);
v___x_1988_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1967_, v_fixedPrefixSize_1968_, v_F_1969_, v_x_1970_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; size_t v_sz_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v_sz_1990_ = lean_array_size(v_x_1971_);
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1967_, v_fixedPrefixSize_1968_, v_F_1969_, v_sz_1990_, v___x_1991_, v_x_1971_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2001_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = l_Lean_mkAppN(v_a_1989_, v_a_1993_);
lean_dec(v_a_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1997_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_a_1989_);
v_a_2002_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1992_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1992_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_dec_ref(v_x_1971_);
lean_dec_ref(v_F_1969_);
lean_dec(v_fixedPrefixSize_1968_);
lean_dec(v_recFnName_1967_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2010_, lean_object* v_fixedPrefixSize_2011_, lean_object* v_F_2012_, lean_object* v_e_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Expr_isAppOf(v_e_2013_, v_recFnName_2010_);
if (v___x_2023_ == 0)
{
lean_object* v_dummy_2024_; lean_object* v_nargs_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_dummy_2024_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2025_ = l_Lean_Expr_getAppNumArgs(v_e_2013_);
lean_inc(v_nargs_2025_);
v___x_2026_ = lean_mk_array(v_nargs_2025_, v_dummy_2024_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_sub(v_nargs_2025_, v___x_2027_);
lean_dec(v_nargs_2025_);
v___x_2029_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2010_, v_fixedPrefixSize_2011_, v_F_2012_, v_e_2013_, v___x_2026_, v___x_2028_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2010_, v_fixedPrefixSize_2011_, v_F_2012_, v_e_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
return v___x_2030_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2037_, lean_object* v_b_2038_, lean_object* v_recFnName_2039_, lean_object* v_fixedPrefixSize_2040_, uint8_t v___x_2041_, lean_object* v___x_2042_, lean_object* v_a_2043_, lean_object* v_e_2044_, lean_object* v_xs_2045_, lean_object* v_altBody_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_array_get_size(v_xs_2045_);
v___x_2064_ = lean_nat_dec_eq(v___x_2063_, v___x_2042_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_altBody_2046_);
lean_dec(v_fixedPrefixSize_2040_);
lean_dec(v_recFnName_2039_);
v___x_2065_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2066_ = l_Lean_indentExpr(v_a_2043_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_indentExpr(v_e_2044_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2071_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_dec_ref(v_e_2044_);
lean_dec_ref(v_a_2043_);
goto v___jp_2056_;
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_array_get_borrowed(v___x_2037_, v_xs_2045_, v_b_2038_);
lean_inc(v___x_2057_);
v___x_2058_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2039_, v_fixedPrefixSize_2040_, v___x_2057_, v_altBody_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; uint8_t v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = 0;
v___x_2061_ = 1;
v___x_2062_ = l_Lean_Meta_mkLambdaFVars(v_xs_2045_, v_a_2059_, v___x_2060_, v___x_2041_, v___x_2060_, v___x_2041_, v___x_2061_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
return v___x_2062_;
}
else
{
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2081_ = _args[0];
lean_object* v_b_2082_ = _args[1];
lean_object* v_recFnName_2083_ = _args[2];
lean_object* v_fixedPrefixSize_2084_ = _args[3];
lean_object* v___x_2085_ = _args[4];
lean_object* v___x_2086_ = _args[5];
lean_object* v_a_2087_ = _args[6];
lean_object* v_e_2088_ = _args[7];
lean_object* v_xs_2089_ = _args[8];
lean_object* v_altBody_2090_ = _args[9];
lean_object* v___y_2091_ = _args[10];
lean_object* v___y_2092_ = _args[11];
lean_object* v___y_2093_ = _args[12];
lean_object* v___y_2094_ = _args[13];
lean_object* v___y_2095_ = _args[14];
lean_object* v___y_2096_ = _args[15];
lean_object* v___y_2097_ = _args[16];
lean_object* v___y_2098_ = _args[17];
lean_object* v___y_2099_ = _args[18];
_start:
{
uint8_t v___x_57750__boxed_2100_; lean_object* v_res_2101_; 
v___x_57750__boxed_2100_ = lean_unbox(v___x_2085_);
v_res_2101_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2081_, v_b_2082_, v_recFnName_2083_, v_fixedPrefixSize_2084_, v___x_57750__boxed_2100_, v___x_2086_, v_a_2087_, v_e_2088_, v_xs_2089_, v_altBody_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v_xs_2089_);
lean_dec(v___x_2086_);
lean_dec(v_b_2082_);
lean_dec_ref(v___x_2081_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2102_, lean_object* v_fixedPrefixSize_2103_, lean_object* v_e_2104_, lean_object* v_as_2105_, lean_object* v_bs_2106_, lean_object* v_i_2107_, lean_object* v_cs_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_array_get_size(v_as_2105_);
v___x_2119_ = lean_nat_dec_lt(v_i_2107_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_i_2107_);
lean_dec_ref(v_e_2104_);
lean_dec(v_fixedPrefixSize_2103_);
lean_dec(v_recFnName_2102_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_cs_2108_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_array_get_size(v_bs_2106_);
v___x_2122_ = lean_nat_dec_lt(v_i_2107_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_i_2107_);
lean_dec_ref(v_e_2104_);
lean_dec(v_fixedPrefixSize_2103_);
lean_dec(v_recFnName_2102_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_cs_2108_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v_b_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2124_ = l_Lean_instInhabitedExpr;
v_a_2125_ = lean_array_fget_borrowed(v_as_2105_, v_i_2107_);
v_b_2126_ = lean_array_fget_borrowed(v_bs_2106_, v_i_2107_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_add(v_b_2126_, v___x_2127_);
v___x_2129_ = lean_box(v___x_2122_);
lean_inc_ref(v_e_2104_);
lean_inc_n(v_a_2125_, 2);
lean_inc(v___x_2128_);
lean_inc(v_fixedPrefixSize_2103_);
lean_inc(v_recFnName_2102_);
lean_inc(v_b_2126_);
v___f_2130_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2130_, 0, v___x_2124_);
lean_closure_set(v___f_2130_, 1, v_b_2126_);
lean_closure_set(v___f_2130_, 2, v_recFnName_2102_);
lean_closure_set(v___f_2130_, 3, v_fixedPrefixSize_2103_);
lean_closure_set(v___f_2130_, 4, v___x_2129_);
lean_closure_set(v___f_2130_, 5, v___x_2128_);
lean_closure_set(v___f_2130_, 6, v_a_2125_);
lean_closure_set(v___f_2130_, 7, v_e_2104_);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2125_, v___x_2128_, v___f_2130_, v___x_2131_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = lean_nat_add(v_i_2107_, v___x_2127_);
lean_dec(v_i_2107_);
v___x_2135_ = lean_array_push(v_cs_2108_, v_a_2133_);
v_i_2107_ = v___x_2134_;
v_cs_2108_ = v___x_2135_;
goto _start;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_cs_2108_);
lean_dec(v_i_2107_);
lean_dec_ref(v_e_2104_);
lean_dec(v_fixedPrefixSize_2103_);
lean_dec(v_recFnName_2102_);
v_a_2137_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2132_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2145_, lean_object* v_fixedPrefixSize_2146_, lean_object* v_F_2147_, lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
switch(lean_obj_tag(v_e_2148_))
{
case 6:
{
lean_object* v_binderName_2158_; lean_object* v_binderType_2159_; lean_object* v_body_2160_; uint8_t v_binderInfo_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; 
v_binderName_2158_ = lean_ctor_get(v_e_2148_, 0);
lean_inc(v_binderName_2158_);
v_binderType_2159_ = lean_ctor_get(v_e_2148_, 1);
lean_inc_ref(v_binderType_2159_);
v_body_2160_ = lean_ctor_get(v_e_2148_, 2);
lean_inc_ref(v_body_2160_);
v_binderInfo_2161_ = lean_ctor_get_uint8(v_e_2148_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2148_, 3);
lean_inc_ref(v_F_2147_);
lean_inc(v_fixedPrefixSize_2146_);
lean_inc(v_recFnName_2145_);
v___f_2162_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2162_, 0, v_body_2160_);
lean_closure_set(v___f_2162_, 1, v_recFnName_2145_);
lean_closure_set(v___f_2162_, 2, v_fixedPrefixSize_2146_);
lean_closure_set(v___f_2162_, 3, v_F_2147_);
v___x_2163_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_binderType_2159_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = 0;
v___x_2166_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2158_, v_binderInfo_2161_, v_a_2164_, v___f_2162_, v___x_2165_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2166_;
}
else
{
lean_dec_ref(v___f_2162_);
lean_dec(v_binderName_2158_);
return v___x_2163_;
}
}
case 7:
{
lean_object* v_binderName_2167_; lean_object* v_binderType_2168_; lean_object* v_body_2169_; uint8_t v_binderInfo_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; 
v_binderName_2167_ = lean_ctor_get(v_e_2148_, 0);
lean_inc(v_binderName_2167_);
v_binderType_2168_ = lean_ctor_get(v_e_2148_, 1);
lean_inc_ref(v_binderType_2168_);
v_body_2169_ = lean_ctor_get(v_e_2148_, 2);
lean_inc_ref(v_body_2169_);
v_binderInfo_2170_ = lean_ctor_get_uint8(v_e_2148_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2148_, 3);
lean_inc_ref(v_F_2147_);
lean_inc(v_fixedPrefixSize_2146_);
lean_inc(v_recFnName_2145_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2171_, 0, v_body_2169_);
lean_closure_set(v___f_2171_, 1, v_recFnName_2145_);
lean_closure_set(v___f_2171_, 2, v_fixedPrefixSize_2146_);
lean_closure_set(v___f_2171_, 3, v_F_2147_);
v___x_2172_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_binderType_2168_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = 0;
v___x_2175_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2167_, v_binderInfo_2170_, v_a_2173_, v___f_2171_, v___x_2174_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2175_;
}
else
{
lean_dec_ref(v___f_2171_);
lean_dec(v_binderName_2167_);
return v___x_2172_;
}
}
case 8:
{
lean_object* v_declName_2176_; lean_object* v_type_2177_; lean_object* v_value_2178_; lean_object* v_body_2179_; uint8_t v_nondep_2180_; lean_object* v___f_2181_; lean_object* v___x_2182_; 
v_declName_2176_ = lean_ctor_get(v_e_2148_, 0);
lean_inc(v_declName_2176_);
v_type_2177_ = lean_ctor_get(v_e_2148_, 1);
lean_inc_ref(v_type_2177_);
v_value_2178_ = lean_ctor_get(v_e_2148_, 2);
lean_inc_ref(v_value_2178_);
v_body_2179_ = lean_ctor_get(v_e_2148_, 3);
lean_inc_ref(v_body_2179_);
v_nondep_2180_ = lean_ctor_get_uint8(v_e_2148_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2148_, 4);
lean_inc_ref_n(v_F_2147_, 2);
lean_inc_n(v_fixedPrefixSize_2146_, 2);
lean_inc_n(v_recFnName_2145_, 2);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2181_, 0, v_body_2179_);
lean_closure_set(v___f_2181_, 1, v_recFnName_2145_);
lean_closure_set(v___f_2181_, 2, v_fixedPrefixSize_2146_);
lean_closure_set(v___f_2181_, 3, v_F_2147_);
v___x_2182_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_type_2177_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_value_2178_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; uint8_t v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = 0;
v___x_2187_ = 0;
v___x_2188_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2176_, v_a_2183_, v_a_2185_, v___f_2181_, v_nondep_2180_, v___x_2186_, v___x_2187_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2188_;
}
else
{
lean_dec(v_a_2183_);
lean_dec_ref(v___f_2181_);
lean_dec(v_declName_2176_);
return v___x_2184_;
}
}
else
{
lean_dec_ref(v___f_2181_);
lean_dec_ref(v_value_2178_);
lean_dec(v_declName_2176_);
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
lean_dec(v_recFnName_2145_);
return v___x_2182_;
}
}
case 10:
{
lean_object* v_data_2189_; lean_object* v_expr_2190_; lean_object* v___x_2191_; 
v_data_2189_ = lean_ctor_get(v_e_2148_, 0);
lean_inc(v_data_2189_);
v_expr_2190_ = lean_ctor_get(v_e_2148_, 1);
lean_inc_ref(v_expr_2190_);
v___x_2191_ = l_Lean_getRecAppSyntax_x3f(v_e_2148_);
lean_dec_ref_known(v_e_2148_, 2);
if (lean_obj_tag(v___x_2191_) == 1)
{
lean_object* v_val_2192_; lean_object* v_toCold_2193_; lean_object* v_currRecDepth_2194_; lean_object* v_ref_2195_; uint16_t v_optionFlags_2196_; uint8_t v_suppressElabErrors_2197_; uint8_t v_isRecordingDeps_2198_; lean_object* v_ref_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_data_2189_);
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v_toCold_2193_ = lean_ctor_get(v_a_2155_, 0);
v_currRecDepth_2194_ = lean_ctor_get(v_a_2155_, 1);
v_ref_2195_ = lean_ctor_get(v_a_2155_, 2);
v_optionFlags_2196_ = lean_ctor_get_uint16(v_a_2155_, sizeof(void*)*3);
v_suppressElabErrors_2197_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2198_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*3 + 3);
v_ref_2199_ = l_Lean_replaceRef(v_val_2192_, v_ref_2195_);
lean_dec(v_val_2192_);
lean_inc(v_currRecDepth_2194_);
lean_inc_ref(v_toCold_2193_);
v___x_2200_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2200_, 0, v_toCold_2193_);
lean_ctor_set(v___x_2200_, 1, v_currRecDepth_2194_);
lean_ctor_set(v___x_2200_, 2, v_ref_2199_);
lean_ctor_set_uint16(v___x_2200_, sizeof(void*)*3, v_optionFlags_2196_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*3 + 2, v_suppressElabErrors_2197_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*3 + 3, v_isRecordingDeps_2198_);
v___x_2201_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_expr_2190_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v___x_2200_, v_a_2156_);
lean_dec_ref_known(v___x_2200_, 3);
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; 
lean_dec(v___x_2191_);
v___x_2202_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_expr_2190_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_mkMData(v_data_2189_, v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_dec(v_data_2189_);
return v___x_2202_;
}
}
}
case 11:
{
lean_object* v_typeName_2212_; lean_object* v_idx_2213_; lean_object* v_struct_2214_; lean_object* v___x_2215_; 
v_typeName_2212_ = lean_ctor_get(v_e_2148_, 0);
lean_inc(v_typeName_2212_);
v_idx_2213_ = lean_ctor_get(v_e_2148_, 1);
lean_inc(v_idx_2213_);
v_struct_2214_ = lean_ctor_get(v_e_2148_, 2);
lean_inc_ref(v_struct_2214_);
lean_dec_ref_known(v_e_2148_, 3);
v___x_2215_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_struct_2214_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_mkProj(v_typeName_2212_, v_idx_2213_, v_a_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
else
{
lean_dec(v_idx_2213_);
lean_dec(v_typeName_2212_);
return v___x_2215_;
}
}
case 4:
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Lean_Expr_isConstOf(v_e_2148_, v_recFnName_2145_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
lean_dec(v_recFnName_2145_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_e_2148_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_e_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2227_;
}
}
case 5:
{
uint8_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = 1;
lean_inc_ref(v_e_2148_);
v___x_2229_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2148_, v___x_2228_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_e_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2233_; 
v_val_2232_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v_a_2230_, 1);
lean_inc_ref(v_F_2147_);
v___x_2233_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2232_, v_F_2147_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
if (lean_obj_tag(v_a_2234_) == 1)
{
lean_object* v_val_2235_; lean_object* v_toMatcherInfo_2236_; lean_object* v_matcherName_2237_; lean_object* v_matcherLevels_2238_; lean_object* v_params_2239_; lean_object* v_motive_2240_; lean_object* v_discrs_2241_; lean_object* v_alts_2242_; lean_object* v_remaining_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_val_2235_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v_a_2234_, 1);
v_toMatcherInfo_2236_ = lean_ctor_get(v_val_2235_, 0);
lean_inc_ref(v_toMatcherInfo_2236_);
v_matcherName_2237_ = lean_ctor_get(v_val_2235_, 1);
lean_inc(v_matcherName_2237_);
v_matcherLevels_2238_ = lean_ctor_get(v_val_2235_, 2);
lean_inc_ref(v_matcherLevels_2238_);
v_params_2239_ = lean_ctor_get(v_val_2235_, 3);
lean_inc_ref(v_params_2239_);
v_motive_2240_ = lean_ctor_get(v_val_2235_, 4);
lean_inc_ref(v_motive_2240_);
v_discrs_2241_ = lean_ctor_get(v_val_2235_, 5);
lean_inc_ref(v_discrs_2241_);
v_alts_2242_ = lean_ctor_get(v_val_2235_, 6);
lean_inc_ref(v_alts_2242_);
v_remaining_2243_ = lean_ctor_get(v_val_2235_, 7);
lean_inc_ref(v_remaining_2243_);
v___x_2244_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2235_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2146_);
lean_inc(v_recFnName_2145_);
v___x_2247_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_e_2148_, v_alts_2242_, v___x_2244_, v___x_2245_, v___x_2246_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_alts_2242_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; size_t v_sz_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v_sz_2249_ = lean_array_size(v_discrs_2241_);
v___x_2250_ = ((size_t)0ULL);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_sz_2249_, v___x_2250_, v_discrs_2241_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2261_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2256_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2256_, 0, v_toMatcherInfo_2236_);
lean_ctor_set(v___x_2256_, 1, v_matcherName_2237_);
lean_ctor_set(v___x_2256_, 2, v_matcherLevels_2238_);
lean_ctor_set(v___x_2256_, 3, v_params_2239_);
lean_ctor_set(v___x_2256_, 4, v_motive_2240_);
lean_ctor_set(v___x_2256_, 5, v_a_2252_);
lean_ctor_set(v___x_2256_, 6, v_a_2248_);
lean_ctor_set(v___x_2256_, 7, v_remaining_2243_);
v___x_2257_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2256_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_2248_);
lean_dec_ref(v_remaining_2243_);
lean_dec_ref(v_motive_2240_);
lean_dec_ref(v_params_2239_);
lean_dec_ref(v_matcherLevels_2238_);
lean_dec(v_matcherName_2237_);
lean_dec_ref(v_toMatcherInfo_2236_);
v_a_2262_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2251_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2251_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_remaining_2243_);
lean_dec_ref(v_discrs_2241_);
lean_dec_ref(v_motive_2240_);
lean_dec_ref(v_params_2239_);
lean_dec_ref(v_matcherLevels_2238_);
lean_dec(v_matcherName_2237_);
lean_dec_ref(v_toMatcherInfo_2236_);
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
lean_dec(v_recFnName_2145_);
v_a_2270_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2247_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2247_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v___x_2278_; 
lean_dec(v_a_2234_);
v___x_2278_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2145_, v_fixedPrefixSize_2146_, v_F_2147_, v_e_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2278_;
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref_known(v_e_2148_, 2);
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
lean_dec(v_recFnName_2145_);
v_a_2279_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2233_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2233_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref_known(v_e_2148_, 2);
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
lean_dec(v_recFnName_2145_);
v_a_2287_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2229_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2229_);
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
default: 
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_F_2147_);
lean_dec(v_fixedPrefixSize_2146_);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___x_2295_);
v___x_2297_ = lean_array_push(v___x_2296_, v_recFnName_2145_);
lean_inc_ref(v_e_2148_);
v___x_2298_ = l_Lean_Elab_ensureNoRecFn(v___x_2297_, v_e_2148_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v___x_2298_, 0);
lean_dec(v_unused_2306_);
v___x_2300_ = v___x_2298_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v___x_2298_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_e_2148_);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_e_2148_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_e_2148_);
v_a_2307_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2298_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2298_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2315_, lean_object* v_fixedPrefixSize_2316_, lean_object* v_F_2317_, lean_object* v_e_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___x_2347_; 
lean_inc_ref(v_e_2318_);
lean_inc(v_recFnName_2315_);
v___x_2347_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2315_, v_e_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2435_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2435_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2435_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_unbox(v_a_2348_);
lean_dec(v_a_2348_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2354_; 
lean_dec_ref(v_F_2317_);
lean_dec(v_fixedPrefixSize_2316_);
lean_dec(v_recFnName_2315_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_e_2318_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_e_2318_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
uint8_t v___x_2356_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_del_object(v___x_2350_);
v___x_2356_ = 0;
v___x_2412_ = lean_st_ref_get(v_a_2320_);
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2412_, v_e_2318_);
lean_dec(v___x_2412_);
if (lean_obj_tag(v___x_2413_) == 1)
{
lean_object* v_val_2414_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2417_; 
v_val_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_val_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v_fst_2415_ = lean_ctor_get(v_val_2414_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_val_2414_, 1);
lean_inc(v_snd_2416_);
lean_dec(v_val_2414_);
v___x_2417_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2416_, v_a_2323_);
lean_dec(v_snd_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
uint8_t v___x_2422_; 
v___x_2422_ = lean_unbox(v_a_2418_);
lean_dec(v_a_2418_);
if (v___x_2422_ == 0)
{
lean_del_object(v___x_2420_);
lean_dec(v_fst_2415_);
v___y_2358_ = v_a_2319_;
v___y_2359_ = v_a_2320_;
v___y_2360_ = v_a_2321_;
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
v___y_2363_ = v_a_2324_;
v___y_2364_ = v_a_2325_;
v___y_2365_ = v_a_2326_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2424_; 
lean_dec_ref(v_e_2318_);
lean_dec_ref(v_F_2317_);
lean_dec(v_fixedPrefixSize_2316_);
lean_dec(v_recFnName_2315_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_fst_2415_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_fst_2415_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_fst_2415_);
lean_dec_ref(v_e_2318_);
lean_dec_ref(v_F_2317_);
lean_dec(v_fixedPrefixSize_2316_);
lean_dec(v_recFnName_2315_);
v_a_2427_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2417_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2417_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_dec(v___x_2413_);
v___y_2358_ = v_a_2319_;
v___y_2359_ = v_a_2320_;
v___y_2360_ = v_a_2321_;
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
v___y_2363_ = v_a_2324_;
v___y_2364_ = v_a_2325_;
v___y_2365_ = v_a_2326_;
goto v___jp_2357_;
}
v___jp_2357_:
{
lean_object* v___x_2366_; 
lean_inc_ref(v_e_2318_);
v___x_2366_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2315_, v_fixedPrefixSize_2316_, v_F_2317_, v_e_2318_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_n(v_a_2367_, 2);
lean_dec_ref_known(v___x_2366_, 1);
lean_inc_ref(v_e_2318_);
v___f_2368_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2368_, 0, v_e_2318_);
lean_closure_set(v___f_2368_, 1, v_a_2367_);
v___x_2369_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2403_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2403_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2403_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2374_ = lean_st_ref_take(v___y_2359_);
lean_inc(v_a_2367_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v_a_2367_);
lean_ctor_set(v___x_2375_, 1, v_a_2370_);
v___x_2376_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2374_, v_e_2318_, v___x_2375_);
v___x_2377_ = lean_st_ref_put(v___y_2359_, v___x_2376_);
v___x_2378_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2364_);
v___x_2379_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2380_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_2378_, v___x_2379_);
lean_dec_ref(v___x_2378_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2382_; 
lean_dec_ref(v___f_2368_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v_a_2367_);
v___x_2382_ = v___x_2372_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2367_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
else
{
lean_object* v___x_2384_; uint8_t v_transparency_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; 
lean_del_object(v___x_2372_);
v___x_2384_ = l_Lean_Meta_Context_config(v___y_2362_);
v_transparency_2385_ = lean_ctor_get_uint8(v___x_2384_, 9);
lean_dec_ref(v___x_2384_);
v___x_2386_ = 0;
v___x_2387_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v_keyedConfig_2388_; uint8_t v_trackZetaDelta_2389_; lean_object* v_zetaDeltaSet_2390_; lean_object* v_lctx_2391_; lean_object* v_localInstances_2392_; lean_object* v_defEqCtx_x3f_2393_; lean_object* v_synthPendingDepth_2394_; lean_object* v_customCanUnfoldPredicate_x3f_2395_; uint8_t v_univApprox_2396_; uint8_t v_inTypeClassResolution_2397_; uint8_t v_cacheInferType_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_keyedConfig_2388_ = lean_ctor_get(v___y_2362_, 0);
v_trackZetaDelta_2389_ = lean_ctor_get_uint8(v___y_2362_, sizeof(void*)*7);
v_zetaDeltaSet_2390_ = lean_ctor_get(v___y_2362_, 1);
v_lctx_2391_ = lean_ctor_get(v___y_2362_, 2);
v_localInstances_2392_ = lean_ctor_get(v___y_2362_, 3);
v_defEqCtx_x3f_2393_ = lean_ctor_get(v___y_2362_, 4);
v_synthPendingDepth_2394_ = lean_ctor_get(v___y_2362_, 5);
v_customCanUnfoldPredicate_x3f_2395_ = lean_ctor_get(v___y_2362_, 6);
v_univApprox_2396_ = lean_ctor_get_uint8(v___y_2362_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2397_ = lean_ctor_get_uint8(v___y_2362_, sizeof(void*)*7 + 2);
v_cacheInferType_2398_ = lean_ctor_get_uint8(v___y_2362_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2388_);
v___x_2399_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2386_, v_keyedConfig_2388_);
lean_inc(v_customCanUnfoldPredicate_x3f_2395_);
lean_inc(v_synthPendingDepth_2394_);
lean_inc(v_defEqCtx_x3f_2393_);
lean_inc_ref(v_localInstances_2392_);
lean_inc_ref(v_lctx_2391_);
lean_inc(v_zetaDeltaSet_2390_);
v___x_2400_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v_zetaDeltaSet_2390_);
lean_ctor_set(v___x_2400_, 2, v_lctx_2391_);
lean_ctor_set(v___x_2400_, 3, v_localInstances_2392_);
lean_ctor_set(v___x_2400_, 4, v_defEqCtx_x3f_2393_);
lean_ctor_set(v___x_2400_, 5, v_synthPendingDepth_2394_);
lean_ctor_set(v___x_2400_, 6, v_customCanUnfoldPredicate_x3f_2395_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*7, v_trackZetaDelta_2389_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*7 + 1, v_univApprox_2396_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2397_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*7 + 3, v_cacheInferType_2398_);
v___x_2401_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2368_, v___x_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___x_2400_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec_ref_known(v___x_2400_, 7);
v___y_2329_ = v_a_2367_;
v___y_2330_ = v___x_2401_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2368_, v___x_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
v___y_2329_ = v_a_2367_;
v___y_2330_ = v___x_2402_;
goto v___jp_2328_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v___f_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_e_2318_);
v_a_2404_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2369_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2369_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_dec_ref(v_e_2318_);
return v___x_2366_;
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v_e_2318_);
lean_dec_ref(v_F_2317_);
lean_dec(v_fixedPrefixSize_2316_);
lean_dec(v_recFnName_2315_);
v_a_2436_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2347_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2347_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
v___jp_2328_:
{
if (lean_obj_tag(v___y_2330_) == 0)
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v___y_2330_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___y_2330_, 0);
lean_dec(v_unused_2338_);
v___x_2332_ = v___y_2330_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v___y_2330_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___y_2329_);
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___y_2329_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v___y_2329_);
v_a_2339_ = lean_ctor_get(v___y_2330_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___y_2330_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___y_2330_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___y_2330_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2444_, lean_object* v_recFnName_2445_, lean_object* v_fixedPrefixSize_2446_, lean_object* v_F_2447_, lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_expr_instantiate1(v_body_2444_, v_x_2448_);
v___x_2459_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2445_, v_fixedPrefixSize_2446_, v_F_2447_, v___x_2458_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2460_, lean_object* v_fixedPrefixSize_2461_, lean_object* v_F_2462_, lean_object* v_e_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2460_, v_fixedPrefixSize_2461_, v_F_2462_, v_e_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec(v_a_2464_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2474_, lean_object* v_fixedPrefixSize_2475_, lean_object* v_F_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_bs_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
size_t v_sz_boxed_2489_; size_t v_i_boxed_2490_; lean_object* v_res_2491_; 
v_sz_boxed_2489_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2490_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2474_, v_fixedPrefixSize_2475_, v_F_2476_, v_sz_boxed_2489_, v_i_boxed_2490_, v_bs_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2492_, lean_object* v_fixedPrefixSize_2493_, lean_object* v_F_2494_, lean_object* v_x_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2492_, v_fixedPrefixSize_2493_, v_F_2494_, v_x_2495_, v_x_2496_, v_x_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2508_, lean_object* v_fixedPrefixSize_2509_, lean_object* v_e_2510_, lean_object* v_as_2511_, lean_object* v_bs_2512_, lean_object* v_i_2513_, lean_object* v_cs_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2508_, v_fixedPrefixSize_2509_, v_e_2510_, v_as_2511_, v_bs_2512_, v_i_2513_, v_cs_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v_bs_2512_);
lean_dec_ref(v_as_2511_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2525_, lean_object* v_fixedPrefixSize_2526_, lean_object* v_F_2527_, lean_object* v_e_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2525_, v_fixedPrefixSize_2526_, v_F_2527_, v_e_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec(v_a_2529_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2539_, lean_object* v_fixedPrefixSize_2540_, lean_object* v_F_2541_, lean_object* v_e_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2539_, v_fixedPrefixSize_2540_, v_F_2541_, v_e_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec(v_a_2543_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2553_, lean_object* v_fixedPrefixSize_2554_, lean_object* v_F_2555_, lean_object* v_e_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2553_, v_fixedPrefixSize_2554_, v_F_2555_, v_e_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec(v_a_2557_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2567_, lean_object* v_k_2568_, uint8_t v_allowLevelAssignments_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2568_, v_allowLevelAssignments_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_k_2581_, lean_object* v_allowLevelAssignments_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2592_; lean_object* v_res_2593_; 
v_allowLevelAssignments_boxed_2592_ = lean_unbox(v_allowLevelAssignments_2582_);
v_res_2593_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2580_, v_k_2581_, v_allowLevelAssignments_boxed_2592_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2594_, lean_object* v_name_2595_, uint8_t v_bi_2596_, lean_object* v_type_2597_, lean_object* v_k_2598_, uint8_t v_kind_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2595_, v_bi_2596_, v_type_2597_, v_k_2598_, v_kind_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_name_2611_, lean_object* v_bi_2612_, lean_object* v_type_2613_, lean_object* v_k_2614_, lean_object* v_kind_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v_bi_boxed_2625_; uint8_t v_kind_boxed_2626_; lean_object* v_res_2627_; 
v_bi_boxed_2625_ = lean_unbox(v_bi_2612_);
v_kind_boxed_2626_ = lean_unbox(v_kind_2615_);
v_res_2627_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2610_, v_name_2611_, v_bi_boxed_2625_, v_type_2613_, v_k_2614_, v_kind_boxed_2626_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec(v___y_2616_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2628_, lean_object* v_e_2629_, lean_object* v_maxFVars_2630_, lean_object* v_k_2631_, uint8_t v_cleanupAnnotations_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2629_, v_maxFVars_2630_, v_k_2631_, v_cleanupAnnotations_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_e_2644_, lean_object* v_maxFVars_2645_, lean_object* v_k_2646_, lean_object* v_cleanupAnnotations_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2657_; lean_object* v_res_2658_; 
v_cleanupAnnotations_boxed_2657_ = lean_unbox(v_cleanupAnnotations_2647_);
v_res_2658_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2643_, v_e_2644_, v_maxFVars_2645_, v_k_2646_, v_cleanupAnnotations_boxed_2657_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec(v___y_2648_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2659_, lean_object* v_R_2660_, lean_object* v_a_2661_, lean_object* v_b_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2661_, v_b_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2664_, lean_object* v_msg_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2664_, v_msg_2665_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2676_, lean_object* v_msg_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2676_, v_msg_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v___y_2678_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2688_, lean_object* v_m_2689_, lean_object* v_a_2690_, lean_object* v_b_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2689_, v_a_2690_, v_b_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2694_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_msg_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2705_, v_msg_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2717_, lean_object* v_m_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2718_, v_a_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_m_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2721_, v_m_2722_, v_a_2723_);
lean_dec_ref(v_a_2723_);
lean_dec_ref(v_m_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2725_, lean_object* v_name_2726_, lean_object* v_type_2727_, lean_object* v_val_2728_, lean_object* v_k_2729_, uint8_t v_nondep_2730_, uint8_t v_kind_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2726_, v_type_2727_, v_val_2728_, v_k_2729_, v_nondep_2730_, v_kind_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_name_2743_, lean_object* v_type_2744_, lean_object* v_val_2745_, lean_object* v_k_2746_, lean_object* v_nondep_2747_, lean_object* v_kind_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
uint8_t v_nondep_boxed_2758_; uint8_t v_kind_boxed_2759_; lean_object* v_res_2760_; 
v_nondep_boxed_2758_ = lean_unbox(v_nondep_2747_);
v_kind_boxed_2759_ = lean_unbox(v_kind_2748_);
v_res_2760_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2742_, v_name_2743_, v_type_2744_, v_val_2745_, v_k_2746_, v_nondep_boxed_2758_, v_kind_boxed_2759_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2761_, v___y_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec(v___y_2773_);
return v_res_2782_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2783_, lean_object* v_a_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2787_, lean_object* v_a_2788_, lean_object* v_x_2789_){
_start:
{
uint8_t v_res_2790_; lean_object* v_r_2791_; 
v_res_2790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2787_, v_a_2788_, v_x_2789_);
lean_dec(v_x_2789_);
lean_dec_ref(v_a_2788_);
v_r_2791_ = lean_box(v_res_2790_);
return v_r_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2792_, lean_object* v_data_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2795_, lean_object* v_a_2796_, lean_object* v_b_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2796_, v_b_2797_, v_x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2800_, lean_object* v_a_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2801_, v_x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_a_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2804_, v_a_2805_, v_x_2806_);
lean_dec(v_x_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2808_, lean_object* v_i_2809_, lean_object* v_source_2810_, lean_object* v_target_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2809_, v_source_2810_, v_target_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2813_, lean_object* v_constName_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_constName_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2825_, v_constName_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec(v___y_2827_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2838_, v_x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2841_, lean_object* v_ref_2842_, lean_object* v_constName_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2842_, v_constName_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2854_, lean_object* v_ref_2855_, lean_object* v_constName_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2854_, v_ref_2855_, v_constName_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v_ref_2855_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2867_, lean_object* v_ref_2868_, lean_object* v_msg_2869_, lean_object* v_declHint_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2868_, v_msg_2869_, v_declHint_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2881_, lean_object* v_ref_2882_, lean_object* v_msg_2883_, lean_object* v_declHint_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2881_, v_ref_2882_, v_msg_2883_, v_declHint_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec(v_ref_2882_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2895_, lean_object* v_declHint_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2895_, v_declHint_2896_, v___y_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2907_, lean_object* v_declHint_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2907_, v_declHint_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2919_, lean_object* v_ref_2920_, lean_object* v_msg_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2920_, v_msg_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_ref_2933_, lean_object* v_msg_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2932_, v_ref_2933_, v_msg_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v_ref_2933_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2945_, lean_object* v_msg_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_ref_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2999_; 
v_ref_2952_ = lean_ctor_get(v___y_2949_, 2);
v___x_2953_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2999_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2999_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v_traceState_2959_; lean_object* v_env_2960_; lean_object* v_nextMacroScope_2961_; lean_object* v_ngen_2962_; lean_object* v_auxDeclNGen_2963_; lean_object* v_cache_2964_; lean_object* v_recordedDeps_2965_; lean_object* v_messages_2966_; lean_object* v_infoState_2967_; lean_object* v_snapshotTasks_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2998_; 
v___x_2958_ = lean_st_ref_take(v___y_2950_);
v_traceState_2959_ = lean_ctor_get(v___x_2958_, 4);
v_env_2960_ = lean_ctor_get(v___x_2958_, 0);
v_nextMacroScope_2961_ = lean_ctor_get(v___x_2958_, 1);
v_ngen_2962_ = lean_ctor_get(v___x_2958_, 2);
v_auxDeclNGen_2963_ = lean_ctor_get(v___x_2958_, 3);
v_cache_2964_ = lean_ctor_get(v___x_2958_, 5);
v_recordedDeps_2965_ = lean_ctor_get(v___x_2958_, 6);
v_messages_2966_ = lean_ctor_get(v___x_2958_, 7);
v_infoState_2967_ = lean_ctor_get(v___x_2958_, 8);
v_snapshotTasks_2968_ = lean_ctor_get(v___x_2958_, 9);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2970_ = v___x_2958_;
v_isShared_2971_ = v_isSharedCheck_2998_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_snapshotTasks_2968_);
lean_inc(v_infoState_2967_);
lean_inc(v_messages_2966_);
lean_inc(v_recordedDeps_2965_);
lean_inc(v_cache_2964_);
lean_inc(v_traceState_2959_);
lean_inc(v_auxDeclNGen_2963_);
lean_inc(v_ngen_2962_);
lean_inc(v_nextMacroScope_2961_);
lean_inc(v_env_2960_);
lean_dec(v___x_2958_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2998_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint64_t v_tid_2972_; lean_object* v_traces_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2997_; 
v_tid_2972_ = lean_ctor_get_uint64(v_traceState_2959_, sizeof(void*)*1);
v_traces_2973_ = lean_ctor_get(v_traceState_2959_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_traceState_2959_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2975_ = v_traceState_2959_;
v_isShared_2976_ = v_isSharedCheck_2997_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_traces_2973_);
lean_dec(v_traceState_2959_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2997_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; double v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2980_ = 0;
v___x_2981_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2982_, 0, v_cls_2945_);
lean_ctor_set(v___x_2982_, 1, v___x_2978_);
lean_ctor_set(v___x_2982_, 2, v___x_2981_);
lean_ctor_set_float(v___x_2982_, sizeof(void*)*3, v___x_2979_);
lean_ctor_set_float(v___x_2982_, sizeof(void*)*3 + 8, v___x_2979_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*3 + 16, v___x_2980_);
v___x_2983_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2984_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v_a_2954_);
lean_ctor_set(v___x_2984_, 2, v___x_2983_);
lean_inc(v_ref_2952_);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_ref_2952_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Lean_PersistentArray_push___redArg(v_traces_2973_, v___x_2985_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2986_);
v___x_2988_ = v___x_2975_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2986_);
lean_ctor_set_uint64(v_reuseFailAlloc_2996_, sizeof(void*)*1, v_tid_2972_);
v___x_2988_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2990_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 4, v___x_2988_);
v___x_2990_ = v___x_2970_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_env_2960_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_nextMacroScope_2961_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_ngen_2962_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v_auxDeclNGen_2963_);
lean_ctor_set(v_reuseFailAlloc_2995_, 4, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2995_, 5, v_cache_2964_);
lean_ctor_set(v_reuseFailAlloc_2995_, 6, v_recordedDeps_2965_);
lean_ctor_set(v_reuseFailAlloc_2995_, 7, v_messages_2966_);
lean_ctor_set(v_reuseFailAlloc_2995_, 8, v_infoState_2967_);
lean_ctor_set(v_reuseFailAlloc_2995_, 9, v_snapshotTasks_2968_);
v___x_2990_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = lean_st_ref_put(v___y_2950_, v___x_2990_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2977_);
v___x_2993_ = v___x_2956_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2977_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3000_, lean_object* v_msg_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3000_, v_msg_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3007_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_unsigned_to_nat(16u);
v___x_3010_ = lean_mk_array(v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3019_ = l_Lean_stringToMessageData(v___x_3018_);
return v___x_3019_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3022_ = l_Lean_stringToMessageData(v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3023_, lean_object* v_fixedPrefixSize_3024_, lean_object* v_F_3025_, lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v_toCold_3055_; lean_object* v_options_3056_; uint8_t v_hasTrace_3057_; 
v_toCold_3055_ = lean_ctor_get(v_a_3031_, 0);
v_options_3056_ = lean_ctor_get(v_toCold_3055_, 2);
v_hasTrace_3057_ = lean_ctor_get_uint8(v_options_3056_, sizeof(void*)*1);
if (v_hasTrace_3057_ == 0)
{
v___y_3035_ = v_a_3027_;
v___y_3036_ = v_a_3028_;
v___y_3037_ = v_a_3029_;
v___y_3038_ = v_a_3030_;
v___y_3039_ = v_a_3031_;
v___y_3040_ = v_a_3032_;
goto v___jp_3034_;
}
else
{
lean_object* v_inheritedTraceOptions_3058_; lean_object* v_cls_3059_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v_options_3066_; lean_object* v_inheritedTraceOptions_3067_; lean_object* v___y_3068_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_inheritedTraceOptions_3058_ = lean_ctor_get(v_toCold_3055_, 11);
v_cls_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3089_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3090_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3058_, v_options_3056_, v___x_3089_);
if (v___x_3090_ == 0)
{
v___y_3061_ = v_a_3027_;
v___y_3062_ = v_a_3028_;
v___y_3063_ = v_a_3029_;
v___y_3064_ = v_a_3030_;
v___y_3065_ = v_a_3031_;
v_options_3066_ = v_options_3056_;
v_inheritedTraceOptions_3067_ = v_inheritedTraceOptions_3058_;
v___y_3068_ = v_a_3032_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3091_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3026_);
v___x_3092_ = l_Lean_indentExpr(v_e_3026_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3059_, v___x_3093_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_dec_ref_known(v___x_3094_, 1);
v___y_3061_ = v_a_3027_;
v___y_3062_ = v_a_3028_;
v___y_3063_ = v_a_3029_;
v___y_3064_ = v_a_3030_;
v___y_3065_ = v_a_3031_;
v_options_3066_ = v_options_3056_;
v_inheritedTraceOptions_3067_ = v_inheritedTraceOptions_3058_;
v___y_3068_ = v_a_3032_;
goto v___jp_3060_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_e_3026_);
lean_dec_ref(v_F_3025_);
lean_dec(v_fixedPrefixSize_3024_);
lean_dec(v_recFnName_3023_);
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
v___jp_3060_:
{
lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3069_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3067_, v_options_3066_, v___x_3069_);
if (v___x_3070_ == 0)
{
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3068_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3071_; 
lean_inc(v___y_3068_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc_ref(v_F_3025_);
v___x_3071_ = lean_infer_type(v_F_3025_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3068_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3025_);
v___x_3074_ = l_Lean_MessageData_ofExpr(v_F_3025_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_indentExpr(v_a_3072_);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3059_, v___x_3079_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3068_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref_known(v___x_3080_, 1);
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3068_;
goto v___jp_3034_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v_e_3026_);
lean_dec_ref(v_F_3025_);
lean_dec(v_fixedPrefixSize_3024_);
lean_dec(v_recFnName_3023_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_dec_ref(v_e_3026_);
lean_dec_ref(v_F_3025_);
lean_dec(v_fixedPrefixSize_3024_);
lean_dec(v_recFnName_3023_);
return v___x_3071_;
}
}
}
}
v___jp_3034_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3042_ = lean_st_mk_ref(v___x_3041_);
v___x_3043_ = lean_st_mk_ref(v___x_3041_);
v___x_3044_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3023_, v_fixedPrefixSize_3024_, v_F_3025_, v_e_3026_, v___x_3043_, v___x_3042_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3054_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3054_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3054_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_get(v___x_3043_);
lean_dec(v___x_3043_);
lean_dec(v___x_3049_);
v___x_3050_ = lean_st_ref_get(v___x_3042_);
lean_dec(v___x_3042_);
lean_dec(v___x_3050_);
if (v_isShared_3048_ == 0)
{
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3045_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_dec(v___x_3043_);
lean_dec(v___x_3042_);
return v___x_3044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3103_, lean_object* v_fixedPrefixSize_3104_, lean_object* v_F_3105_, lean_object* v_e_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3103_, v_fixedPrefixSize_3104_, v_F_3105_, v_e_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3115_, v_msg_3116_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3125_, lean_object* v_msg_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3125_, v_msg_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v_b_3138_, lean_object* v_c_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
v___x_3145_ = lean_apply_9(v_k_3135_, v_b_3138_, v_c_3139_, v___y_3136_, v___y_3137_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v_b_3149_, lean_object* v_c_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3146_, v___y_3147_, v___y_3148_, v_b_3149_, v_c_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3157_, lean_object* v_maxFVars_3158_, lean_object* v_k_3159_, uint8_t v_cleanupAnnotations_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___f_3168_; uint8_t v___x_3169_; uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3168_, 0, v_k_3159_);
lean_closure_set(v___f_3168_, 1, v___y_3161_);
lean_closure_set(v___f_3168_, 2, v___y_3162_);
v___x_3169_ = 1;
v___x_3170_ = 0;
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_maxFVars_3158_);
v___x_3172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3157_, v___x_3169_, v___x_3170_, v___x_3169_, v___x_3170_, v___x_3171_, v___f_3168_, v_cleanupAnnotations_3160_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec_ref_known(v___x_3171_, 1);
if (lean_obj_tag(v___x_3172_) == 0)
{
return v___x_3172_;
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3181_, lean_object* v_maxFVars_3182_, lean_object* v_k_3183_, lean_object* v_cleanupAnnotations_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3192_; lean_object* v_res_3193_; 
v_cleanupAnnotations_boxed_3192_ = lean_unbox(v_cleanupAnnotations_3184_);
v_res_3193_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3181_, v_maxFVars_3182_, v_k_3183_, v_cleanupAnnotations_boxed_3192_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3194_, lean_object* v_e_3195_, lean_object* v_maxFVars_3196_, lean_object* v_k_3197_, uint8_t v_cleanupAnnotations_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3195_, v_maxFVars_3196_, v_k_3197_, v_cleanupAnnotations_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3207_, lean_object* v_e_3208_, lean_object* v_maxFVars_3209_, lean_object* v_k_3210_, lean_object* v_cleanupAnnotations_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3219_; lean_object* v_res_3220_; 
v_cleanupAnnotations_boxed_3219_ = lean_unbox(v_cleanupAnnotations_3211_);
v_res_3220_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3207_, v_e_3208_, v_maxFVars_3209_, v_k_3210_, v_cleanupAnnotations_boxed_3219_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3221_, lean_object* v_k_3222_, uint8_t v_cleanupAnnotations_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___f_3231_; uint8_t v___x_3232_; uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
v___f_3231_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3231_, 0, v_k_3222_);
lean_closure_set(v___f_3231_, 1, v___y_3224_);
lean_closure_set(v___f_3231_, 2, v___y_3225_);
v___x_3232_ = 1;
v___x_3233_ = 0;
v___x_3234_ = lean_box(0);
v___x_3235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3221_, v___x_3232_, v___x_3233_, v___x_3232_, v___x_3233_, v___x_3234_, v___f_3231_, v_cleanupAnnotations_3223_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3235_) == 0)
{
return v___x_3235_;
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3244_, lean_object* v_k_3245_, lean_object* v_cleanupAnnotations_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3254_; lean_object* v_res_3255_; 
v_cleanupAnnotations_boxed_3254_ = lean_unbox(v_cleanupAnnotations_3246_);
v_res_3255_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3244_, v_k_3245_, v_cleanupAnnotations_boxed_3254_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3256_, lean_object* v_e_3257_, lean_object* v_k_3258_, uint8_t v_cleanupAnnotations_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3257_, v_k_3258_, v_cleanupAnnotations_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_e_3269_, lean_object* v_k_3270_, lean_object* v_cleanupAnnotations_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3279_; lean_object* v_res_3280_; 
v_cleanupAnnotations_boxed_3279_ = lean_unbox(v_cleanupAnnotations_3271_);
v_res_3280_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3268_, v_e_3269_, v_k_3270_, v_cleanupAnnotations_boxed_3279_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3281_, lean_object* v___x_3282_, lean_object* v___x_3283_, lean_object* v_x_3284_, uint8_t v___x_3285_, lean_object* v_xs_3286_, lean_object* v_type_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3295_ = l_Lean_LocalDecl_type(v_a_3281_);
v___x_3296_ = lean_array_get_borrowed(v___x_3282_, v_xs_3286_, v___x_3283_);
v___x_3297_ = l_Lean_Expr_replaceFVar(v___x_3295_, v_x_3284_, v___x_3296_);
lean_dec_ref(v___x_3295_);
v___x_3298_ = l_Lean_mkArrow(v___x_3297_, v_type_3287_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; uint8_t v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_n(v_a_3299_, 2);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = 0;
v___x_3301_ = 1;
v___x_3302_ = l_Lean_Meta_mkLambdaFVars(v_xs_3286_, v_a_3299_, v___x_3300_, v___x_3285_, v___x_3300_, v___x_3285_, v___x_3301_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = l_Lean_Meta_getLevel(v_a_3299_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3313_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3313_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3313_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_a_3303_);
lean_ctor_set(v___x_3309_, 1, v_a_3305_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3309_);
v___x_3311_ = v___x_3307_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_a_3303_);
v_a_3314_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3304_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3304_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v_a_3299_);
v_a_3322_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3302_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3302_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3298_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3298_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3338_, lean_object* v___x_3339_, lean_object* v___x_3340_, lean_object* v_x_3341_, lean_object* v___x_3342_, lean_object* v_xs_3343_, lean_object* v_type_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v___x_6245__boxed_3352_; lean_object* v_res_3353_; 
v___x_6245__boxed_3352_ = lean_unbox(v___x_3342_);
v_res_3353_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3338_, v___x_3339_, v___x_3340_, v_x_3341_, v___x_6245__boxed_3352_, v_xs_3343_, v_type_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v_xs_3343_);
lean_dec(v___x_3340_);
lean_dec_ref(v___x_3339_);
lean_dec_ref(v_a_3338_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; 
lean_inc(v___y_3361_);
lean_inc_ref(v___y_3360_);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
v___x_3363_ = lean_apply_8(v_k_3354_, v_b_3357_, v___y_3355_, v___y_3356_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, lean_box(0));
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v_b_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3364_, v___y_3365_, v___y_3366_, v_b_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3374_, uint8_t v_bi_3375_, lean_object* v_type_3376_, lean_object* v_k_3377_, uint8_t v_kind_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___f_3386_; lean_object* v___x_3387_; 
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3386_, 0, v_k_3377_);
lean_closure_set(v___f_3386_, 1, v___y_3379_);
lean_closure_set(v___f_3386_, 2, v___y_3380_);
v___x_3387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3374_, v_bi_3375_, v_type_3376_, v___f_3386_, v_kind_3378_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3387_) == 0)
{
return v___x_3387_;
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3396_, lean_object* v_bi_3397_, lean_object* v_type_3398_, lean_object* v_k_3399_, lean_object* v_kind_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v_bi_boxed_3408_; uint8_t v_kind_boxed_3409_; lean_object* v_res_3410_; 
v_bi_boxed_3408_ = lean_unbox(v_bi_3397_);
v_kind_boxed_3409_ = lean_unbox(v_kind_3400_);
v_res_3410_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3396_, v_bi_boxed_3408_, v_type_3398_, v_k_3399_, v_kind_boxed_3409_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3411_, lean_object* v_type_3412_, lean_object* v_k_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
uint8_t v___x_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = 0;
v___x_3422_ = 0;
v___x_3423_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3411_, v___x_3421_, v_type_3412_, v_k_3413_, v___x_3422_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3424_, lean_object* v_type_3425_, lean_object* v_k_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3424_, v_type_3425_, v_k_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3448_, lean_object* v_F_3449_, lean_object* v_val_3450_, lean_object* v_k_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v___x_3459_; uint8_t v___y_3461_; uint8_t v___x_3575_; 
v___x_3459_ = l_Lean_instInhabitedExpr;
v___x_3575_ = l_Lean_Expr_isFVar(v_x_3448_);
if (v___x_3575_ == 0)
{
v___y_3461_ = v___x_3575_;
goto v___jp_3460_;
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3576_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3577_ = lean_unsigned_to_nat(6u);
v___x_3578_ = l_Lean_Expr_isAppOfArity(v_val_3450_, v___x_3576_, v___x_3577_);
v___y_3461_ = v___x_3578_;
goto v___jp_3460_;
}
v___jp_3460_:
{
if (v___y_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
lean_inc(v_a_3455_);
lean_inc_ref(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc_ref(v_a_3452_);
v___x_3462_ = lean_apply_10(v_k_3451_, v_x_3448_, v_F_3449_, v_val_3450_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, lean_box(0));
return v___x_3462_;
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3463_ = lean_unsigned_to_nat(3u);
v___x_3464_ = l_Lean_Expr_getAppNumArgs(v_val_3450_);
v___x_3465_ = lean_nat_sub(v___x_3464_, v___x_3463_);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_sub(v___x_3465_, v___x_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = l_Lean_Expr_getRevArg_x21(v_val_3450_, v___x_3467_);
v___x_3469_ = lean_expr_eqv(v___x_3468_, v_x_3448_);
lean_dec_ref(v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_dec(v___x_3464_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
lean_inc(v_a_3455_);
lean_inc_ref(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc_ref(v_a_3452_);
v___x_3470_ = lean_apply_10(v_k_3451_, v_x_3448_, v_F_3449_, v_val_3450_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, lean_box(0));
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3471_ = lean_unsigned_to_nat(4u);
v___x_3472_ = lean_nat_sub(v___x_3464_, v___x_3471_);
v___x_3473_ = lean_nat_sub(v___x_3472_, v___x_3466_);
lean_dec(v___x_3472_);
v___x_3474_ = l_Lean_Expr_getRevArg_x21(v_val_3450_, v___x_3473_);
v___x_3475_ = l_Lean_Expr_isLambda(v___x_3474_);
lean_dec_ref(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec(v___x_3464_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
lean_inc(v_a_3455_);
lean_inc_ref(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc_ref(v_a_3452_);
v___x_3476_ = lean_apply_10(v_k_3451_, v_x_3448_, v_F_3449_, v_val_3450_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, lean_box(0));
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3477_ = lean_unsigned_to_nat(5u);
v___x_3478_ = lean_nat_sub(v___x_3464_, v___x_3477_);
v___x_3479_ = lean_nat_sub(v___x_3478_, v___x_3466_);
lean_dec(v___x_3478_);
v___x_3480_ = l_Lean_Expr_getRevArg_x21(v_val_3450_, v___x_3479_);
v___x_3481_ = l_Lean_Expr_isLambda(v___x_3480_);
lean_dec_ref(v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec(v___x_3464_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
lean_inc(v_a_3455_);
lean_inc_ref(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc_ref(v_a_3452_);
v___x_3482_ = lean_apply_10(v_k_3451_, v_x_3448_, v_F_3449_, v_val_3450_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, lean_box(0));
return v___x_3482_;
}
else
{
lean_object* v_dummy_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v_args_3486_; lean_object* v___x_3487_; lean_object* v_00_u03b1_3488_; lean_object* v_00_u03b2_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_dummy_3483_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3464_);
v___x_3484_ = lean_mk_array(v___x_3464_, v_dummy_3483_);
v___x_3485_ = lean_nat_sub(v___x_3464_, v___x_3466_);
lean_dec(v___x_3464_);
v_args_3486_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3450_, v___x_3484_, v___x_3485_);
v___x_3487_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3488_ = lean_array_get(v___x_3459_, v_args_3486_, v___x_3487_);
v_00_u03b2_3489_ = lean_array_get(v___x_3459_, v_args_3486_, v___x_3466_);
v___x_3490_ = l_Lean_Expr_fvarId_x21(v_F_3449_);
v___x_3491_ = l_Lean_FVarId_getDecl___redArg(v___x_3490_, v_a_3454_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc_n(v_a_3492_, 2);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = lean_box(v___x_3475_);
lean_inc_ref(v_x_3448_);
v___f_3494_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3494_, 0, v_a_3492_);
lean_closure_set(v___f_3494_, 1, v___x_3459_);
lean_closure_set(v___f_3494_, 2, v___x_3487_);
lean_closure_set(v___f_3494_, 3, v_x_3448_);
lean_closure_set(v___f_3494_, 4, v___x_3493_);
v___x_3495_ = lean_unsigned_to_nat(2u);
v___x_3496_ = lean_array_get(v___x_3459_, v_args_3486_, v___x_3495_);
v___x_3497_ = 0;
v___x_3498_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3496_, v___f_3494_, v___x_3497_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3558_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v_fst_3500_ = lean_ctor_get(v_a_3499_, 0);
v_snd_3501_ = lean_ctor_get(v_a_3499_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_a_3499_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3503_ = v_a_3499_;
v_isShared_3504_ = v_isSharedCheck_3558_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_inc(v_fst_3500_);
lean_dec(v_a_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3558_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3506_ = lean_array_get(v___x_3459_, v_args_3486_, v___x_3471_);
lean_inc_ref(v_x_3448_);
lean_inc(v_a_3492_);
lean_inc(v_00_u03b2_3489_);
lean_inc(v_00_u03b1_3488_);
lean_inc_ref(v_k_3451_);
v___x_3507_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3459_, v___x_3487_, v_k_3451_, v___x_3495_, v___x_3497_, v___x_3475_, v_00_u03b1_3488_, v_00_u03b2_3489_, v___x_3463_, v_a_3492_, v_x_3448_, v___x_3466_, v___x_3505_, v___x_3506_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3510_ = lean_array_get(v___x_3459_, v_args_3486_, v___x_3477_);
lean_dec_ref(v_args_3486_);
lean_inc_ref(v_x_3448_);
lean_inc(v_00_u03b2_3489_);
lean_inc(v_00_u03b1_3488_);
v___x_3511_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3459_, v___x_3487_, v_k_3451_, v___x_3495_, v___x_3497_, v___x_3475_, v_00_u03b1_3488_, v_00_u03b2_3489_, v___x_3463_, v_a_3492_, v_x_3448_, v___x_3466_, v___x_3509_, v___x_3510_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
lean_inc(v_00_u03b1_3488_);
v___x_3513_ = l_Lean_Meta_getLevel(v_00_u03b1_3488_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
lean_inc(v_00_u03b2_3489_);
v___x_3515_ = l_Lean_Meta_getLevel(v_00_u03b2_3489_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3541_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3541_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3541_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3521_ = lean_box(0);
if (v_isShared_3504_ == 0)
{
lean_ctor_set_tag(v___x_3503_, 1);
lean_ctor_set(v___x_3503_, 1, v___x_3521_);
lean_ctor_set(v___x_3503_, 0, v_a_3516_);
v___x_3523_ = v___x_3503_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3516_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3524_, 0, v_a_3514_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_snd_3501_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_mkConst(v___x_3520_, v___x_3525_);
v___x_3527_ = lean_unsigned_to_nat(7u);
v___x_3528_ = lean_mk_empty_array_with_capacity(v___x_3527_);
v___x_3529_ = lean_array_push(v___x_3528_, v_00_u03b1_3488_);
v___x_3530_ = lean_array_push(v___x_3529_, v_00_u03b2_3489_);
v___x_3531_ = lean_array_push(v___x_3530_, v_fst_3500_);
v___x_3532_ = lean_array_push(v___x_3531_, v_x_3448_);
v___x_3533_ = lean_array_push(v___x_3532_, v_a_3508_);
v___x_3534_ = lean_array_push(v___x_3533_, v_a_3512_);
v___x_3535_ = lean_array_push(v___x_3534_, v_F_3449_);
v___x_3536_ = l_Lean_mkAppN(v___x_3526_, v___x_3535_);
lean_dec_ref(v___x_3535_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3536_);
v___x_3538_ = v___x_3518_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec(v_a_3508_);
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
v_a_3542_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3515_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3515_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_a_3512_);
lean_dec(v_a_3508_);
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
v_a_3550_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3513_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3513_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_dec(v_a_3508_);
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
return v___x_3511_;
}
}
else
{
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec(v_fst_3500_);
lean_dec(v_a_3492_);
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_args_3486_);
lean_dec_ref(v_k_3451_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
return v___x_3507_;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3492_);
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_args_3486_);
lean_dec_ref(v_k_3451_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
v_a_3559_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3498_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3498_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_00_u03b2_3489_);
lean_dec(v_00_u03b1_3488_);
lean_dec_ref(v_args_3486_);
lean_dec_ref(v_k_3451_);
lean_dec_ref(v_F_3449_);
lean_dec_ref(v_x_3448_);
v_a_3567_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3491_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3491_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3579_, lean_object* v_body_3580_, lean_object* v_k_3581_, lean_object* v___x_3582_, uint8_t v___x_3583_, uint8_t v___x_3584_, lean_object* v_FNew_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; 
lean_inc_ref(v_FNew_3585_);
lean_inc_ref(v___x_3579_);
v___x_3593_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3579_, v_FNew_3585_, v_body_3580_, v_k_3581_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = lean_mk_empty_array_with_capacity(v___x_3582_);
v___x_3596_ = lean_array_push(v___x_3595_, v___x_3579_);
v___x_3597_ = lean_array_push(v___x_3596_, v_FNew_3585_);
v___x_3598_ = 1;
v___x_3599_ = l_Lean_Meta_mkLambdaFVars(v___x_3597_, v_a_3594_, v___x_3583_, v___x_3584_, v___x_3583_, v___x_3584_, v___x_3598_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec_ref(v___x_3597_);
return v___x_3599_;
}
else
{
lean_dec_ref(v_FNew_3585_);
lean_dec_ref(v___x_3579_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3600_, lean_object* v_body_3601_, lean_object* v_k_3602_, lean_object* v___x_3603_, lean_object* v___x_3604_, lean_object* v___x_3605_, lean_object* v_FNew_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
uint8_t v___x_6491__boxed_3614_; uint8_t v___x_6492__boxed_3615_; lean_object* v_res_3616_; 
v___x_6491__boxed_3614_ = lean_unbox(v___x_3604_);
v___x_6492__boxed_3615_ = lean_unbox(v___x_3605_);
v_res_3616_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3600_, v_body_3601_, v_k_3602_, v___x_3603_, v___x_6491__boxed_3614_, v___x_6492__boxed_3615_, v_FNew_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___x_3603_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3617_, lean_object* v___x_3618_, lean_object* v_k_3619_, lean_object* v___x_3620_, uint8_t v___x_3621_, uint8_t v___x_3622_, lean_object* v_00_u03b1_3623_, lean_object* v_00_u03b2_3624_, lean_object* v___x_3625_, lean_object* v_ctorName_3626_, lean_object* v_a_3627_, lean_object* v_x_3628_, lean_object* v_xs_3629_, lean_object* v_body_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3638_ = lean_array_get_borrowed(v___x_3617_, v_xs_3629_, v___x_3618_);
v___x_3639_ = lean_box(v___x_3621_);
v___x_3640_ = lean_box(v___x_3622_);
lean_inc_n(v___x_3638_, 2);
v___f_3641_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3641_, 0, v___x_3638_);
lean_closure_set(v___f_3641_, 1, v_body_3630_);
lean_closure_set(v___f_3641_, 2, v_k_3619_);
lean_closure_set(v___f_3641_, 3, v___x_3620_);
lean_closure_set(v___f_3641_, 4, v___x_3639_);
lean_closure_set(v___f_3641_, 5, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_00_u03b1_3623_);
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v_00_u03b2_3624_);
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3638_);
v___x_3645_ = lean_mk_empty_array_with_capacity(v___x_3625_);
v___x_3646_ = lean_array_push(v___x_3645_, v___x_3642_);
v___x_3647_ = lean_array_push(v___x_3646_, v___x_3643_);
v___x_3648_ = lean_array_push(v___x_3647_, v___x_3644_);
v___x_3649_ = l_Lean_Meta_mkAppOptM(v_ctorName_3626_, v___x_3648_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = l_Lean_LocalDecl_type(v_a_3627_);
v___x_3652_ = l_Lean_Expr_replaceFVar(v___x_3651_, v_x_3628_, v_a_3650_);
lean_dec(v_a_3650_);
lean_dec_ref(v___x_3651_);
v___x_3653_ = l_Lean_LocalDecl_userName(v_a_3627_);
v___x_3654_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3653_, v___x_3652_, v___f_3641_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
return v___x_3654_;
}
else
{
lean_dec_ref(v___f_3641_);
lean_dec_ref(v_x_3628_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3655_ = _args[0];
lean_object* v___x_3656_ = _args[1];
lean_object* v_k_3657_ = _args[2];
lean_object* v___x_3658_ = _args[3];
lean_object* v___x_3659_ = _args[4];
lean_object* v___x_3660_ = _args[5];
lean_object* v_00_u03b1_3661_ = _args[6];
lean_object* v_00_u03b2_3662_ = _args[7];
lean_object* v___x_3663_ = _args[8];
lean_object* v_ctorName_3664_ = _args[9];
lean_object* v_a_3665_ = _args[10];
lean_object* v_x_3666_ = _args[11];
lean_object* v_xs_3667_ = _args[12];
lean_object* v_body_3668_ = _args[13];
lean_object* v___y_3669_ = _args[14];
lean_object* v___y_3670_ = _args[15];
lean_object* v___y_3671_ = _args[16];
lean_object* v___y_3672_ = _args[17];
lean_object* v___y_3673_ = _args[18];
lean_object* v___y_3674_ = _args[19];
lean_object* v___y_3675_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3676_; uint8_t v___x_6512__boxed_3677_; lean_object* v_res_3678_; 
v___x_6511__boxed_3676_ = lean_unbox(v___x_3659_);
v___x_6512__boxed_3677_ = lean_unbox(v___x_3660_);
v_res_3678_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3655_, v___x_3656_, v_k_3657_, v___x_3658_, v___x_6511__boxed_3676_, v___x_6512__boxed_3677_, v_00_u03b1_3661_, v_00_u03b2_3662_, v___x_3663_, v_ctorName_3664_, v_a_3665_, v_x_3666_, v_xs_3667_, v_body_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_xs_3667_);
lean_dec_ref(v_a_3665_);
lean_dec(v___x_3663_);
lean_dec(v___x_3656_);
lean_dec_ref(v___x_3655_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3679_, lean_object* v___x_3680_, lean_object* v_k_3681_, lean_object* v___x_3682_, uint8_t v___x_3683_, uint8_t v___x_3684_, lean_object* v_00_u03b1_3685_, lean_object* v_00_u03b2_3686_, lean_object* v___x_3687_, lean_object* v_a_3688_, lean_object* v_x_3689_, lean_object* v___x_3690_, lean_object* v_ctorName_3691_, lean_object* v_minor_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; 
v___x_3700_ = lean_box(v___x_3683_);
v___x_3701_ = lean_box(v___x_3684_);
v___f_3702_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3702_, 0, v___x_3679_);
lean_closure_set(v___f_3702_, 1, v___x_3680_);
lean_closure_set(v___f_3702_, 2, v_k_3681_);
lean_closure_set(v___f_3702_, 3, v___x_3682_);
lean_closure_set(v___f_3702_, 4, v___x_3700_);
lean_closure_set(v___f_3702_, 5, v___x_3701_);
lean_closure_set(v___f_3702_, 6, v_00_u03b1_3685_);
lean_closure_set(v___f_3702_, 7, v_00_u03b2_3686_);
lean_closure_set(v___f_3702_, 8, v___x_3687_);
lean_closure_set(v___f_3702_, 9, v_ctorName_3691_);
lean_closure_set(v___f_3702_, 10, v_a_3688_);
lean_closure_set(v___f_3702_, 11, v_x_3689_);
v___x_3703_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3692_, v___x_3690_, v___f_3702_, v___x_3683_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3704_ = _args[0];
lean_object* v___x_3705_ = _args[1];
lean_object* v_k_3706_ = _args[2];
lean_object* v___x_3707_ = _args[3];
lean_object* v___x_3708_ = _args[4];
lean_object* v___x_3709_ = _args[5];
lean_object* v_00_u03b1_3710_ = _args[6];
lean_object* v_00_u03b2_3711_ = _args[7];
lean_object* v___x_3712_ = _args[8];
lean_object* v_a_3713_ = _args[9];
lean_object* v_x_3714_ = _args[10];
lean_object* v___x_3715_ = _args[11];
lean_object* v_ctorName_3716_ = _args[12];
lean_object* v_minor_3717_ = _args[13];
lean_object* v___y_3718_ = _args[14];
lean_object* v___y_3719_ = _args[15];
lean_object* v___y_3720_ = _args[16];
lean_object* v___y_3721_ = _args[17];
lean_object* v___y_3722_ = _args[18];
lean_object* v___y_3723_ = _args[19];
lean_object* v___y_3724_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3725_; uint8_t v___x_6476__boxed_3726_; lean_object* v_res_3727_; 
v___x_6475__boxed_3725_ = lean_unbox(v___x_3708_);
v___x_6476__boxed_3726_ = lean_unbox(v___x_3709_);
v_res_3727_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3704_, v___x_3705_, v_k_3706_, v___x_3707_, v___x_6475__boxed_3725_, v___x_6476__boxed_3726_, v_00_u03b1_3710_, v_00_u03b2_3711_, v___x_3712_, v_a_3713_, v_x_3714_, v___x_3715_, v_ctorName_3716_, v_minor_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3728_, lean_object* v_F_3729_, lean_object* v_val_3730_, lean_object* v_k_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3728_, v_F_3729_, v_val_3730_, v_k_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3740_, lean_object* v_name_3741_, uint8_t v_bi_3742_, lean_object* v_type_3743_, lean_object* v_k_3744_, uint8_t v_kind_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3741_, v_bi_3742_, v_type_3743_, v_k_3744_, v_kind_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3754_, lean_object* v_name_3755_, lean_object* v_bi_3756_, lean_object* v_type_3757_, lean_object* v_k_3758_, lean_object* v_kind_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v_bi_boxed_3767_; uint8_t v_kind_boxed_3768_; lean_object* v_res_3769_; 
v_bi_boxed_3767_ = lean_unbox(v_bi_3756_);
v_kind_boxed_3768_ = lean_unbox(v_kind_3759_);
v_res_3769_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3754_, v_name_3755_, v_bi_boxed_3767_, v_type_3757_, v_k_3758_, v_kind_boxed_3768_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3770_, lean_object* v_name_3771_, lean_object* v_type_3772_, lean_object* v_k_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3771_, v_type_3772_, v_k_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_name_3783_, lean_object* v_type_3784_, lean_object* v_k_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3782_, v_name_3783_, v_type_3784_, v_k_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
return v_res_3793_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3331__overap_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3804_ = lean_panic_fn_borrowed(v___x_3803_, v_msg_3795_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc(v___y_3797_);
lean_inc_ref(v___y_3796_);
v___x_3805_ = lean_apply_7(v___x_3331__overap_3804_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, lean_box(0));
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
return v_res_3814_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3818_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3819_ = lean_unsigned_to_nat(49u);
v___x_3820_ = lean_unsigned_to_nat(186u);
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3823_ = l_mkPanicMessageWithDecl(v___x_3822_, v___x_3821_, v___x_3820_, v___x_3819_, v___x_3818_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3824_, lean_object* v_a_3825_, lean_object* v_k_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v___x_3829_, lean_object* v___x_3830_, lean_object* v___x_3831_, lean_object* v_FNew_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
uint8_t v___x_3506__boxed_3840_; uint8_t v___x_3507__boxed_3841_; uint8_t v___x_3508__boxed_3842_; lean_object* v_res_3843_; 
v___x_3506__boxed_3840_ = lean_unbox(v___x_3829_);
v___x_3507__boxed_3841_ = lean_unbox(v___x_3830_);
v___x_3508__boxed_3842_ = lean_unbox(v___x_3831_);
v_res_3843_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3824_, v_a_3825_, v_k_3826_, v___x_3827_, v___x_3828_, v___x_3506__boxed_3840_, v___x_3507__boxed_3841_, v___x_3508__boxed_3842_, v_FNew_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___x_3827_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v___x_3852_, uint8_t v___x_3853_, uint8_t v___x_3854_, lean_object* v_k_3855_, lean_object* v___x_3856_, lean_object* v_00_u03b1_3857_, lean_object* v_00_u03b2_3858_, lean_object* v___x_3859_, lean_object* v_a_3860_, lean_object* v_x_3861_, lean_object* v_xs_3862_, lean_object* v_body_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3871_ = lean_array_get(v___x_3849_, v_xs_3862_, v___x_3850_);
v___x_3872_ = lean_array_get(v___x_3849_, v_xs_3862_, v___x_3851_);
v___x_3873_ = lean_array_get_size(v_xs_3862_);
v___x_3874_ = l_Array_toSubarray___redArg(v_xs_3862_, v___x_3852_, v___x_3873_);
v___x_3875_ = l_Subarray_copy___redArg(v___x_3874_);
v___x_3876_ = 1;
v___x_3877_ = l_Lean_Meta_mkLambdaFVars(v___x_3875_, v_body_3863_, v___x_3853_, v___x_3854_, v___x_3853_, v___x_3854_, v___x_3876_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec_ref(v___x_3875_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3904_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3904_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3904_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___f_3885_; lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3882_ = lean_box(v___x_3853_);
v___x_3883_ = lean_box(v___x_3854_);
v___x_3884_ = lean_box(v___x_3876_);
lean_inc(v___x_3871_);
lean_inc(v___x_3872_);
v___f_3885_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3885_, 0, v___x_3872_);
lean_closure_set(v___f_3885_, 1, v_a_3878_);
lean_closure_set(v___f_3885_, 2, v_k_3855_);
lean_closure_set(v___f_3885_, 3, v___x_3856_);
lean_closure_set(v___f_3885_, 4, v___x_3871_);
lean_closure_set(v___f_3885_, 5, v___x_3882_);
lean_closure_set(v___f_3885_, 6, v___x_3883_);
lean_closure_set(v___f_3885_, 7, v___x_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3881_ == 0)
{
lean_ctor_set_tag(v___x_3880_, 1);
lean_ctor_set(v___x_3880_, 0, v_00_u03b1_3857_);
v___x_3888_ = v___x_3880_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_00_u03b1_3857_);
v___x_3888_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_00_u03b2_3858_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3871_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3872_);
v___x_3892_ = lean_mk_empty_array_with_capacity(v___x_3859_);
v___x_3893_ = lean_array_push(v___x_3892_, v___x_3888_);
v___x_3894_ = lean_array_push(v___x_3893_, v___x_3889_);
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3890_);
v___x_3896_ = lean_array_push(v___x_3895_, v___x_3891_);
v___x_3897_ = l_Lean_Meta_mkAppOptM(v___x_3886_, v___x_3896_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = l_Lean_LocalDecl_type(v_a_3860_);
v___x_3900_ = l_Lean_Expr_replaceFVar(v___x_3899_, v_x_3861_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v___x_3899_);
v___x_3901_ = l_Lean_LocalDecl_userName(v_a_3860_);
v___x_3902_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3901_, v___x_3900_, v___f_3885_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
return v___x_3902_;
}
else
{
lean_dec_ref(v___f_3885_);
lean_dec_ref(v_x_3861_);
return v___x_3897_;
}
}
}
}
else
{
lean_dec(v___x_3872_);
lean_dec(v___x_3871_);
lean_dec_ref(v_x_3861_);
lean_dec_ref(v_00_u03b2_3858_);
lean_dec_ref(v_00_u03b1_3857_);
lean_dec(v___x_3856_);
lean_dec_ref(v_k_3855_);
return v___x_3877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3905_ = _args[0];
lean_object* v___x_3906_ = _args[1];
lean_object* v___x_3907_ = _args[2];
lean_object* v___x_3908_ = _args[3];
lean_object* v___x_3909_ = _args[4];
lean_object* v___x_3910_ = _args[5];
lean_object* v_k_3911_ = _args[6];
lean_object* v___x_3912_ = _args[7];
lean_object* v_00_u03b1_3913_ = _args[8];
lean_object* v_00_u03b2_3914_ = _args[9];
lean_object* v___x_3915_ = _args[10];
lean_object* v_a_3916_ = _args[11];
lean_object* v_x_3917_ = _args[12];
lean_object* v_xs_3918_ = _args[13];
lean_object* v_body_3919_ = _args[14];
lean_object* v___y_3920_ = _args[15];
lean_object* v___y_3921_ = _args[16];
lean_object* v___y_3922_ = _args[17];
lean_object* v___y_3923_ = _args[18];
lean_object* v___y_3924_ = _args[19];
lean_object* v___y_3925_ = _args[20];
lean_object* v___y_3926_ = _args[21];
_start:
{
uint8_t v___x_3533__boxed_3927_; uint8_t v___x_3534__boxed_3928_; lean_object* v_res_3929_; 
v___x_3533__boxed_3927_ = lean_unbox(v___x_3909_);
v___x_3534__boxed_3928_ = lean_unbox(v___x_3910_);
v_res_3929_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3905_, v___x_3906_, v___x_3907_, v___x_3908_, v___x_3533__boxed_3927_, v___x_3534__boxed_3928_, v_k_3911_, v___x_3912_, v_00_u03b1_3913_, v_00_u03b2_3914_, v___x_3915_, v_a_3916_, v_x_3917_, v_xs_3918_, v_body_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v_a_3916_);
lean_dec(v___x_3915_);
lean_dec(v___x_3907_);
lean_dec(v___x_3906_);
lean_dec_ref(v___x_3905_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3933_, lean_object* v_F_3934_, lean_object* v_val_3935_, lean_object* v_k_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___x_3953_; uint8_t v___y_3955_; uint8_t v___x_4046_; 
v___x_3953_ = l_Lean_instInhabitedExpr;
v___x_4046_ = l_Lean_Expr_isFVar(v_x_3933_);
if (v___x_4046_ == 0)
{
v___y_3955_ = v___x_4046_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
v___x_4047_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4048_ = lean_unsigned_to_nat(5u);
v___x_4049_ = l_Lean_Expr_isAppOfArity(v_val_3935_, v___x_4047_, v___x_4048_);
v___y_3955_ = v___x_4049_;
goto v___jp_3954_;
}
v___jp_3944_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3952_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3951_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_3952_;
}
v___jp_3954_:
{
if (v___y_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec_ref(v_x_3933_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
lean_inc(v_a_3940_);
lean_inc_ref(v_a_3939_);
lean_inc(v_a_3938_);
lean_inc_ref(v_a_3937_);
v___x_3956_ = lean_apply_9(v_k_3936_, v_F_3934_, v_val_3935_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, lean_box(0));
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3957_ = lean_unsigned_to_nat(3u);
v___x_3958_ = l_Lean_Expr_getAppNumArgs(v_val_3935_);
v___x_3959_ = lean_nat_sub(v___x_3958_, v___x_3957_);
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = lean_nat_sub(v___x_3959_, v___x_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = l_Lean_Expr_getRevArg_x21(v_val_3935_, v___x_3961_);
v___x_3963_ = lean_expr_eqv(v___x_3962_, v_x_3933_);
lean_dec_ref(v___x_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec(v___x_3958_);
lean_dec_ref(v_x_3933_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
lean_inc(v_a_3940_);
lean_inc_ref(v_a_3939_);
lean_inc(v_a_3938_);
lean_inc_ref(v_a_3937_);
v___x_3964_ = lean_apply_9(v_k_3936_, v_F_3934_, v_val_3935_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, lean_box(0));
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3965_ = lean_unsigned_to_nat(4u);
v___x_3966_ = lean_nat_sub(v___x_3958_, v___x_3965_);
v___x_3967_ = lean_nat_sub(v___x_3966_, v___x_3960_);
lean_dec(v___x_3966_);
v___x_3968_ = l_Lean_Expr_getRevArg_x21(v_val_3935_, v___x_3967_);
v___x_3969_ = l_Lean_Expr_isLambda(v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; 
lean_dec_ref(v___x_3968_);
lean_dec(v___x_3958_);
lean_dec_ref(v_x_3933_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
lean_inc(v_a_3940_);
lean_inc_ref(v_a_3939_);
lean_inc(v_a_3938_);
lean_inc_ref(v_a_3937_);
v___x_3970_ = lean_apply_9(v_k_3936_, v_F_3934_, v_val_3935_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, lean_box(0));
return v___x_3970_;
}
else
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3971_ = l_Lean_Expr_bindingBody_x21(v___x_3968_);
lean_dec_ref(v___x_3968_);
v___x_3972_ = l_Lean_Expr_isLambda(v___x_3971_);
lean_dec_ref(v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
lean_dec(v___x_3958_);
lean_dec_ref(v_x_3933_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
lean_inc(v_a_3940_);
lean_inc_ref(v_a_3939_);
lean_inc(v_a_3938_);
lean_inc_ref(v_a_3937_);
v___x_3973_ = lean_apply_9(v_k_3936_, v_F_3934_, v_val_3935_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, lean_box(0));
return v___x_3973_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = l_Lean_Expr_getAppFn(v_val_3935_);
v___x_3975_ = l_Lean_Expr_constLevels_x21(v___x_3974_);
lean_dec_ref(v___x_3974_);
if (lean_obj_tag(v___x_3975_) == 1)
{
lean_object* v_tail_3976_; 
v_tail_3976_ = lean_ctor_get(v___x_3975_, 1);
lean_inc(v_tail_3976_);
lean_dec_ref_known(v___x_3975_, 2);
if (lean_obj_tag(v_tail_3976_) == 1)
{
lean_object* v_tail_3977_; 
v_tail_3977_ = lean_ctor_get(v_tail_3976_, 1);
lean_inc(v_tail_3977_);
if (lean_obj_tag(v_tail_3977_) == 1)
{
lean_object* v_tail_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4044_; 
v_tail_3978_ = lean_ctor_get(v_tail_3977_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_tail_3977_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v_tail_3977_, 0);
lean_dec(v_unused_4045_);
v___x_3980_ = v_tail_3977_;
v_isShared_3981_ = v_isSharedCheck_4044_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_tail_3978_);
lean_dec(v_tail_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4044_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
if (lean_obj_tag(v_tail_3978_) == 0)
{
lean_object* v_dummy_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v_args_3985_; lean_object* v___x_3986_; lean_object* v_00_u03b1_3987_; lean_object* v_00_u03b2_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_dummy_3982_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3958_);
v___x_3983_ = lean_mk_array(v___x_3958_, v_dummy_3982_);
v___x_3984_ = lean_nat_sub(v___x_3958_, v___x_3960_);
lean_dec(v___x_3958_);
v_args_3985_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3935_, v___x_3983_, v___x_3984_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3987_ = lean_array_get(v___x_3953_, v_args_3985_, v___x_3986_);
v_00_u03b2_3988_ = lean_array_get(v___x_3953_, v_args_3985_, v___x_3960_);
v___x_3989_ = l_Lean_Expr_fvarId_x21(v_F_3934_);
v___x_3990_ = l_Lean_FVarId_getDecl___redArg(v___x_3989_, v_a_3939_, v_a_3941_, v_a_3942_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___f_3999_; lean_object* v___x_4000_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc_n(v_a_3991_, 2);
lean_dec_ref_known(v___x_3990_, 1);
v___x_3992_ = lean_box(v___x_3969_);
lean_inc_ref_n(v_x_3933_, 2);
v___f_3993_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3993_, 0, v_a_3991_);
lean_closure_set(v___f_3993_, 1, v___x_3953_);
lean_closure_set(v___f_3993_, 2, v___x_3986_);
lean_closure_set(v___f_3993_, 3, v_x_3933_);
lean_closure_set(v___f_3993_, 4, v___x_3992_);
v___x_3994_ = lean_unsigned_to_nat(2u);
v___x_3995_ = lean_array_get(v___x_3953_, v_args_3985_, v___x_3994_);
v___x_3996_ = 0;
v___x_3997_ = lean_box(v___x_3996_);
v___x_3998_ = lean_box(v___x_3969_);
lean_inc(v_00_u03b2_3988_);
lean_inc(v_00_u03b1_3987_);
v___f_3999_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_3999_, 0, v___x_3953_);
lean_closure_set(v___f_3999_, 1, v___x_3986_);
lean_closure_set(v___f_3999_, 2, v___x_3960_);
lean_closure_set(v___f_3999_, 3, v___x_3994_);
lean_closure_set(v___f_3999_, 4, v___x_3997_);
lean_closure_set(v___f_3999_, 5, v___x_3998_);
lean_closure_set(v___f_3999_, 6, v_k_3936_);
lean_closure_set(v___f_3999_, 7, v___x_3957_);
lean_closure_set(v___f_3999_, 8, v_00_u03b1_3987_);
lean_closure_set(v___f_3999_, 9, v_00_u03b2_3988_);
lean_closure_set(v___f_3999_, 10, v___x_3965_);
lean_closure_set(v___f_3999_, 11, v_a_3991_);
lean_closure_set(v___f_3999_, 12, v_x_3933_);
v___x_4000_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3995_, v___f_3993_, v___x_3996_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v_fst_4002_; lean_object* v_snd_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v_fst_4002_ = lean_ctor_get(v_a_4001_, 0);
lean_inc(v_fst_4002_);
v_snd_4003_ = lean_ctor_get(v_a_4001_, 1);
lean_inc(v_snd_4003_);
lean_dec(v_a_4001_);
v___x_4004_ = lean_array_get(v___x_3953_, v_args_3985_, v___x_3965_);
lean_dec_ref(v_args_3985_);
v___x_4005_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4004_, v___f_3999_, v___x_3996_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4027_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4010_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v_tail_3976_);
lean_ctor_set(v___x_3980_, 0, v_snd_4003_);
v___x_4012_ = v___x_3980_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_snd_4003_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_tail_3976_);
v___x_4012_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4013_ = l_Lean_mkConst(v___x_4010_, v___x_4012_);
v___x_4014_ = lean_unsigned_to_nat(6u);
v___x_4015_ = lean_mk_empty_array_with_capacity(v___x_4014_);
v___x_4016_ = lean_array_push(v___x_4015_, v_00_u03b1_3987_);
v___x_4017_ = lean_array_push(v___x_4016_, v_00_u03b2_3988_);
v___x_4018_ = lean_array_push(v___x_4017_, v_fst_4002_);
v___x_4019_ = lean_array_push(v___x_4018_, v_x_3933_);
v___x_4020_ = lean_array_push(v___x_4019_, v_a_4006_);
v___x_4021_ = lean_array_push(v___x_4020_, v_F_3934_);
v___x_4022_ = l_Lean_mkAppN(v___x_4013_, v___x_4021_);
lean_dec_ref(v___x_4021_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4022_);
v___x_4024_ = v___x_4008_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
else
{
lean_dec(v_snd_4003_);
lean_dec(v_fst_4002_);
lean_dec(v_00_u03b2_3988_);
lean_dec(v_00_u03b1_3987_);
lean_del_object(v___x_3980_);
lean_dec_ref_known(v_tail_3976_, 2);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
return v___x_4005_;
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v___f_3999_);
lean_dec(v_00_u03b2_3988_);
lean_dec(v_00_u03b1_3987_);
lean_dec_ref(v_args_3985_);
lean_del_object(v___x_3980_);
lean_dec_ref_known(v_tail_3976_, 2);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v_a_4028_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4000_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4000_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v_00_u03b2_3988_);
lean_dec(v_00_u03b1_3987_);
lean_dec_ref(v_args_3985_);
lean_del_object(v___x_3980_);
lean_dec_ref_known(v_tail_3976_, 2);
lean_dec_ref(v_k_3936_);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v_a_4036_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_3990_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_3990_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_del_object(v___x_3980_);
lean_dec(v_tail_3978_);
lean_dec_ref_known(v_tail_3976_, 2);
lean_dec(v___x_3958_);
lean_dec_ref(v_k_3936_);
lean_dec_ref(v_val_3935_);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
goto v___jp_3944_;
}
}
}
else
{
lean_dec_ref_known(v_tail_3976_, 2);
lean_dec(v_tail_3977_);
lean_dec(v___x_3958_);
lean_dec_ref(v_k_3936_);
lean_dec_ref(v_val_3935_);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
goto v___jp_3944_;
}
}
else
{
lean_dec(v_tail_3976_);
lean_dec(v___x_3958_);
lean_dec_ref(v_k_3936_);
lean_dec_ref(v_val_3935_);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
goto v___jp_3944_;
}
}
else
{
lean_dec(v___x_3975_);
lean_dec(v___x_3958_);
lean_dec_ref(v_k_3936_);
lean_dec_ref(v_val_3935_);
lean_dec_ref(v_F_3934_);
lean_dec_ref(v_x_3933_);
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
goto v___jp_3944_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4050_, lean_object* v_a_4051_, lean_object* v_k_4052_, lean_object* v___x_4053_, lean_object* v___x_4054_, uint8_t v___x_4055_, uint8_t v___x_4056_, uint8_t v___x_4057_, lean_object* v_FNew_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___x_4066_; 
lean_inc_ref(v_FNew_4058_);
lean_inc_ref(v___x_4050_);
v___x_4066_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4050_, v_FNew_4058_, v_a_4051_, v_k_4052_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = lean_mk_empty_array_with_capacity(v___x_4053_);
v___x_4069_ = lean_array_push(v___x_4068_, v___x_4054_);
v___x_4070_ = lean_array_push(v___x_4069_, v___x_4050_);
v___x_4071_ = lean_array_push(v___x_4070_, v_FNew_4058_);
v___x_4072_ = l_Lean_Meta_mkLambdaFVars(v___x_4071_, v_a_4067_, v___x_4055_, v___x_4056_, v___x_4055_, v___x_4056_, v___x_4057_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec_ref(v___x_4071_);
return v___x_4072_;
}
else
{
lean_dec_ref(v_FNew_4058_);
lean_dec_ref(v___x_4054_);
lean_dec_ref(v___x_4050_);
return v___x_4066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4073_, lean_object* v_F_4074_, lean_object* v_val_4075_, lean_object* v_k_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4073_, v_F_4074_, v_val_4075_, v_k_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_ref_4099_; uint8_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4098_, 1);
v_ref_4099_ = lean_ctor_get(v___y_4095_, 2);
v___x_4100_ = 0;
v___x_4101_ = l_Lean_SourceInfo_fromRef(v_ref_4099_, v___x_4100_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4101_);
v___x_4104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4101_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node1(v___x_4101_, v___x_4102_, v___x_4104_);
v___x_4106_ = l_Lean_Elab_Tactic_evalTactic(v___x_4105_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4106_;
}
else
{
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v___f_4126_; lean_object* v___x_4127_; 
v___f_4126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4127_ = l_Lean_Elab_Tactic_run(v_mvarId_4118_, v___f_4126_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4138_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
uint8_t v___x_4132_; 
v___x_4132_ = l_List_isEmpty___redArg(v_a_4128_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
lean_del_object(v___x_4130_);
v___x_4133_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4128_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
return v___x_4133_;
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4136_; 
lean_dec(v_a_4128_);
v___x_4134_ = lean_box(0);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4134_);
v___x_4136_ = v___x_4130_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
v_a_4139_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4127_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4127_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4156_, lean_object* v_x_4157_, lean_object* v_x_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v_ks_4160_; lean_object* v_vs_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4185_; 
v_ks_4160_ = lean_ctor_get(v_x_4156_, 0);
v_vs_4161_ = lean_ctor_get(v_x_4156_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_x_4156_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4163_ = v_x_4156_;
v_isShared_4164_ = v_isSharedCheck_4185_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_vs_4161_);
lean_inc(v_ks_4160_);
lean_dec(v_x_4156_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4185_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = lean_array_get_size(v_ks_4160_);
v___x_4166_ = lean_nat_dec_lt(v_x_4157_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
lean_dec(v_x_4157_);
v___x_4167_ = lean_array_push(v_ks_4160_, v_x_4158_);
v___x_4168_ = lean_array_push(v_vs_4161_, v_x_4159_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 1, v___x_4168_);
lean_ctor_set(v___x_4163_, 0, v___x_4167_);
v___x_4170_ = v___x_4163_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
else
{
lean_object* v_k_x27_4172_; uint8_t v___x_4173_; 
v_k_x27_4172_ = lean_array_fget_borrowed(v_ks_4160_, v_x_4157_);
v___x_4173_ = l_Lean_instBEqMVarId_beq(v_x_4158_, v_k_x27_4172_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4175_; 
if (v_isShared_4164_ == 0)
{
v___x_4175_ = v___x_4163_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_ks_4160_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_vs_4161_);
v___x_4175_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_nat_add(v_x_4157_, v___x_4176_);
lean_dec(v_x_4157_);
v_x_4156_ = v___x_4175_;
v_x_4157_ = v___x_4177_;
goto _start;
}
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4180_ = lean_array_fset(v_ks_4160_, v_x_4157_, v_x_4158_);
v___x_4181_ = lean_array_fset(v_vs_4161_, v_x_4157_, v_x_4159_);
lean_dec(v_x_4157_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 1, v___x_4181_);
lean_ctor_set(v___x_4163_, 0, v___x_4180_);
v___x_4183_ = v___x_4163_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4186_, lean_object* v_k_4187_, lean_object* v_v_4188_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4186_, v___x_4189_, v_k_4187_, v_v_4188_);
return v___x_4190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4192_, size_t v_x_4193_, size_t v_x_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
if (lean_obj_tag(v_x_4192_) == 0)
{
lean_object* v_es_4197_; size_t v___x_4198_; size_t v___x_4199_; lean_object* v_j_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v_es_4197_ = lean_ctor_get(v_x_4192_, 0);
v___x_4198_ = ((size_t)31ULL);
v___x_4199_ = lean_usize_land(v_x_4193_, v___x_4198_);
v_j_4200_ = lean_usize_to_nat(v___x_4199_);
v___x_4201_ = lean_array_get_size(v_es_4197_);
v___x_4202_ = lean_nat_dec_lt(v_j_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_dec(v_j_4200_);
lean_dec(v_x_4196_);
lean_dec(v_x_4195_);
return v_x_4192_;
}
else
{
lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4241_; 
lean_inc_ref(v_es_4197_);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4192_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; 
v_unused_4242_ = lean_ctor_get(v_x_4192_, 0);
lean_dec(v_unused_4242_);
v___x_4204_ = v_x_4192_;
v_isShared_4205_ = v_isSharedCheck_4241_;
goto v_resetjp_4203_;
}
else
{
lean_dec(v_x_4192_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4241_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_v_4206_; lean_object* v___x_4207_; lean_object* v_xs_x27_4208_; lean_object* v___y_4210_; 
v_v_4206_ = lean_array_fget(v_es_4197_, v_j_4200_);
v___x_4207_ = lean_box(0);
v_xs_x27_4208_ = lean_array_fset(v_es_4197_, v_j_4200_, v___x_4207_);
switch(lean_obj_tag(v_v_4206_))
{
case 0:
{
lean_object* v_key_4215_; lean_object* v_val_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4226_; 
v_key_4215_ = lean_ctor_get(v_v_4206_, 0);
v_val_4216_ = lean_ctor_get(v_v_4206_, 1);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_v_4206_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4218_ = v_v_4206_;
v_isShared_4219_ = v_isSharedCheck_4226_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_val_4216_);
lean_inc(v_key_4215_);
lean_dec(v_v_4206_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4226_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
uint8_t v___x_4220_; 
v___x_4220_ = l_Lean_instBEqMVarId_beq(v_x_4195_, v_key_4215_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_del_object(v___x_4218_);
v___x_4221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4215_, v_val_4216_, v_x_4195_, v_x_4196_);
v___x_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
v___y_4210_ = v___x_4222_;
goto v___jp_4209_;
}
else
{
lean_object* v___x_4224_; 
lean_dec(v_val_4216_);
lean_dec(v_key_4215_);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 1, v_x_4196_);
lean_ctor_set(v___x_4218_, 0, v_x_4195_);
v___x_4224_ = v___x_4218_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_x_4195_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_x_4196_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
v___y_4210_ = v___x_4224_;
goto v___jp_4209_;
}
}
}
}
case 1:
{
lean_object* v_node_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4239_; 
v_node_4227_ = lean_ctor_get(v_v_4206_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_v_4206_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4229_ = v_v_4206_;
v_isShared_4230_ = v_isSharedCheck_4239_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_node_4227_);
lean_dec(v_v_4206_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4239_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
size_t v___x_4231_; size_t v___x_4232_; size_t v___x_4233_; size_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4231_ = ((size_t)5ULL);
v___x_4232_ = lean_usize_shift_right(v_x_4193_, v___x_4231_);
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_x_4194_, v___x_4233_);
v___x_4235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4227_, v___x_4232_, v___x_4234_, v_x_4195_, v_x_4196_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4235_);
v___x_4237_ = v___x_4229_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
v___y_4210_ = v___x_4237_;
goto v___jp_4209_;
}
}
}
default: 
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4240_, 0, v_x_4195_);
lean_ctor_set(v___x_4240_, 1, v_x_4196_);
v___y_4210_ = v___x_4240_;
goto v___jp_4209_;
}
}
v___jp_4209_:
{
lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4211_ = lean_array_fset(v_xs_x27_4208_, v_j_4200_, v___y_4210_);
lean_dec(v_j_4200_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4211_);
v___x_4213_ = v___x_4204_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
else
{
lean_object* v_ks_4243_; lean_object* v_vs_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4262_; 
v_ks_4243_ = lean_ctor_get(v_x_4192_, 0);
v_vs_4244_ = lean_ctor_get(v_x_4192_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_x_4192_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4246_ = v_x_4192_;
v_isShared_4247_ = v_isSharedCheck_4262_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_vs_4244_);
lean_inc(v_ks_4243_);
lean_dec(v_x_4192_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4262_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_ks_4243_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_vs_4244_);
v___x_4249_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v_newNode_4250_; size_t v___x_4251_; uint8_t v___x_4252_; 
v_newNode_4250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4249_, v_x_4195_, v_x_4196_);
v___x_4251_ = ((size_t)7ULL);
v___x_4252_ = lean_usize_dec_le(v___x_4251_, v_x_4194_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4253_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4250_);
v___x_4254_ = lean_unsigned_to_nat(4u);
v___x_4255_ = lean_nat_dec_lt(v___x_4253_, v___x_4254_);
lean_dec(v___x_4253_);
if (v___x_4255_ == 0)
{
lean_object* v_ks_4256_; lean_object* v_vs_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_ks_4256_ = lean_ctor_get(v_newNode_4250_, 0);
lean_inc_ref(v_ks_4256_);
v_vs_4257_ = lean_ctor_get(v_newNode_4250_, 1);
lean_inc_ref(v_vs_4257_);
lean_dec_ref(v_newNode_4250_);
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4194_, v_ks_4256_, v_vs_4257_, v___x_4258_, v___x_4259_);
lean_dec_ref(v_vs_4257_);
lean_dec_ref(v_ks_4256_);
return v___x_4260_;
}
else
{
return v_newNode_4250_;
}
}
else
{
return v_newNode_4250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4263_, lean_object* v_keys_4264_, lean_object* v_vals_4265_, lean_object* v_i_4266_, lean_object* v_entries_4267_){
_start:
{
lean_object* v___x_4268_; uint8_t v___x_4269_; 
v___x_4268_ = lean_array_get_size(v_keys_4264_);
v___x_4269_ = lean_nat_dec_lt(v_i_4266_, v___x_4268_);
if (v___x_4269_ == 0)
{
lean_dec(v_i_4266_);
return v_entries_4267_;
}
else
{
lean_object* v_k_4270_; lean_object* v_v_4271_; uint64_t v___x_4272_; size_t v_h_4273_; size_t v___x_4274_; lean_object* v___x_4275_; size_t v___x_4276_; size_t v___x_4277_; size_t v___x_4278_; size_t v_h_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_k_4270_ = lean_array_fget_borrowed(v_keys_4264_, v_i_4266_);
v_v_4271_ = lean_array_fget_borrowed(v_vals_4265_, v_i_4266_);
v___x_4272_ = l_Lean_instHashableMVarId_hash(v_k_4270_);
v_h_4273_ = lean_uint64_to_usize(v___x_4272_);
v___x_4274_ = ((size_t)5ULL);
v___x_4275_ = lean_unsigned_to_nat(1u);
v___x_4276_ = ((size_t)1ULL);
v___x_4277_ = lean_usize_sub(v_depth_4263_, v___x_4276_);
v___x_4278_ = lean_usize_mul(v___x_4274_, v___x_4277_);
v_h_4279_ = lean_usize_shift_right(v_h_4273_, v___x_4278_);
v___x_4280_ = lean_nat_add(v_i_4266_, v___x_4275_);
lean_dec(v_i_4266_);
lean_inc(v_v_4271_);
lean_inc(v_k_4270_);
v___x_4281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4267_, v_h_4279_, v_depth_4263_, v_k_4270_, v_v_4271_);
v_i_4266_ = v___x_4280_;
v_entries_4267_ = v___x_4281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4283_, lean_object* v_keys_4284_, lean_object* v_vals_4285_, lean_object* v_i_4286_, lean_object* v_entries_4287_){
_start:
{
size_t v_depth_boxed_4288_; lean_object* v_res_4289_; 
v_depth_boxed_4288_ = lean_unbox_usize(v_depth_4283_);
lean_dec(v_depth_4283_);
v_res_4289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4288_, v_keys_4284_, v_vals_4285_, v_i_4286_, v_entries_4287_);
lean_dec_ref(v_vals_4285_);
lean_dec_ref(v_keys_4284_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4290_, lean_object* v_x_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_, lean_object* v_x_4294_){
_start:
{
size_t v_x_3985__boxed_4295_; size_t v_x_3986__boxed_4296_; lean_object* v_res_4297_; 
v_x_3985__boxed_4295_ = lean_unbox_usize(v_x_4291_);
lean_dec(v_x_4291_);
v_x_3986__boxed_4296_ = lean_unbox_usize(v_x_4292_);
lean_dec(v_x_4292_);
v_res_4297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4290_, v_x_3985__boxed_4295_, v_x_3986__boxed_4296_, v_x_4293_, v_x_4294_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4298_, lean_object* v_x_4299_, lean_object* v_x_4300_){
_start:
{
uint64_t v___x_4301_; size_t v___x_4302_; size_t v___x_4303_; lean_object* v___x_4304_; 
v___x_4301_ = l_Lean_instHashableMVarId_hash(v_x_4299_);
v___x_4302_ = lean_uint64_to_usize(v___x_4301_);
v___x_4303_ = ((size_t)1ULL);
v___x_4304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4298_, v___x_4302_, v___x_4303_, v_x_4299_, v_x_4300_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4305_, lean_object* v_val_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v_mctx_4310_; lean_object* v_cache_4311_; lean_object* v_zetaDeltaFVarIds_4312_; lean_object* v_postponed_4313_; lean_object* v_diag_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4343_; 
v___x_4309_ = lean_st_ref_take(v___y_4307_);
v_mctx_4310_ = lean_ctor_get(v___x_4309_, 0);
v_cache_4311_ = lean_ctor_get(v___x_4309_, 1);
v_zetaDeltaFVarIds_4312_ = lean_ctor_get(v___x_4309_, 2);
v_postponed_4313_ = lean_ctor_get(v___x_4309_, 3);
v_diag_4314_ = lean_ctor_get(v___x_4309_, 4);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4316_ = v___x_4309_;
v_isShared_4317_ = v_isSharedCheck_4343_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_diag_4314_);
lean_inc(v_postponed_4313_);
lean_inc(v_zetaDeltaFVarIds_4312_);
lean_inc(v_cache_4311_);
lean_inc(v_mctx_4310_);
lean_dec(v___x_4309_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4343_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_depth_4318_; lean_object* v_levelAssignDepth_4319_; lean_object* v_lmvarCounter_4320_; lean_object* v_mvarCounter_4321_; lean_object* v_lDecls_4322_; lean_object* v_decls_4323_; lean_object* v_userNames_4324_; lean_object* v_lAssignment_4325_; lean_object* v_eAssignment_4326_; lean_object* v_dAssignment_4327_; lean_object* v_instanceTypedMVars_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4342_; 
v_depth_4318_ = lean_ctor_get(v_mctx_4310_, 0);
v_levelAssignDepth_4319_ = lean_ctor_get(v_mctx_4310_, 1);
v_lmvarCounter_4320_ = lean_ctor_get(v_mctx_4310_, 2);
v_mvarCounter_4321_ = lean_ctor_get(v_mctx_4310_, 3);
v_lDecls_4322_ = lean_ctor_get(v_mctx_4310_, 4);
v_decls_4323_ = lean_ctor_get(v_mctx_4310_, 5);
v_userNames_4324_ = lean_ctor_get(v_mctx_4310_, 6);
v_lAssignment_4325_ = lean_ctor_get(v_mctx_4310_, 7);
v_eAssignment_4326_ = lean_ctor_get(v_mctx_4310_, 8);
v_dAssignment_4327_ = lean_ctor_get(v_mctx_4310_, 9);
v_instanceTypedMVars_4328_ = lean_ctor_get(v_mctx_4310_, 10);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_mctx_4310_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4330_ = v_mctx_4310_;
v_isShared_4331_ = v_isSharedCheck_4342_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_instanceTypedMVars_4328_);
lean_inc(v_dAssignment_4327_);
lean_inc(v_eAssignment_4326_);
lean_inc(v_lAssignment_4325_);
lean_inc(v_userNames_4324_);
lean_inc(v_decls_4323_);
lean_inc(v_lDecls_4322_);
lean_inc(v_mvarCounter_4321_);
lean_inc(v_lmvarCounter_4320_);
lean_inc(v_levelAssignDepth_4319_);
lean_inc(v_depth_4318_);
lean_dec(v_mctx_4310_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4342_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4332_ = lean_box(0);
v___x_4333_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4326_, v_mvarId_4305_, v_val_4306_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 8, v___x_4333_);
v___x_4335_ = v___x_4330_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_depth_4318_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_levelAssignDepth_4319_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_lmvarCounter_4320_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_mvarCounter_4321_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_lDecls_4322_);
lean_ctor_set(v_reuseFailAlloc_4341_, 5, v_decls_4323_);
lean_ctor_set(v_reuseFailAlloc_4341_, 6, v_userNames_4324_);
lean_ctor_set(v_reuseFailAlloc_4341_, 7, v_lAssignment_4325_);
lean_ctor_set(v_reuseFailAlloc_4341_, 8, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4341_, 9, v_dAssignment_4327_);
lean_ctor_set(v_reuseFailAlloc_4341_, 10, v_instanceTypedMVars_4328_);
v___x_4335_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4335_);
v___x_4337_ = v___x_4316_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_cache_4311_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_zetaDeltaFVarIds_4312_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_postponed_4313_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_diag_4314_);
v___x_4337_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = lean_st_ref_put(v___y_4307_, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4332_);
return v___x_4339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4344_, lean_object* v_val_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4344_, v_val_4345_, v___y_4346_);
lean_dec(v___y_4346_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4353_, lean_object* v_mv_u2082_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4363_; 
lean_inc(v_mv_u2081_4353_);
v___x_4363_ = l_Lean_MVarId_getDecl(v_mv_u2081_4353_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4365_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
lean_inc(v_mv_u2082_4354_);
v___x_4365_ = l_Lean_MVarId_getDecl(v_mv_u2082_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v_lctx_4367_; lean_object* v_type_4368_; lean_object* v_lctx_4369_; lean_object* v_type_4370_; uint8_t v___x_4371_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v_lctx_4367_ = lean_ctor_get(v_a_4364_, 1);
lean_inc_ref(v_lctx_4367_);
v_type_4368_ = lean_ctor_get(v_a_4364_, 2);
lean_inc_ref(v_type_4368_);
lean_dec(v_a_4364_);
v_lctx_4369_ = lean_ctor_get(v_a_4366_, 1);
lean_inc_ref(v_lctx_4369_);
v_type_4370_ = lean_ctor_get(v_a_4366_, 2);
lean_inc_ref(v_type_4370_);
lean_dec(v_a_4366_);
v___x_4371_ = lean_expr_eqv(v_type_4368_, v_type_4370_);
lean_dec_ref(v_type_4370_);
lean_dec_ref(v_type_4368_);
if (v___x_4371_ == 0)
{
lean_dec_ref(v_lctx_4369_);
lean_dec_ref(v_lctx_4367_);
lean_dec(v_mv_u2082_4354_);
lean_dec(v_mv_u2081_4353_);
goto v___jp_4360_;
}
else
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4373_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4367_, v_lctx_4369_, v___x_4372_);
if (v___x_4373_ == 0)
{
uint8_t v___x_4374_; 
v___x_4374_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4369_, v_lctx_4367_, v___x_4372_);
lean_dec_ref(v_lctx_4367_);
lean_dec_ref(v_lctx_4369_);
if (v___x_4374_ == 0)
{
lean_dec(v_mv_u2082_4354_);
lean_dec(v_mv_u2081_4353_);
goto v___jp_4360_;
}
else
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4386_; 
v___x_4375_ = l_Lean_Expr_mvar___override(v_mv_u2082_4354_);
v___x_4376_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4353_, v___x_4375_, v___y_4356_);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4386_ == 0)
{
lean_object* v_unused_4387_; 
v_unused_4387_ = lean_ctor_get(v___x_4376_, 0);
lean_dec(v_unused_4387_);
v___x_4378_ = v___x_4376_;
v_isShared_4379_ = v_isSharedCheck_4386_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v___x_4376_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4386_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4380_ = lean_box(v___x_4373_);
v___x_4381_ = lean_box(v___x_4371_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4380_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4382_);
v___x_4384_ = v___x_4378_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4400_; 
lean_dec_ref(v_lctx_4369_);
lean_dec_ref(v_lctx_4367_);
v___x_4388_ = l_Lean_Expr_mvar___override(v_mv_u2081_4353_);
v___x_4389_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4354_, v___x_4388_, v___y_4356_);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4389_, 0);
lean_dec(v_unused_4401_);
v___x_4391_ = v___x_4389_;
v_isShared_4392_ = v_isSharedCheck_4400_;
goto v_resetjp_4390_;
}
else
{
lean_dec(v___x_4389_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4400_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4393_ = 0;
v___x_4394_ = lean_box(v___x_4371_);
v___x_4395_ = lean_box(v___x_4393_);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v___x_4396_);
v___x_4398_ = v___x_4391_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_a_4364_);
lean_dec(v_mv_u2082_4354_);
lean_dec(v_mv_u2081_4353_);
v_a_4402_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4365_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4365_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
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
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_mv_u2082_4354_);
lean_dec(v_mv_u2081_4353_);
v_a_4410_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4363_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4363_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
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
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
v___jp_4360_:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4418_, lean_object* v_mv_u2082_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4418_, v_mv_u2082_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4426_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4440_, lean_object* v___x_4441_, lean_object* v___x_4442_, lean_object* v___x_4443_, lean_object* v_a_4444_, uint8_t v___x_4445_, lean_object* v_snd_4446_, lean_object* v_fst_4447_, lean_object* v_next_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_apply_7(v_f_4440_, v___x_4441_, v___x_4442_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, lean_box(0));
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4490_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4490_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4490_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_fst_4459_; lean_object* v_snd_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4489_; 
v_fst_4459_ = lean_ctor_get(v_a_4455_, 0);
v_snd_4460_ = lean_ctor_get(v_a_4455_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_a_4455_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4462_ = v_a_4455_;
v_isShared_4463_ = v_isSharedCheck_4489_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_snd_4460_);
lean_inc(v_fst_4459_);
lean_dec(v_a_4455_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4489_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v_removed_4465_; lean_object* v_numRemoved_4466_; uint8_t v___x_4485_; 
v___x_4485_ = lean_unbox(v_fst_4459_);
lean_dec(v_fst_4459_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = lean_nat_add(v_snd_4446_, v___x_4443_);
lean_dec(v_snd_4446_);
v___x_4487_ = lean_box(v___x_4445_);
v___x_4488_ = lean_array_set(v_fst_4447_, v_next_4448_, v___x_4487_);
v_removed_4465_ = v___x_4488_;
v_numRemoved_4466_ = v___x_4486_;
goto v___jp_4464_;
}
else
{
v_removed_4465_ = v_fst_4447_;
v_numRemoved_4466_ = v_snd_4446_;
goto v___jp_4464_;
}
v___jp_4464_:
{
uint8_t v___x_4467_; 
v___x_4467_ = lean_unbox(v_snd_4460_);
lean_dec(v_snd_4460_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4468_ = lean_nat_add(v_numRemoved_4466_, v___x_4443_);
lean_dec(v_numRemoved_4466_);
v___x_4469_ = lean_box(v___x_4445_);
v___x_4470_ = lean_array_set(v_removed_4465_, v_a_4444_, v___x_4469_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 1, v___x_4468_);
lean_ctor_set(v___x_4462_, 0, v___x_4470_);
v___x_4472_ = v___x_4462_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4468_);
v___x_4472_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4473_);
v___x_4475_ = v___x_4457_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
else
{
lean_object* v___x_4479_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 1, v_numRemoved_4466_);
lean_ctor_set(v___x_4462_, 0, v_removed_4465_);
v___x_4479_ = v___x_4462_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_removed_4465_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_numRemoved_4466_);
v___x_4479_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4480_);
v___x_4482_ = v___x_4457_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_fst_4447_);
lean_dec(v_snd_4446_);
v_a_4491_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4454_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4454_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4499_, lean_object* v___x_4500_, lean_object* v___x_4501_, lean_object* v___x_4502_, lean_object* v_a_4503_, lean_object* v___x_4504_, lean_object* v_snd_4505_, lean_object* v_fst_4506_, lean_object* v_next_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
uint8_t v___x_4358__boxed_4513_; lean_object* v_res_4514_; 
v___x_4358__boxed_4513_ = lean_unbox(v___x_4504_);
v_res_4514_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4499_, v___x_4500_, v___x_4501_, v___x_4502_, v_a_4503_, v___x_4358__boxed_4513_, v_snd_4505_, v_fst_4506_, v_next_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
lean_dec(v_next_4507_);
lean_dec(v_a_4503_);
lean_dec(v___x_4502_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4515_, lean_object* v_a_4516_, lean_object* v_next_4517_, lean_object* v_f_4518_, lean_object* v_a_4519_, lean_object* v_b_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
uint8_t v___x_4526_; 
v___x_4526_ = lean_nat_dec_lt(v_a_4519_, v_upperBound_4515_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_dec(v_a_4519_);
lean_dec_ref(v_f_4518_);
lean_dec(v_next_4517_);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_b_4520_);
return v___x_4527_;
}
else
{
lean_object* v_fst_4528_; lean_object* v_snd_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4576_; 
v_fst_4528_ = lean_ctor_get(v_b_4520_, 0);
v_snd_4529_ = lean_ctor_get(v_b_4520_, 1);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_b_4520_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4531_ = v_b_4520_;
v_isShared_4532_ = v_isSharedCheck_4576_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_snd_4529_);
lean_inc(v_fst_4528_);
lean_dec(v_b_4520_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4576_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; lean_object* v___y_4535_; uint8_t v___y_4558_; uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4568_ = 0;
v___x_4569_ = lean_box(v___x_4568_);
v___x_4570_ = lean_array_get(v___x_4569_, v_fst_4528_, v_next_4517_);
lean_dec(v___x_4569_);
v___x_4571_ = lean_unbox(v___x_4570_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; 
lean_dec(v___x_4570_);
v___x_4572_ = lean_box(v___x_4568_);
v___x_4573_ = lean_array_get(v___x_4572_, v_fst_4528_, v_a_4519_);
lean_dec(v___x_4572_);
v___x_4574_ = lean_unbox(v___x_4573_);
lean_dec(v___x_4573_);
v___y_4558_ = v___x_4574_;
goto v___jp_4557_;
}
else
{
uint8_t v___x_4575_; 
v___x_4575_ = lean_unbox(v___x_4570_);
lean_dec(v___x_4570_);
v___y_4558_ = v___x_4575_;
goto v___jp_4557_;
}
v___jp_4534_:
{
lean_object* v___x_4536_; 
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
v___x_4536_ = lean_apply_5(v___y_4535_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, lean_box(0));
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4548_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4548_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4548_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
if (lean_obj_tag(v_a_4537_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; 
lean_dec(v_a_4519_);
lean_dec_ref(v_f_4518_);
lean_dec(v_next_4517_);
v_a_4541_ = lean_ctor_get(v_a_4537_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v_a_4537_, 1);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v_a_4541_);
v___x_4543_ = v___x_4539_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4541_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4546_; 
lean_del_object(v___x_4539_);
v_a_4545_ = lean_ctor_get(v_a_4537_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v_a_4537_, 1);
v___x_4546_ = lean_nat_add(v_a_4519_, v___x_4533_);
lean_dec(v_a_4519_);
v_a_4519_ = v___x_4546_;
v_b_4520_ = v_a_4545_;
goto _start;
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v_a_4519_);
lean_dec_ref(v_f_4518_);
lean_dec(v_next_4517_);
v_a_4549_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4536_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4536_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
v___jp_4557_:
{
if (v___y_4558_ == 0)
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___f_4562_; 
lean_del_object(v___x_4531_);
v___x_4559_ = lean_array_fget_borrowed(v_a_4516_, v_next_4517_);
v___x_4560_ = lean_array_fget_borrowed(v_a_4516_, v_a_4519_);
v___x_4561_ = lean_box(v___x_4526_);
lean_inc(v_next_4517_);
lean_inc(v_a_4519_);
lean_inc(v___x_4560_);
lean_inc(v___x_4559_);
lean_inc_ref(v_f_4518_);
v___f_4562_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4562_, 0, v_f_4518_);
lean_closure_set(v___f_4562_, 1, v___x_4559_);
lean_closure_set(v___f_4562_, 2, v___x_4560_);
lean_closure_set(v___f_4562_, 3, v___x_4533_);
lean_closure_set(v___f_4562_, 4, v_a_4519_);
lean_closure_set(v___f_4562_, 5, v___x_4561_);
lean_closure_set(v___f_4562_, 6, v_snd_4529_);
lean_closure_set(v___f_4562_, 7, v_fst_4528_);
lean_closure_set(v___f_4562_, 8, v_next_4517_);
v___y_4535_ = v___f_4562_;
goto v___jp_4534_;
}
else
{
lean_object* v___x_4564_; 
if (v_isShared_4532_ == 0)
{
v___x_4564_ = v___x_4531_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_fst_4528_);
lean_ctor_set(v_reuseFailAlloc_4567_, 1, v_snd_4529_);
v___x_4564_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4565_; lean_object* v___f_4566_; 
v___x_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
v___f_4566_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4566_, 0, v___x_4565_);
v___y_4535_ = v___f_4566_;
goto v___jp_4534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4577_, lean_object* v_a_4578_, lean_object* v_next_4579_, lean_object* v_f_4580_, lean_object* v_a_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4577_, v_a_4578_, v_next_4579_, v_f_4580_, v_a_4581_, v_b_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec_ref(v_a_4578_);
lean_dec(v_upperBound_4577_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4589_, lean_object* v___x_4590_, lean_object* v_a_4591_, lean_object* v_f_4592_, lean_object* v_a_4593_, lean_object* v_b_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
uint8_t v___x_4600_; 
v___x_4600_ = lean_nat_dec_lt(v_a_4593_, v_upperBound_4589_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; 
lean_dec(v_a_4593_);
lean_dec_ref(v_f_4592_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v_b_4594_);
return v___x_4601_;
}
else
{
lean_object* v_fst_4602_; lean_object* v_snd_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4624_; 
v_fst_4602_ = lean_ctor_get(v_b_4594_, 0);
v_snd_4603_ = lean_ctor_get(v_b_4594_, 1);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_b_4594_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4605_ = v_b_4594_;
v_isShared_4606_ = v_isSharedCheck_4624_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_snd_4603_);
lean_inc(v_fst_4602_);
lean_dec(v_b_4594_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4624_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4610_; 
v___x_4607_ = lean_unsigned_to_nat(1u);
v___x_4608_ = lean_nat_add(v_a_4593_, v___x_4607_);
if (v_isShared_4606_ == 0)
{
v___x_4610_ = v___x_4605_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_fst_4602_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_snd_4603_);
v___x_4610_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4611_; 
lean_inc(v___x_4608_);
lean_inc_ref(v_f_4592_);
v___x_4611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4590_, v_a_4591_, v_a_4593_, v_f_4592_, v___x_4608_, v___x_4610_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v_fst_4613_; lean_object* v_snd_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4622_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref_known(v___x_4611_, 1);
v_fst_4613_ = lean_ctor_get(v_a_4612_, 0);
v_snd_4614_ = lean_ctor_get(v_a_4612_, 1);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_a_4612_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4616_ = v_a_4612_;
v_isShared_4617_ = v_isSharedCheck_4622_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_snd_4614_);
lean_inc(v_fst_4613_);
lean_dec(v_a_4612_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4622_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_fst_4613_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_snd_4614_);
v___x_4619_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
v_a_4593_ = v___x_4608_;
v_b_4594_ = v___x_4619_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4608_);
lean_dec_ref(v_f_4592_);
return v___x_4611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4625_, lean_object* v___x_4626_, lean_object* v_a_4627_, lean_object* v_f_4628_, lean_object* v_a_4629_, lean_object* v_b_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4625_, v___x_4626_, v_a_4627_, v_f_4628_, v_a_4629_, v_b_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec_ref(v_a_4627_);
lean_dec(v___x_4626_);
lean_dec(v_upperBound_4625_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4637_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4651_, lean_object* v_removed_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v___y_4662_; uint8_t v___x_4685_; 
v___x_4685_ = lean_nat_dec_lt(v_a_4654_, v_upperBound_4651_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; 
lean_dec(v_a_4654_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_b_4655_);
return v___x_4686_;
}
else
{
uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4687_ = 0;
v___x_4688_ = lean_box(v___x_4687_);
v___x_4689_ = lean_array_get(v___x_4688_, v_removed_4652_, v_a_4654_);
lean_dec(v___x_4688_);
v___x_4690_ = lean_unbox(v___x_4689_);
lean_dec(v___x_4689_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___f_4694_; 
v___x_4691_ = lean_array_fget_borrowed(v_a_4653_, v_a_4654_);
lean_inc(v___x_4691_);
v___x_4692_ = lean_array_push(v_b_4655_, v___x_4691_);
v___x_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
v___f_4694_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4694_, 0, v___x_4693_);
v___y_4662_ = v___f_4694_;
goto v___jp_4661_;
}
else
{
lean_object* v___x_4695_; lean_object* v___f_4696_; 
v___x_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4695_, 0, v_b_4655_);
v___f_4696_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4696_, 0, v___x_4695_);
v___y_4662_ = v___f_4696_;
goto v___jp_4661_;
}
}
v___jp_4661_:
{
lean_object* v___x_4663_; 
lean_inc(v___y_4659_);
lean_inc_ref(v___y_4658_);
lean_inc(v___y_4657_);
lean_inc_ref(v___y_4656_);
v___x_4663_ = lean_apply_5(v___y_4662_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, lean_box(0));
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4676_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4676_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4676_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
if (lean_obj_tag(v_a_4664_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; 
lean_dec(v_a_4654_);
v_a_4668_ = lean_ctor_get(v_a_4664_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v_a_4664_, 1);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v_a_4668_);
v___x_4670_ = v___x_4666_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4668_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
lean_del_object(v___x_4666_);
v_a_4672_ = lean_ctor_get(v_a_4664_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v_a_4664_, 1);
v___x_4673_ = lean_unsigned_to_nat(1u);
v___x_4674_ = lean_nat_add(v_a_4654_, v___x_4673_);
lean_dec(v_a_4654_);
v_a_4654_ = v___x_4674_;
v_b_4655_ = v_a_4672_;
goto _start;
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec(v_a_4654_);
v_a_4677_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4663_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4663_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4697_, lean_object* v_removed_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_b_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4697_, v_removed_4698_, v_a_4699_, v_a_4700_, v_b_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec_ref(v_a_4699_);
lean_dec_ref(v_removed_4698_);
lean_dec(v_upperBound_4697_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4708_, lean_object* v_f_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; uint8_t v___x_4716_; lean_object* v___x_4717_; lean_object* v_removed_4718_; lean_object* v_numRemoved_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4715_ = lean_array_get_size(v_a_4708_);
v___x_4716_ = 0;
v___x_4717_ = lean_box(v___x_4716_);
v_removed_4718_ = lean_mk_array(v___x_4715_, v___x_4717_);
v_numRemoved_4719_ = lean_unsigned_to_nat(0u);
v___x_4720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4720_, 0, v_removed_4718_);
lean_ctor_set(v___x_4720_, 1, v_numRemoved_4719_);
v___x_4721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4715_, v___x_4715_, v_a_4708_, v_f_4709_, v_numRemoved_4719_, v___x_4720_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v_fst_4723_; lean_object* v_snd_4724_; lean_object* v_a_x27_4725_; lean_object* v___x_4726_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4721_, 1);
v_fst_4723_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_fst_4723_);
v_snd_4724_ = lean_ctor_get(v_a_4722_, 1);
lean_inc(v_snd_4724_);
lean_dec(v_a_4722_);
v_a_x27_4725_ = lean_mk_empty_array_with_capacity(v_snd_4724_);
lean_dec(v_snd_4724_);
v___x_4726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4715_, v_fst_4723_, v_a_4708_, v_numRemoved_4719_, v_a_x27_4725_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v_fst_4723_);
return v___x_4726_;
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
v_a_4727_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4721_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4721_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4735_, lean_object* v_f_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4735_, v_f_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec_ref(v_a_4735_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v___f_4750_; lean_object* v___x_4751_; 
v___f_4750_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4751_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4744_, v___f_4750_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec_ref(v_mvars_4752_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4759_, lean_object* v_val_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4759_, v_val_4760_, v___y_4762_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4767_, lean_object* v_val_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4767_, v_val_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4775_, lean_object* v_a_4776_, lean_object* v_f_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4776_, v_f_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4784_, lean_object* v_a_4785_, lean_object* v_f_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4784_, v_a_4785_, v_f_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec_ref(v_a_4785_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4793_, lean_object* v_x_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4794_, v_x_4795_, v_x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4798_, lean_object* v_00_u03b1_4799_, lean_object* v_a_4800_, lean_object* v_next_4801_, lean_object* v_f_4802_, lean_object* v_inst_4803_, lean_object* v_R_4804_, lean_object* v_a_4805_, lean_object* v_b_4806_, lean_object* v_c_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4798_, v_a_4800_, v_next_4801_, v_f_4802_, v_a_4805_, v_b_4806_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4814_, lean_object* v_00_u03b1_4815_, lean_object* v_a_4816_, lean_object* v_next_4817_, lean_object* v_f_4818_, lean_object* v_inst_4819_, lean_object* v_R_4820_, lean_object* v_a_4821_, lean_object* v_b_4822_, lean_object* v_c_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4814_, v_00_u03b1_4815_, v_a_4816_, v_next_4817_, v_f_4818_, v_inst_4819_, v_R_4820_, v_a_4821_, v_b_4822_, v_c_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec_ref(v_a_4816_);
lean_dec(v_upperBound_4814_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4830_, lean_object* v_upperBound_4831_, lean_object* v_removed_4832_, lean_object* v_a_4833_, lean_object* v_inst_4834_, lean_object* v_R_4835_, lean_object* v_a_4836_, lean_object* v_b_4837_, lean_object* v_c_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4831_, v_removed_4832_, v_a_4833_, v_a_4836_, v_b_4837_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_upperBound_4846_, lean_object* v_removed_4847_, lean_object* v_a_4848_, lean_object* v_inst_4849_, lean_object* v_R_4850_, lean_object* v_a_4851_, lean_object* v_b_4852_, lean_object* v_c_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4845_, v_upperBound_4846_, v_removed_4847_, v_a_4848_, v_inst_4849_, v_R_4850_, v_a_4851_, v_b_4852_, v_c_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec_ref(v_a_4848_);
lean_dec_ref(v_removed_4847_);
lean_dec(v_upperBound_4846_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4860_, lean_object* v___x_4861_, lean_object* v_00_u03b1_4862_, lean_object* v_a_4863_, lean_object* v_f_4864_, lean_object* v_inst_4865_, lean_object* v_R_4866_, lean_object* v_a_4867_, lean_object* v_b_4868_, lean_object* v_c_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4860_, v___x_4861_, v_a_4863_, v_f_4864_, v_a_4867_, v_b_4868_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4876_, lean_object* v___x_4877_, lean_object* v_00_u03b1_4878_, lean_object* v_a_4879_, lean_object* v_f_4880_, lean_object* v_inst_4881_, lean_object* v_R_4882_, lean_object* v_a_4883_, lean_object* v_b_4884_, lean_object* v_c_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4876_, v___x_4877_, v_00_u03b1_4878_, v_a_4879_, v_f_4880_, v_inst_4881_, v_R_4882_, v_a_4883_, v_b_4884_, v_c_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
lean_dec(v___y_4889_);
lean_dec_ref(v___y_4888_);
lean_dec(v___y_4887_);
lean_dec_ref(v___y_4886_);
lean_dec_ref(v_a_4879_);
lean_dec(v___x_4877_);
lean_dec(v_upperBound_4876_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4892_, lean_object* v_x_4893_, size_t v_x_4894_, size_t v_x_4895_, lean_object* v_x_4896_, lean_object* v_x_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4893_, v_x_4894_, v_x_4895_, v_x_4896_, v_x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4899_, lean_object* v_x_4900_, lean_object* v_x_4901_, lean_object* v_x_4902_, lean_object* v_x_4903_, lean_object* v_x_4904_){
_start:
{
size_t v_x_4928__boxed_4905_; size_t v_x_4929__boxed_4906_; lean_object* v_res_4907_; 
v_x_4928__boxed_4905_ = lean_unbox_usize(v_x_4901_);
lean_dec(v_x_4901_);
v_x_4929__boxed_4906_ = lean_unbox_usize(v_x_4902_);
lean_dec(v_x_4902_);
v_res_4907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4899_, v_x_4900_, v_x_4928__boxed_4905_, v_x_4929__boxed_4906_, v_x_4903_, v_x_4904_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4908_, lean_object* v_n_4909_, lean_object* v_k_4910_, lean_object* v_v_4911_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4909_, v_k_4910_, v_v_4911_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4913_, size_t v_depth_4914_, lean_object* v_keys_4915_, lean_object* v_vals_4916_, lean_object* v_heq_4917_, lean_object* v_i_4918_, lean_object* v_entries_4919_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4914_, v_keys_4915_, v_vals_4916_, v_i_4918_, v_entries_4919_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4921_, lean_object* v_depth_4922_, lean_object* v_keys_4923_, lean_object* v_vals_4924_, lean_object* v_heq_4925_, lean_object* v_i_4926_, lean_object* v_entries_4927_){
_start:
{
size_t v_depth_boxed_4928_; lean_object* v_res_4929_; 
v_depth_boxed_4928_ = lean_unbox_usize(v_depth_4922_);
lean_dec(v_depth_4922_);
v_res_4929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4921_, v_depth_boxed_4928_, v_keys_4923_, v_vals_4924_, v_heq_4925_, v_i_4926_, v_entries_4927_);
lean_dec_ref(v_vals_4924_);
lean_dec_ref(v_keys_4923_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4930_, lean_object* v_x_4931_, lean_object* v_x_4932_, lean_object* v_x_4933_, lean_object* v_x_4934_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4931_, v_x_4932_, v_x_4933_, v_x_4934_);
return v___x_4935_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4938_ = l_Lean_stringToMessageData(v___x_4937_);
return v___x_4938_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4941_ = l_Lean_stringToMessageData(v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4942_, lean_object* v_as_4943_, size_t v_sz_4944_, size_t v_i_4945_, lean_object* v_b_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v_a_4953_; uint8_t v___x_4957_; 
v___x_4957_ = lean_usize_dec_lt(v_i_4945_, v_sz_4944_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; 
v___x_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4958_, 0, v_b_4946_);
return v___x_4958_;
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_array_uget_borrowed(v_as_4943_, v_i_4945_);
lean_inc(v_a_4959_);
v___x_4960_ = l_Lean_MVarId_getType(v_a_4959_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; lean_object* v___y_4966_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
if (lean_obj_tag(v_a_4961_) == 10)
{
lean_object* v_expr_4979_; 
v_expr_4979_ = lean_ctor_get(v_a_4961_, 1);
if (lean_obj_tag(v_expr_4979_) == 5)
{
lean_object* v_arg_4980_; lean_object* v___x_4981_; 
lean_inc_ref(v_expr_4979_);
lean_dec_ref_known(v_a_4961_, 2);
v_arg_4980_ = lean_ctor_get(v_expr_4979_, 1);
lean_inc_ref_n(v_arg_4980_, 2);
lean_dec_ref_known(v_expr_4979_, 2);
v___x_4981_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4942_, v_arg_4980_);
if (lean_obj_tag(v___x_4981_) == 1)
{
lean_object* v_val_4982_; lean_object* v_fst_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
lean_dec_ref(v_arg_4980_);
v_val_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_val_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v_fst_4983_ = lean_ctor_get(v_val_4982_, 0);
lean_inc(v_fst_4983_);
lean_dec(v_val_4982_);
v___x_4984_ = lean_array_get_size(v_b_4946_);
v___x_4985_ = lean_nat_dec_lt(v_fst_4983_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_dec(v_fst_4983_);
v_a_4953_ = v_b_4946_;
goto v___jp_4952_;
}
else
{
lean_object* v_v_4986_; lean_object* v___x_4987_; lean_object* v_xs_x27_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_v_4986_ = lean_array_fget(v_b_4946_, v_fst_4983_);
v___x_4987_ = lean_box(0);
v_xs_x27_4988_ = lean_array_fset(v_b_4946_, v_fst_4983_, v___x_4987_);
lean_inc(v_a_4959_);
v___x_4989_ = lean_array_push(v_v_4986_, v_a_4959_);
v___x_4990_ = lean_array_fset(v_xs_x27_4988_, v_fst_4983_, v___x_4989_);
lean_dec(v_fst_4983_);
v_a_4953_ = v___x_4990_;
goto v___jp_4952_;
}
}
else
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_dec(v___x_4981_);
v___x_4991_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_4992_ = l_Lean_indentExpr(v_arg_4980_);
v___x_4993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set(v___x_4993_, 1, v___x_4992_);
v___x_4994_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4993_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_dec_ref_known(v___x_4994_, 1);
v_a_4953_ = v_b_4946_;
goto v___jp_4952_;
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
lean_dec_ref(v_b_4946_);
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4994_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4994_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
else
{
v___y_4963_ = v___y_4947_;
v___y_4964_ = v___y_4948_;
v___y_4965_ = v___y_4949_;
v___y_4966_ = v___y_4950_;
goto v___jp_4962_;
}
}
else
{
v___y_4963_ = v___y_4947_;
v___y_4964_ = v___y_4948_;
v___y_4965_ = v___y_4949_;
v___y_4966_ = v___y_4950_;
goto v___jp_4962_;
}
v___jp_4962_:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4968_ = l_Lean_indentExpr(v_a_4961_);
v___x_4969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4967_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
v___x_4970_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4969_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_dec_ref_known(v___x_4970_, 1);
v_a_4953_ = v_b_4946_;
goto v___jp_4952_;
}
else
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
lean_dec_ref(v_b_4946_);
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec_ref(v_b_4946_);
v_a_5003_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4960_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4960_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
v___jp_4952_:
{
size_t v___x_4954_; size_t v___x_4955_; 
v___x_4954_ = ((size_t)1ULL);
v___x_4955_ = lean_usize_add(v_i_4945_, v___x_4954_);
v_i_4945_ = v___x_4955_;
v_b_4946_ = v_a_4953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5011_, lean_object* v_as_5012_, lean_object* v_sz_5013_, lean_object* v_i_5014_, lean_object* v_b_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
size_t v_sz_boxed_5021_; size_t v_i_boxed_5022_; lean_object* v_res_5023_; 
v_sz_boxed_5021_ = lean_unbox_usize(v_sz_5013_);
lean_dec(v_sz_5013_);
v_i_boxed_5022_ = lean_unbox_usize(v_i_5014_);
lean_dec(v_i_5014_);
v_res_5023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5011_, v_as_5012_, v_sz_boxed_5021_, v_i_boxed_5022_, v_b_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec_ref(v_as_5012_);
lean_dec_ref(v_argsPacker_5011_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5024_, lean_object* v_numFuncs_5025_, lean_object* v_goals_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v___x_5032_; lean_object* v_r_5033_; size_t v_sz_5034_; size_t v___x_5035_; lean_object* v___x_5036_; 
v___x_5032_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5033_ = lean_mk_array(v_numFuncs_5025_, v___x_5032_);
v_sz_5034_ = lean_array_size(v_goals_5026_);
v___x_5035_ = ((size_t)0ULL);
v___x_5036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5024_, v_goals_5026_, v_sz_5034_, v___x_5035_, v_r_5033_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5037_, lean_object* v_numFuncs_5038_, lean_object* v_goals_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5037_, v_numFuncs_5038_, v_goals_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec_ref(v_goals_5039_);
lean_dec_ref(v_argsPacker_5037_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; lean_object* v_infoState_5050_; uint8_t v_enabled_5051_; 
v___x_5049_ = lean_st_ref_get(v___y_5047_);
v_infoState_5050_ = lean_ctor_get(v___x_5049_, 8);
lean_inc_ref(v_infoState_5050_);
lean_dec(v___x_5049_);
v_enabled_5051_ = lean_ctor_get_uint8(v_infoState_5050_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5050_);
if (v_enabled_5051_ == 0)
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_dec_ref(v_t_5046_);
v___x_5052_ = lean_box(0);
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
return v___x_5053_;
}
else
{
lean_object* v___x_5054_; lean_object* v_infoState_5055_; lean_object* v_env_5056_; lean_object* v_nextMacroScope_5057_; lean_object* v_ngen_5058_; lean_object* v_auxDeclNGen_5059_; lean_object* v_traceState_5060_; lean_object* v_cache_5061_; lean_object* v_recordedDeps_5062_; lean_object* v_messages_5063_; lean_object* v_snapshotTasks_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5086_; 
v___x_5054_ = lean_st_ref_take(v___y_5047_);
v_infoState_5055_ = lean_ctor_get(v___x_5054_, 8);
v_env_5056_ = lean_ctor_get(v___x_5054_, 0);
v_nextMacroScope_5057_ = lean_ctor_get(v___x_5054_, 1);
v_ngen_5058_ = lean_ctor_get(v___x_5054_, 2);
v_auxDeclNGen_5059_ = lean_ctor_get(v___x_5054_, 3);
v_traceState_5060_ = lean_ctor_get(v___x_5054_, 4);
v_cache_5061_ = lean_ctor_get(v___x_5054_, 5);
v_recordedDeps_5062_ = lean_ctor_get(v___x_5054_, 6);
v_messages_5063_ = lean_ctor_get(v___x_5054_, 7);
v_snapshotTasks_5064_ = lean_ctor_get(v___x_5054_, 9);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5066_ = v___x_5054_;
v_isShared_5067_ = v_isSharedCheck_5086_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_snapshotTasks_5064_);
lean_inc(v_infoState_5055_);
lean_inc(v_messages_5063_);
lean_inc(v_recordedDeps_5062_);
lean_inc(v_cache_5061_);
lean_inc(v_traceState_5060_);
lean_inc(v_auxDeclNGen_5059_);
lean_inc(v_ngen_5058_);
lean_inc(v_nextMacroScope_5057_);
lean_inc(v_env_5056_);
lean_dec(v___x_5054_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5086_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
uint8_t v_enabled_5068_; lean_object* v_assignment_5069_; lean_object* v_lazyAssignment_5070_; lean_object* v_trees_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5085_; 
v_enabled_5068_ = lean_ctor_get_uint8(v_infoState_5055_, sizeof(void*)*3);
v_assignment_5069_ = lean_ctor_get(v_infoState_5055_, 0);
v_lazyAssignment_5070_ = lean_ctor_get(v_infoState_5055_, 1);
v_trees_5071_ = lean_ctor_get(v_infoState_5055_, 2);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_infoState_5055_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5073_ = v_infoState_5055_;
v_isShared_5074_ = v_isSharedCheck_5085_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_trees_5071_);
lean_inc(v_lazyAssignment_5070_);
lean_inc(v_assignment_5069_);
lean_dec(v_infoState_5055_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5085_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5078_; 
v___x_5075_ = lean_box(0);
v___x_5076_ = l_Lean_PersistentArray_push___redArg(v_trees_5071_, v_t_5046_);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 2, v___x_5076_);
v___x_5078_ = v___x_5073_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_assignment_5069_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v_lazyAssignment_5070_);
lean_ctor_set(v_reuseFailAlloc_5084_, 2, v___x_5076_);
lean_ctor_set_uint8(v_reuseFailAlloc_5084_, sizeof(void*)*3, v_enabled_5068_);
v___x_5078_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 8, v___x_5078_);
v___x_5080_ = v___x_5066_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_env_5056_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_nextMacroScope_5057_);
lean_ctor_set(v_reuseFailAlloc_5083_, 2, v_ngen_5058_);
lean_ctor_set(v_reuseFailAlloc_5083_, 3, v_auxDeclNGen_5059_);
lean_ctor_set(v_reuseFailAlloc_5083_, 4, v_traceState_5060_);
lean_ctor_set(v_reuseFailAlloc_5083_, 5, v_cache_5061_);
lean_ctor_set(v_reuseFailAlloc_5083_, 6, v_recordedDeps_5062_);
lean_ctor_set(v_reuseFailAlloc_5083_, 7, v_messages_5063_);
lean_ctor_set(v_reuseFailAlloc_5083_, 8, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5083_, 9, v_snapshotTasks_5064_);
v___x_5080_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = lean_st_ref_put(v___y_5047_, v___x_5080_);
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5075_);
return v___x_5082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5087_, v___y_5088_);
lean_dec(v___y_5088_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5091_, v___y_5097_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5109_, lean_object* v___y_5110_){
_start:
{
uint8_t v___x_5112_; 
v___x_5112_ = l_Lean_Expr_hasMVar(v_e_5109_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5113_, 0, v_e_5109_);
return v___x_5113_;
}
else
{
lean_object* v___x_5114_; lean_object* v_mctx_5115_; lean_object* v___x_5116_; lean_object* v_fst_5117_; lean_object* v_snd_5118_; lean_object* v___x_5119_; lean_object* v_cache_5120_; lean_object* v_zetaDeltaFVarIds_5121_; lean_object* v_postponed_5122_; lean_object* v_diag_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5132_; 
v___x_5114_ = lean_st_ref_get(v___y_5110_);
v_mctx_5115_ = lean_ctor_get(v___x_5114_, 0);
lean_inc_ref(v_mctx_5115_);
lean_dec(v___x_5114_);
v___x_5116_ = l_Lean_instantiateMVarsCore(v_mctx_5115_, v_e_5109_);
v_fst_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_fst_5117_);
v_snd_5118_ = lean_ctor_get(v___x_5116_, 1);
lean_inc(v_snd_5118_);
lean_dec_ref(v___x_5116_);
v___x_5119_ = lean_st_ref_take(v___y_5110_);
v_cache_5120_ = lean_ctor_get(v___x_5119_, 1);
v_zetaDeltaFVarIds_5121_ = lean_ctor_get(v___x_5119_, 2);
v_postponed_5122_ = lean_ctor_get(v___x_5119_, 3);
v_diag_5123_ = lean_ctor_get(v___x_5119_, 4);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5132_ == 0)
{
lean_object* v_unused_5133_; 
v_unused_5133_ = lean_ctor_get(v___x_5119_, 0);
lean_dec(v_unused_5133_);
v___x_5125_ = v___x_5119_;
v_isShared_5126_ = v_isSharedCheck_5132_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_diag_5123_);
lean_inc(v_postponed_5122_);
lean_inc(v_zetaDeltaFVarIds_5121_);
lean_inc(v_cache_5120_);
lean_dec(v___x_5119_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5132_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v_snd_5118_);
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_snd_5118_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v_cache_5120_);
lean_ctor_set(v_reuseFailAlloc_5131_, 2, v_zetaDeltaFVarIds_5121_);
lean_ctor_set(v_reuseFailAlloc_5131_, 3, v_postponed_5122_);
lean_ctor_set(v_reuseFailAlloc_5131_, 4, v_diag_5123_);
v___x_5128_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = lean_st_ref_put(v___y_5110_, v___x_5128_);
v___x_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5130_, 0, v_fst_5117_);
return v___x_5130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5134_, v___y_5135_);
lean_dec(v___y_5135_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5138_, v___y_5140_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v___y_5147_);
lean_dec_ref(v___y_5146_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5152_, size_t v_i_5153_, size_t v_stop_5154_, lean_object* v_b_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
uint8_t v___x_5163_; 
v___x_5163_ = lean_usize_dec_eq(v_i_5153_, v_stop_5154_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5164_ = lean_array_uget_borrowed(v_as_5152_, v_i_5153_);
lean_inc(v___x_5164_);
v___x_5165_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5165_, 0, v___x_5164_);
v___x_5166_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5165_, v___y_5161_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; size_t v___x_5168_; size_t v___x_5169_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v___x_5168_ = ((size_t)1ULL);
v___x_5169_ = lean_usize_add(v_i_5153_, v___x_5168_);
v_i_5153_ = v___x_5169_;
v_b_5155_ = v_a_5167_;
goto _start;
}
else
{
return v___x_5166_;
}
}
else
{
lean_object* v___x_5171_; 
v___x_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5171_, 0, v_b_5155_);
return v___x_5171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5172_, lean_object* v_i_5173_, lean_object* v_stop_5174_, lean_object* v_b_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_){
_start:
{
size_t v_i_boxed_5183_; size_t v_stop_boxed_5184_; lean_object* v_res_5185_; 
v_i_boxed_5183_ = lean_unbox_usize(v_i_5173_);
lean_dec(v_i_5173_);
v_stop_boxed_5184_ = lean_unbox_usize(v_stop_5174_);
lean_dec(v_stop_5174_);
v_res_5185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5172_, v_i_boxed_5183_, v_stop_boxed_5184_, v_b_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v_as_5172_);
return v_res_5185_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5186_ = lean_unsigned_to_nat(32u);
v___x_5187_ = lean_mk_empty_array_with_capacity(v___x_5186_);
v___x_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5187_);
return v___x_5188_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5189_ = ((size_t)5ULL);
v___x_5190_ = lean_unsigned_to_nat(0u);
v___x_5191_ = lean_unsigned_to_nat(32u);
v___x_5192_ = lean_mk_empty_array_with_capacity(v___x_5191_);
v___x_5193_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5194_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
lean_ctor_set(v___x_5194_, 1, v___x_5192_);
lean_ctor_set(v___x_5194_, 2, v___x_5190_);
lean_ctor_set(v___x_5194_, 3, v___x_5190_);
lean_ctor_set_usize(v___x_5194_, 4, v___x_5189_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5195_){
_start:
{
lean_object* v___x_5197_; lean_object* v_infoState_5198_; lean_object* v_trees_5199_; lean_object* v___x_5200_; lean_object* v_infoState_5201_; lean_object* v_env_5202_; lean_object* v_nextMacroScope_5203_; lean_object* v_ngen_5204_; lean_object* v_auxDeclNGen_5205_; lean_object* v_traceState_5206_; lean_object* v_cache_5207_; lean_object* v_recordedDeps_5208_; lean_object* v_messages_5209_; lean_object* v_snapshotTasks_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5231_; 
v___x_5197_ = lean_st_ref_get(v___y_5195_);
v_infoState_5198_ = lean_ctor_get(v___x_5197_, 8);
lean_inc_ref(v_infoState_5198_);
lean_dec(v___x_5197_);
v_trees_5199_ = lean_ctor_get(v_infoState_5198_, 2);
lean_inc_ref(v_trees_5199_);
lean_dec_ref(v_infoState_5198_);
v___x_5200_ = lean_st_ref_take(v___y_5195_);
v_infoState_5201_ = lean_ctor_get(v___x_5200_, 8);
v_env_5202_ = lean_ctor_get(v___x_5200_, 0);
v_nextMacroScope_5203_ = lean_ctor_get(v___x_5200_, 1);
v_ngen_5204_ = lean_ctor_get(v___x_5200_, 2);
v_auxDeclNGen_5205_ = lean_ctor_get(v___x_5200_, 3);
v_traceState_5206_ = lean_ctor_get(v___x_5200_, 4);
v_cache_5207_ = lean_ctor_get(v___x_5200_, 5);
v_recordedDeps_5208_ = lean_ctor_get(v___x_5200_, 6);
v_messages_5209_ = lean_ctor_get(v___x_5200_, 7);
v_snapshotTasks_5210_ = lean_ctor_get(v___x_5200_, 9);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5212_ = v___x_5200_;
v_isShared_5213_ = v_isSharedCheck_5231_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_snapshotTasks_5210_);
lean_inc(v_infoState_5201_);
lean_inc(v_messages_5209_);
lean_inc(v_recordedDeps_5208_);
lean_inc(v_cache_5207_);
lean_inc(v_traceState_5206_);
lean_inc(v_auxDeclNGen_5205_);
lean_inc(v_ngen_5204_);
lean_inc(v_nextMacroScope_5203_);
lean_inc(v_env_5202_);
lean_dec(v___x_5200_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5231_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
uint8_t v_enabled_5214_; lean_object* v_assignment_5215_; lean_object* v_lazyAssignment_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5229_; 
v_enabled_5214_ = lean_ctor_get_uint8(v_infoState_5201_, sizeof(void*)*3);
v_assignment_5215_ = lean_ctor_get(v_infoState_5201_, 0);
v_lazyAssignment_5216_ = lean_ctor_get(v_infoState_5201_, 1);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_infoState_5201_);
if (v_isSharedCheck_5229_ == 0)
{
lean_object* v_unused_5230_; 
v_unused_5230_ = lean_ctor_get(v_infoState_5201_, 2);
lean_dec(v_unused_5230_);
v___x_5218_ = v_infoState_5201_;
v_isShared_5219_ = v_isSharedCheck_5229_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_lazyAssignment_5216_);
lean_inc(v_assignment_5215_);
lean_dec(v_infoState_5201_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5229_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5220_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 2, v___x_5220_);
v___x_5222_ = v___x_5218_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_assignment_5215_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v_lazyAssignment_5216_);
lean_ctor_set(v_reuseFailAlloc_5228_, 2, v___x_5220_);
lean_ctor_set_uint8(v_reuseFailAlloc_5228_, sizeof(void*)*3, v_enabled_5214_);
v___x_5222_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5224_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 8, v___x_5222_);
v___x_5224_ = v___x_5212_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_env_5202_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v_nextMacroScope_5203_);
lean_ctor_set(v_reuseFailAlloc_5227_, 2, v_ngen_5204_);
lean_ctor_set(v_reuseFailAlloc_5227_, 3, v_auxDeclNGen_5205_);
lean_ctor_set(v_reuseFailAlloc_5227_, 4, v_traceState_5206_);
lean_ctor_set(v_reuseFailAlloc_5227_, 5, v_cache_5207_);
lean_ctor_set(v_reuseFailAlloc_5227_, 6, v_recordedDeps_5208_);
lean_ctor_set(v_reuseFailAlloc_5227_, 7, v_messages_5209_);
lean_ctor_set(v_reuseFailAlloc_5227_, 8, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5227_, 9, v_snapshotTasks_5210_);
v___x_5224_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = lean_st_ref_put(v___y_5195_, v___x_5224_);
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_trees_5199_);
return v___x_5226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5232_);
lean_dec(v___y_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5235_, lean_object* v_mkInfoTree_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v_a_5244_, lean_object* v_a_x3f_5245_){
_start:
{
lean_object* v___x_5247_; lean_object* v_infoState_5248_; lean_object* v_trees_5249_; lean_object* v___x_5250_; 
v___x_5247_ = lean_st_ref_get(v___y_5235_);
v_infoState_5248_ = lean_ctor_get(v___x_5247_, 8);
lean_inc_ref(v_infoState_5248_);
lean_dec(v___x_5247_);
v_trees_5249_ = lean_ctor_get(v_infoState_5248_, 2);
lean_inc_ref(v_trees_5249_);
lean_dec_ref(v_infoState_5248_);
lean_inc(v___y_5235_);
lean_inc_ref(v___y_5243_);
lean_inc(v___y_5242_);
lean_inc_ref(v___y_5241_);
lean_inc(v___y_5240_);
lean_inc_ref(v___y_5239_);
lean_inc(v___y_5238_);
lean_inc_ref(v___y_5237_);
v___x_5250_ = lean_apply_10(v_mkInfoTree_5236_, v_trees_5249_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5235_, lean_box(0));
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5290_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5253_ = v___x_5250_;
v_isShared_5254_ = v_isSharedCheck_5290_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5250_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5290_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5255_; lean_object* v_infoState_5256_; lean_object* v_env_5257_; lean_object* v_nextMacroScope_5258_; lean_object* v_ngen_5259_; lean_object* v_auxDeclNGen_5260_; lean_object* v_traceState_5261_; lean_object* v_cache_5262_; lean_object* v_recordedDeps_5263_; lean_object* v_messages_5264_; lean_object* v_snapshotTasks_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5289_; 
v___x_5255_ = lean_st_ref_take(v___y_5235_);
v_infoState_5256_ = lean_ctor_get(v___x_5255_, 8);
v_env_5257_ = lean_ctor_get(v___x_5255_, 0);
v_nextMacroScope_5258_ = lean_ctor_get(v___x_5255_, 1);
v_ngen_5259_ = lean_ctor_get(v___x_5255_, 2);
v_auxDeclNGen_5260_ = lean_ctor_get(v___x_5255_, 3);
v_traceState_5261_ = lean_ctor_get(v___x_5255_, 4);
v_cache_5262_ = lean_ctor_get(v___x_5255_, 5);
v_recordedDeps_5263_ = lean_ctor_get(v___x_5255_, 6);
v_messages_5264_ = lean_ctor_get(v___x_5255_, 7);
v_snapshotTasks_5265_ = lean_ctor_get(v___x_5255_, 9);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5267_ = v___x_5255_;
v_isShared_5268_ = v_isSharedCheck_5289_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_snapshotTasks_5265_);
lean_inc(v_infoState_5256_);
lean_inc(v_messages_5264_);
lean_inc(v_recordedDeps_5263_);
lean_inc(v_cache_5262_);
lean_inc(v_traceState_5261_);
lean_inc(v_auxDeclNGen_5260_);
lean_inc(v_ngen_5259_);
lean_inc(v_nextMacroScope_5258_);
lean_inc(v_env_5257_);
lean_dec(v___x_5255_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5289_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
uint8_t v_enabled_5269_; lean_object* v_assignment_5270_; lean_object* v_lazyAssignment_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5287_; 
v_enabled_5269_ = lean_ctor_get_uint8(v_infoState_5256_, sizeof(void*)*3);
v_assignment_5270_ = lean_ctor_get(v_infoState_5256_, 0);
v_lazyAssignment_5271_ = lean_ctor_get(v_infoState_5256_, 1);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_infoState_5256_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v_infoState_5256_, 2);
lean_dec(v_unused_5288_);
v___x_5273_ = v_infoState_5256_;
v_isShared_5274_ = v_isSharedCheck_5287_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_lazyAssignment_5271_);
lean_inc(v_assignment_5270_);
lean_dec(v_infoState_5256_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5287_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; 
v___x_5275_ = lean_box(0);
v___x_5276_ = l_Lean_PersistentArray_push___redArg(v_a_5244_, v_a_5251_);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 2, v___x_5276_);
v___x_5278_ = v___x_5273_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_assignment_5270_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_lazyAssignment_5271_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v___x_5276_);
lean_ctor_set_uint8(v_reuseFailAlloc_5286_, sizeof(void*)*3, v_enabled_5269_);
v___x_5278_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
lean_object* v___x_5280_; 
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 8, v___x_5278_);
v___x_5280_ = v___x_5267_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_env_5257_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v_nextMacroScope_5258_);
lean_ctor_set(v_reuseFailAlloc_5285_, 2, v_ngen_5259_);
lean_ctor_set(v_reuseFailAlloc_5285_, 3, v_auxDeclNGen_5260_);
lean_ctor_set(v_reuseFailAlloc_5285_, 4, v_traceState_5261_);
lean_ctor_set(v_reuseFailAlloc_5285_, 5, v_cache_5262_);
lean_ctor_set(v_reuseFailAlloc_5285_, 6, v_recordedDeps_5263_);
lean_ctor_set(v_reuseFailAlloc_5285_, 7, v_messages_5264_);
lean_ctor_set(v_reuseFailAlloc_5285_, 8, v___x_5278_);
lean_ctor_set(v_reuseFailAlloc_5285_, 9, v_snapshotTasks_5265_);
v___x_5280_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5281_ = lean_st_ref_put(v___y_5235_, v___x_5280_);
if (v_isShared_5254_ == 0)
{
lean_ctor_set(v___x_5253_, 0, v___x_5275_);
v___x_5283_ = v___x_5253_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5275_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
lean_dec_ref(v_a_5244_);
v_a_5291_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5250_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5250_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5299_, lean_object* v_mkInfoTree_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v_a_5308_, lean_object* v_a_x3f_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5299_, v_mkInfoTree_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v_a_5308_, v_a_x3f_5309_);
lean_dec(v_a_x3f_5309_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5299_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5312_, lean_object* v_mkInfoTree_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v___x_5323_; lean_object* v_infoState_5324_; uint8_t v_enabled_5325_; 
v___x_5323_ = lean_st_ref_get(v___y_5321_);
v_infoState_5324_ = lean_ctor_get(v___x_5323_, 8);
lean_inc_ref(v_infoState_5324_);
lean_dec(v___x_5323_);
v_enabled_5325_ = lean_ctor_get_uint8(v_infoState_5324_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5324_);
if (v_enabled_5325_ == 0)
{
lean_object* v___x_5326_; 
lean_dec_ref(v_mkInfoTree_5313_);
lean_inc(v___y_5321_);
lean_inc_ref(v___y_5320_);
lean_inc(v___y_5319_);
lean_inc_ref(v___y_5318_);
lean_inc(v___y_5317_);
lean_inc_ref(v___y_5316_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
v___x_5326_ = lean_apply_9(v_x_5312_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, lean_box(0));
return v___x_5326_;
}
else
{
lean_object* v___x_5327_; lean_object* v_a_5328_; lean_object* v_r_5329_; 
v___x_5327_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5321_);
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc(v_a_5328_);
lean_dec_ref(v___x_5327_);
lean_inc(v___y_5321_);
lean_inc_ref(v___y_5320_);
lean_inc(v___y_5319_);
lean_inc_ref(v___y_5318_);
lean_inc(v___y_5317_);
lean_inc_ref(v___y_5316_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
v_r_5329_ = lean_apply_9(v_x_5312_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, lean_box(0));
if (lean_obj_tag(v_r_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5354_; 
v_a_5330_ = lean_ctor_get(v_r_5329_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_r_5329_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5332_ = v_r_5329_;
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v_r_5329_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
lean_inc(v_a_5330_);
if (v_isShared_5333_ == 0)
{
lean_ctor_set_tag(v___x_5332_, 1);
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5336_; 
v___x_5336_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5321_, v_mkInfoTree_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v_a_5328_, v___x_5335_);
lean_dec_ref(v___x_5335_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5343_ == 0)
{
lean_object* v_unused_5344_; 
v_unused_5344_ = lean_ctor_get(v___x_5336_, 0);
lean_dec(v_unused_5344_);
v___x_5338_ = v___x_5336_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_dec(v___x_5336_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v_a_5330_);
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5330_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
else
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
lean_dec(v_a_5330_);
v_a_5345_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5336_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5336_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v_a_5355_ = lean_ctor_get(v_r_5329_, 0);
lean_inc(v_a_5355_);
lean_dec_ref_known(v_r_5329_, 1);
v___x_5356_ = lean_box(0);
v___x_5357_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5321_, v_mkInfoTree_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v_a_5328_, v___x_5356_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; 
v_unused_5365_ = lean_ctor_get(v___x_5357_, 0);
lean_dec(v_unused_5365_);
v___x_5359_ = v___x_5357_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_dec(v___x_5357_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
lean_ctor_set_tag(v___x_5359_, 1);
lean_ctor_set(v___x_5359_, 0, v_a_5355_);
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5355_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
else
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
lean_dec(v_a_5355_);
v_a_5366_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5357_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5357_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5374_, lean_object* v_mkInfoTree_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5374_, v_mkInfoTree_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5386_, lean_object* v_trees_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v___x_5397_; 
lean_inc(v___y_5395_);
lean_inc_ref(v___y_5394_);
lean_inc(v___y_5393_);
lean_inc_ref(v___y_5392_);
lean_inc(v___y_5391_);
lean_inc_ref(v___y_5390_);
lean_inc(v___y_5389_);
lean_inc_ref(v___y_5388_);
v___x_5397_ = lean_apply_9(v_a_5386_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, lean_box(0));
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5406_; 
v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5400_ = v___x_5397_;
v_isShared_5401_ = v_isSharedCheck_5406_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5397_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5406_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5402_; lean_object* v___x_5404_; 
v___x_5402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5402_, 0, v_a_5398_);
lean_ctor_set(v___x_5402_, 1, v_trees_5387_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5402_);
v___x_5404_ = v___x_5400_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
lean_dec_ref(v_trees_5387_);
v_a_5407_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5397_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5397_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5415_, lean_object* v_trees_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5415_, v_trees_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5427_, lean_object* v_tactic_5428_, lean_object* v_ref_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5427_, v___y_5431_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v___x_5440_; 
lean_dec_ref_known(v___x_5439_, 1);
v___x_5440_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec_ref_known(v___x_5440_, 1);
v___x_5441_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5441_, 0, v_tactic_5428_);
v___x_5442_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___f_5444_; lean_object* v___x_5445_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v___f_5444_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5444_, 0, v_a_5443_);
v___x_5445_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5441_, v___f_5444_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
return v___x_5445_;
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec_ref(v___x_5441_);
v_a_5446_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5442_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5442_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
else
{
lean_dec(v_ref_5429_);
lean_dec(v_tactic_5428_);
return v___x_5440_;
}
}
else
{
lean_dec(v_ref_5429_);
lean_dec(v_tactic_5428_);
return v___x_5439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5454_, lean_object* v_tactic_5455_, lean_object* v_ref_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5454_, v_tactic_5455_, v_ref_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
return v_res_5466_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5467_ = lean_box(1);
v___x_5468_ = l_Lean_MessageData_ofFormat(v___x_5467_);
return v___x_5468_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; 
v___x_5472_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5473_ = l_Lean_MessageData_ofFormat(v___x_5472_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5474_, lean_object* v_x_5475_){
_start:
{
if (lean_obj_tag(v_x_5475_) == 0)
{
return v_x_5474_;
}
else
{
lean_object* v_head_5476_; lean_object* v_tail_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5499_; 
v_head_5476_ = lean_ctor_get(v_x_5475_, 0);
v_tail_5477_ = lean_ctor_get(v_x_5475_, 1);
v_isSharedCheck_5499_ = !lean_is_exclusive(v_x_5475_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5479_ = v_x_5475_;
v_isShared_5480_ = v_isSharedCheck_5499_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_tail_5477_);
lean_inc(v_head_5476_);
lean_dec(v_x_5475_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5499_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v_before_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5497_; 
v_before_5481_ = lean_ctor_get(v_head_5476_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v_head_5476_);
if (v_isSharedCheck_5497_ == 0)
{
lean_object* v_unused_5498_; 
v_unused_5498_ = lean_ctor_get(v_head_5476_, 1);
lean_dec(v_unused_5498_);
v___x_5483_ = v_head_5476_;
v_isShared_5484_ = v_isSharedCheck_5497_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_before_5481_);
lean_dec(v_head_5476_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5497_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5485_; lean_object* v___x_5487_; 
v___x_5485_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5484_ == 0)
{
lean_ctor_set_tag(v___x_5483_, 7);
lean_ctor_set(v___x_5483_, 1, v___x_5485_);
lean_ctor_set(v___x_5483_, 0, v_x_5474_);
v___x_5487_ = v___x_5483_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_x_5474_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v___x_5485_);
v___x_5487_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5488_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5480_ == 0)
{
lean_ctor_set_tag(v___x_5479_, 7);
lean_ctor_set(v___x_5479_, 1, v___x_5488_);
lean_ctor_set(v___x_5479_, 0, v___x_5487_);
v___x_5490_ = v___x_5479_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5487_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5491_ = l_Lean_MessageData_ofSyntax(v_before_5481_);
v___x_5492_ = l_Lean_indentD(v___x_5491_);
v___x_5493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5490_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
v_x_5474_ = v___x_5493_;
v_x_5475_ = v_tail_5477_;
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
lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5503_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5504_ = l_Lean_MessageData_ofFormat(v___x_5503_);
return v___x_5504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5505_, lean_object* v_macroStack_5506_, lean_object* v___y_5507_){
_start:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; uint8_t v___x_5511_; 
v___x_5509_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5507_);
v___x_5510_ = l_Lean_Elab_pp_macroStack;
v___x_5511_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_5509_, v___x_5510_);
lean_dec_ref(v___x_5509_);
if (v___x_5511_ == 0)
{
lean_object* v___x_5512_; 
lean_dec(v_macroStack_5506_);
v___x_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5512_, 0, v_msgData_5505_);
return v___x_5512_;
}
else
{
if (lean_obj_tag(v_macroStack_5506_) == 0)
{
lean_object* v___x_5513_; 
v___x_5513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5513_, 0, v_msgData_5505_);
return v___x_5513_;
}
else
{
lean_object* v_head_5514_; lean_object* v_after_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5530_; 
v_head_5514_ = lean_ctor_get(v_macroStack_5506_, 0);
lean_inc(v_head_5514_);
v_after_5515_ = lean_ctor_get(v_head_5514_, 1);
v_isSharedCheck_5530_ = !lean_is_exclusive(v_head_5514_);
if (v_isSharedCheck_5530_ == 0)
{
lean_object* v_unused_5531_; 
v_unused_5531_ = lean_ctor_get(v_head_5514_, 0);
lean_dec(v_unused_5531_);
v___x_5517_ = v_head_5514_;
v_isShared_5518_ = v_isSharedCheck_5530_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_after_5515_);
lean_dec(v_head_5514_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5530_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5521_; 
v___x_5519_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5518_ == 0)
{
lean_ctor_set_tag(v___x_5517_, 7);
lean_ctor_set(v___x_5517_, 1, v___x_5519_);
lean_ctor_set(v___x_5517_, 0, v_msgData_5505_);
v___x_5521_ = v___x_5517_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_msgData_5505_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v___x_5519_);
v___x_5521_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v_msgData_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5522_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5521_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
v___x_5524_ = l_Lean_MessageData_ofSyntax(v_after_5515_);
v___x_5525_ = l_Lean_indentD(v___x_5524_);
v_msgData_5526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5526_, 0, v___x_5523_);
lean_ctor_set(v_msgData_5526_, 1, v___x_5525_);
v___x_5527_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5526_, v_macroStack_5506_);
v___x_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5527_);
return v___x_5528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5532_, lean_object* v_macroStack_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_){
_start:
{
lean_object* v_res_5536_; 
v_res_5536_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5532_, v_macroStack_5533_, v___y_5534_);
lean_dec_ref(v___y_5534_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
lean_object* v_ref_5545_; lean_object* v_macroStack_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v_a_5549_; lean_object* v___x_5550_; lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5559_; 
v_ref_5545_ = lean_ctor_get(v___y_5542_, 2);
v_macroStack_5546_ = lean_ctor_get(v___y_5538_, 1);
v___x_5547_ = l_Lean_Elab_getBetterRef(v_ref_5545_, v_macroStack_5546_);
v___x_5548_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5537_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_);
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
lean_dec_ref(v___x_5548_);
lean_inc(v_macroStack_5546_);
v___x_5550_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5549_, v_macroStack_5546_, v___y_5542_);
v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5550_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5553_ = v___x_5550_;
v_isShared_5554_ = v_isSharedCheck_5559_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5550_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5559_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5555_; lean_object* v___x_5557_; 
v___x_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5547_);
lean_ctor_set(v___x_5555_, 1, v_a_5551_);
if (v_isShared_5554_ == 0)
{
lean_ctor_set_tag(v___x_5553_, 1);
lean_ctor_set(v___x_5553_, 0, v___x_5555_);
v___x_5557_ = v___x_5553_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
lean_dec(v___y_5566_);
lean_dec_ref(v___y_5565_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
return v_res_5568_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5571_ = l_Lean_stringToMessageData(v___x_5570_);
return v___x_5571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5572_, size_t v_sz_5573_, size_t v_i_5574_, lean_object* v_b_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_a_5584_; uint8_t v___x_5588_; 
v___x_5588_ = lean_usize_dec_lt(v_i_5574_, v_sz_5573_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; 
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v_b_5575_);
return v___x_5589_;
}
else
{
lean_object* v___x_5590_; lean_object* v_a_5591_; lean_object* v___x_5592_; 
v___x_5590_ = lean_box(0);
v_a_5591_ = lean_array_uget_borrowed(v_as_5572_, v_i_5574_);
lean_inc(v_a_5591_);
v___x_5592_ = l_Lean_MVarId_getType(v_a_5591_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5594_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref_known(v___x_5592_, 1);
lean_inc(v_a_5591_);
v___x_5594_ = l_Lean_MVarId_getType(v_a_5591_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v___x_5596_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___x_5594_, 1);
v___x_5596_ = l_Lean_getRecAppSyntax_x3f(v_a_5595_);
lean_dec(v_a_5595_);
if (lean_obj_tag(v___x_5596_) == 1)
{
lean_object* v_val_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v_val_5597_ = lean_ctor_get(v___x_5596_, 0);
lean_inc(v_val_5597_);
lean_dec_ref_known(v___x_5596_, 1);
v___x_5598_ = l_Lean_Expr_mdataExpr_x21(v_a_5593_);
lean_dec(v_a_5593_);
lean_inc(v_a_5591_);
v___x_5599_ = l_Lean_MVarId_setType___redArg(v_a_5591_, v___x_5598_, v___y_5579_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_toCold_5600_; lean_object* v_currRecDepth_5601_; lean_object* v_ref_5602_; uint16_t v_optionFlags_5603_; uint8_t v_suppressElabErrors_5604_; uint8_t v_isRecordingDeps_5605_; lean_object* v_ref_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
lean_dec_ref_known(v___x_5599_, 1);
v_toCold_5600_ = lean_ctor_get(v___y_5580_, 0);
v_currRecDepth_5601_ = lean_ctor_get(v___y_5580_, 1);
v_ref_5602_ = lean_ctor_get(v___y_5580_, 2);
v_optionFlags_5603_ = lean_ctor_get_uint16(v___y_5580_, sizeof(void*)*3);
v_suppressElabErrors_5604_ = lean_ctor_get_uint8(v___y_5580_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5605_ = lean_ctor_get_uint8(v___y_5580_, sizeof(void*)*3 + 3);
v_ref_5606_ = l_Lean_replaceRef(v_val_5597_, v_ref_5602_);
lean_dec(v_val_5597_);
lean_inc(v_currRecDepth_5601_);
lean_inc_ref(v_toCold_5600_);
v___x_5607_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5607_, 0, v_toCold_5600_);
lean_ctor_set(v___x_5607_, 1, v_currRecDepth_5601_);
lean_ctor_set(v___x_5607_, 2, v_ref_5606_);
lean_ctor_set_uint16(v___x_5607_, sizeof(void*)*3, v_optionFlags_5603_);
lean_ctor_set_uint8(v___x_5607_, sizeof(void*)*3 + 2, v_suppressElabErrors_5604_);
lean_ctor_set_uint8(v___x_5607_, sizeof(void*)*3 + 3, v_isRecordingDeps_5605_);
lean_inc(v_a_5591_);
v___x_5608_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5591_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___x_5607_, v___y_5581_);
lean_dec_ref_known(v___x_5607_, 3);
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_dec_ref_known(v___x_5608_, 1);
v_a_5584_ = v___x_5590_;
goto v___jp_5583_;
}
else
{
return v___x_5608_;
}
}
else
{
lean_dec(v_val_5597_);
return v___x_5599_;
}
}
else
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
lean_dec(v___x_5596_);
v___x_5609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5610_ = l_Lean_indentExpr(v_a_5593_);
v___x_5611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5609_);
lean_ctor_set(v___x_5611_, 1, v___x_5610_);
v___x_5612_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5611_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_dec_ref_known(v___x_5612_, 1);
v_a_5584_ = v___x_5590_;
goto v___jp_5583_;
}
else
{
return v___x_5612_;
}
}
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_a_5593_);
v_a_5613_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5594_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5594_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
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
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
v_a_5621_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5592_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5592_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
v___jp_5583_:
{
size_t v___x_5585_; size_t v___x_5586_; 
v___x_5585_ = ((size_t)1ULL);
v___x_5586_ = lean_usize_add(v_i_5574_, v___x_5585_);
v_i_5574_ = v___x_5586_;
v_b_5575_ = v_a_5584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5629_, lean_object* v_sz_5630_, lean_object* v_i_5631_, lean_object* v_b_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
size_t v_sz_boxed_5640_; size_t v_i_boxed_5641_; lean_object* v_res_5642_; 
v_sz_boxed_5640_ = lean_unbox_usize(v_sz_5630_);
lean_dec(v_sz_5630_);
v_i_boxed_5641_ = lean_unbox_usize(v_i_5631_);
lean_dec(v_i_5631_);
v_res_5642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5629_, v_sz_boxed_5640_, v_i_boxed_5641_, v_b_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
lean_dec_ref(v_as_5629_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5643_, size_t v_i_5644_, size_t v_stop_5645_, lean_object* v_b_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
uint8_t v___x_5652_; 
v___x_5652_ = lean_usize_dec_eq(v_i_5644_, v_stop_5645_);
if (v___x_5652_ == 0)
{
lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5653_ = lean_array_uget_borrowed(v_as_5643_, v_i_5644_);
lean_inc(v___x_5653_);
v___x_5654_ = l_Lean_MVarId_getType(v___x_5653_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref_known(v___x_5654_, 1);
v___x_5656_ = l_Lean_Expr_mdataExpr_x21(v_a_5655_);
lean_dec(v_a_5655_);
lean_inc(v___x_5653_);
v___x_5657_ = l_Lean_MVarId_setType___redArg(v___x_5653_, v___x_5656_, v___y_5648_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v_a_5658_; size_t v___x_5659_; size_t v___x_5660_; 
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_a_5658_);
lean_dec_ref_known(v___x_5657_, 1);
v___x_5659_ = ((size_t)1ULL);
v___x_5660_ = lean_usize_add(v_i_5644_, v___x_5659_);
v_i_5644_ = v___x_5660_;
v_b_5646_ = v_a_5658_;
goto _start;
}
else
{
return v___x_5657_;
}
}
else
{
lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5669_; 
v_a_5662_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5664_ = v___x_5654_;
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_dec(v___x_5654_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5667_; 
if (v_isShared_5665_ == 0)
{
v___x_5667_ = v___x_5664_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
else
{
lean_object* v___x_5670_; 
v___x_5670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5670_, 0, v_b_5646_);
return v___x_5670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5671_, lean_object* v_i_5672_, lean_object* v_stop_5673_, lean_object* v_b_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
size_t v_i_boxed_5680_; size_t v_stop_boxed_5681_; lean_object* v_res_5682_; 
v_i_boxed_5680_ = lean_unbox_usize(v_i_5672_);
lean_dec(v_i_5672_);
v_stop_boxed_5681_ = lean_unbox_usize(v_stop_5673_);
lean_dec(v_stop_5673_);
v_res_5682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5671_, v_i_boxed_5680_, v_stop_boxed_5681_, v_b_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec_ref(v_as_5671_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5683_, lean_object* v___x_5684_, lean_object* v___x_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_object* v___x_5693_; size_t v_sz_5694_; size_t v___x_5695_; lean_object* v___x_5696_; 
v___x_5693_ = lean_box(0);
v_sz_5694_ = lean_array_size(v___x_5684_);
v___x_5695_ = ((size_t)0ULL);
v___x_5696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5684_, v_sz_5694_, v___x_5695_, v___x_5693_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec_ref(v___x_5684_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; 
v_unused_5704_ = lean_ctor_get(v___x_5696_, 0);
lean_dec(v_unused_5704_);
v___x_5698_ = v___x_5696_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_dec(v___x_5696_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 0, v___x_5693_);
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5693_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
else
{
return v___x_5696_;
}
}
else
{
lean_object* v_val_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5773_; 
v_val_5705_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5707_ = v___x_5683_;
v_isShared_5708_ = v_isSharedCheck_5773_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_val_5705_);
lean_dec(v___x_5683_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5773_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
lean_object* v_ref_5709_; lean_object* v_tactic_5710_; lean_object* v_toCold_5711_; lean_object* v_currRecDepth_5712_; lean_object* v_ref_5713_; uint16_t v_optionFlags_5714_; uint8_t v_suppressElabErrors_5715_; uint8_t v_isRecordingDeps_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v_ref_5719_; lean_object* v___x_5720_; lean_object* v___y_5746_; lean_object* v___y_5763_; uint8_t v___x_5764_; 
v_ref_5709_ = lean_ctor_get(v_val_5705_, 0);
lean_inc(v_ref_5709_);
v_tactic_5710_ = lean_ctor_get(v_val_5705_, 1);
lean_inc(v_tactic_5710_);
lean_dec(v_val_5705_);
v_toCold_5711_ = lean_ctor_get(v___y_5690_, 0);
v_currRecDepth_5712_ = lean_ctor_get(v___y_5690_, 1);
v_ref_5713_ = lean_ctor_get(v___y_5690_, 2);
v_optionFlags_5714_ = lean_ctor_get_uint16(v___y_5690_, sizeof(void*)*3);
v_suppressElabErrors_5715_ = lean_ctor_get_uint8(v___y_5690_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5716_ = lean_ctor_get_uint8(v___y_5690_, sizeof(void*)*3 + 3);
v___x_5717_ = lean_unsigned_to_nat(0u);
v___x_5718_ = lean_array_get_size(v___x_5684_);
v_ref_5719_ = l_Lean_replaceRef(v_ref_5709_, v_ref_5713_);
lean_inc(v_currRecDepth_5712_);
lean_inc_ref(v_toCold_5711_);
v___x_5720_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5720_, 0, v_toCold_5711_);
lean_ctor_set(v___x_5720_, 1, v_currRecDepth_5712_);
lean_ctor_set(v___x_5720_, 2, v_ref_5719_);
lean_ctor_set_uint16(v___x_5720_, sizeof(void*)*3, v_optionFlags_5714_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*3 + 2, v_suppressElabErrors_5715_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*3 + 3, v_isRecordingDeps_5716_);
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
v___x_5769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5684_, v___x_5767_, v___x_5768_, v___x_5765_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
v___y_5763_ = v___x_5769_;
goto v___jp_5762_;
}
}
else
{
size_t v___x_5770_; size_t v___x_5771_; lean_object* v___x_5772_; 
v___x_5770_ = ((size_t)0ULL);
v___x_5771_ = lean_usize_of_nat(v___x_5718_);
v___x_5772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5684_, v___x_5770_, v___x_5771_, v___x_5765_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
v___y_5763_ = v___x_5772_;
goto v___jp_5762_;
}
}
v___jp_5721_:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___f_5724_; lean_object* v___x_5725_; 
v___x_5722_ = lean_array_get(v___x_5685_, v___x_5684_, v___x_5717_);
v___x_5723_ = lean_array_to_list(v___x_5684_);
v___f_5724_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5724_, 0, v___x_5723_);
lean_closure_set(v___f_5724_, 1, v_tactic_5710_);
lean_closure_set(v___f_5724_, 2, v_ref_5709_);
v___x_5725_ = l_Lean_Elab_Tactic_run(v___x_5722_, v___f_5724_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
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
v___x_5731_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5726_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
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
lean_dec(v_tactic_5710_);
lean_dec(v_ref_5709_);
lean_dec_ref(v___x_5684_);
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
lean_del_object(v___x_5707_);
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
v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5684_, v___x_5752_, v___x_5753_, v___x_5750_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
v___y_5746_ = v___x_5754_;
goto v___jp_5745_;
}
}
else
{
size_t v___x_5755_; size_t v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = ((size_t)0ULL);
v___x_5756_ = lean_usize_of_nat(v___x_5718_);
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5684_, v___x_5755_, v___x_5756_, v___x_5750_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___x_5720_, v___y_5691_);
v___y_5746_ = v___x_5757_;
goto v___jp_5745_;
}
}
}
else
{
lean_object* v___x_5758_; lean_object* v___x_5760_; 
lean_dec_ref_known(v___x_5720_, 3);
lean_dec(v_tactic_5710_);
lean_dec(v_ref_5709_);
lean_dec_ref(v___x_5684_);
v___x_5758_ = lean_box(0);
if (v_isShared_5708_ == 0)
{
lean_ctor_set_tag(v___x_5707_, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5758_);
v___x_5760_ = v___x_5707_;
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
lean_dec(v_tactic_5710_);
lean_dec(v_ref_5709_);
lean_del_object(v___x_5707_);
lean_dec_ref(v___x_5684_);
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
lean_object* v___f_5839_; lean_object* v___x_5840_; lean_object* v_a_5841_; lean_object* v___x_5842_; lean_object* v___y_5843_; lean_object* v___x_5844_; lean_object* v___x_5846_; 
v___f_5839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5840_ = lean_box(0);
v_a_5841_ = lean_array_uget_borrowed(v_as_5796_, v_i_5798_);
v___x_5842_ = lean_array_fget_borrowed(v_array_5823_, v_start_5824_);
lean_inc(v___x_5842_);
v___y_5843_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5843_, 0, v___x_5826_);
lean_closure_set(v___y_5843_, 1, v___x_5842_);
lean_closure_set(v___y_5843_, 2, v___x_5840_);
v___x_5844_ = lean_nat_add(v_start_5824_, v___x_5827_);
lean_dec(v_start_5824_);
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5844_);
v___x_5846_ = v___x_5837_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_array_5823_);
lean_ctor_set(v_reuseFailAlloc_5870_, 1, v___x_5844_);
lean_ctor_set(v_reuseFailAlloc_5870_, 2, v_stop_5825_);
v___x_5846_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; uint8_t v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; 
lean_inc(v_a_5841_);
v___x_5847_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5847_, 0, lean_box(0));
lean_closure_set(v___x_5847_, 1, v_a_5841_);
lean_closure_set(v___x_5847_, 2, v___y_5843_);
v___x_5848_ = lean_box(0);
v___x_5849_ = lean_box(0);
v___x_5850_ = lean_box(1);
v___x_5851_ = 0;
v___x_5852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5853_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5853_, 0, v___x_5848_);
lean_ctor_set(v___x_5853_, 1, v___x_5849_);
lean_ctor_set(v___x_5853_, 2, v___x_5848_);
lean_ctor_set(v___x_5853_, 3, v___f_5839_);
lean_ctor_set(v___x_5853_, 4, v___x_5850_);
lean_ctor_set(v___x_5853_, 5, v___x_5850_);
lean_ctor_set(v___x_5853_, 6, v___x_5848_);
lean_ctor_set(v___x_5853_, 7, v___x_5852_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8, v___x_5831_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 1, v___x_5831_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 2, v___x_5831_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 3, v___x_5831_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 4, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 5, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 6, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 7, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 8, v___x_5831_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 9, v___x_5851_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*8 + 10, v___x_5831_);
v___x_5854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5855_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5847_, v___x_5853_, v___x_5854_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v___x_5857_; 
lean_dec_ref_known(v___x_5855_, 1);
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 1, v___x_5830_);
lean_ctor_set(v___x_5810_, 0, v___x_5846_);
v___x_5857_ = v___x_5810_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v___x_5846_);
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
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec_ref(v___x_5846_);
lean_dec_ref(v___x_5830_);
lean_del_object(v___x_5810_);
v_a_5862_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5855_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5855_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
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
lean_object* v___x_5967_; lean_object* v_env_5968_; lean_object* v_nextMacroScope_5969_; lean_object* v_ngen_5970_; lean_object* v_auxDeclNGen_5971_; lean_object* v_traceState_5972_; lean_object* v_recordedDeps_5973_; lean_object* v_messages_5974_; lean_object* v_infoState_5975_; lean_object* v_snapshotTasks_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6001_; 
v___x_5967_ = lean_st_ref_take(v___y_5960_);
v_env_5968_ = lean_ctor_get(v___x_5967_, 0);
v_nextMacroScope_5969_ = lean_ctor_get(v___x_5967_, 1);
v_ngen_5970_ = lean_ctor_get(v___x_5967_, 2);
v_auxDeclNGen_5971_ = lean_ctor_get(v___x_5967_, 3);
v_traceState_5972_ = lean_ctor_get(v___x_5967_, 4);
v_recordedDeps_5973_ = lean_ctor_get(v___x_5967_, 6);
v_messages_5974_ = lean_ctor_get(v___x_5967_, 7);
v_infoState_5975_ = lean_ctor_get(v___x_5967_, 8);
v_snapshotTasks_5976_ = lean_ctor_get(v___x_5967_, 9);
v_isSharedCheck_6001_ = !lean_is_exclusive(v___x_5967_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v___x_5967_, 5);
lean_dec(v_unused_6002_);
v___x_5978_ = v___x_5967_;
v_isShared_5979_ = v_isSharedCheck_6001_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_snapshotTasks_5976_);
lean_inc(v_infoState_5975_);
lean_inc(v_messages_5974_);
lean_inc(v_recordedDeps_5973_);
lean_inc(v_traceState_5972_);
lean_inc(v_auxDeclNGen_5971_);
lean_inc(v_ngen_5970_);
lean_inc(v_nextMacroScope_5969_);
lean_inc(v_env_5968_);
lean_dec(v___x_5967_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6001_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5980_ = l_Lean_Environment_setExporting(v_env_5968_, v_isExporting_5961_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 5, v___x_5962_);
lean_ctor_set(v___x_5978_, 0, v___x_5980_);
v___x_5982_ = v___x_5978_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_nextMacroScope_5969_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_ngen_5970_);
lean_ctor_set(v_reuseFailAlloc_6000_, 3, v_auxDeclNGen_5971_);
lean_ctor_set(v_reuseFailAlloc_6000_, 4, v_traceState_5972_);
lean_ctor_set(v_reuseFailAlloc_6000_, 5, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_6000_, 6, v_recordedDeps_5973_);
lean_ctor_set(v_reuseFailAlloc_6000_, 7, v_messages_5974_);
lean_ctor_set(v_reuseFailAlloc_6000_, 8, v_infoState_5975_);
lean_ctor_set(v_reuseFailAlloc_6000_, 9, v_snapshotTasks_5976_);
v___x_5982_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v_mctx_5985_; lean_object* v_zetaDeltaFVarIds_5986_; lean_object* v_postponed_5987_; lean_object* v_diag_5988_; lean_object* v___x_5990_; uint8_t v_isShared_5991_; uint8_t v_isSharedCheck_5998_; 
v___x_5983_ = lean_st_ref_put(v___y_5960_, v___x_5982_);
v___x_5984_ = lean_st_ref_take(v___y_5963_);
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
lean_object* v___x_5992_; lean_object* v___x_5994_; 
v___x_5992_ = lean_box(0);
if (v_isShared_5991_ == 0)
{
lean_ctor_set(v___x_5990_, 1, v___x_5964_);
v___x_5994_ = v___x_5990_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_mctx_5985_);
lean_ctor_set(v_reuseFailAlloc_5997_, 1, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5997_, 2, v_zetaDeltaFVarIds_5986_);
lean_ctor_set(v_reuseFailAlloc_5997_, 3, v_postponed_5987_);
lean_ctor_set(v_reuseFailAlloc_5997_, 4, v_diag_5988_);
v___x_5994_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5995_ = lean_st_ref_put(v___y_5963_, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5992_);
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
lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_6013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
return v___x_6013_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6014_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6016_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
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
lean_object* v___x_6097_; 
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v___x_6097_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
return v___x_6097_;
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
lean_object* v___x_6098_; 
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v___x_6098_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
return v___x_6098_;
}
}
v___jp_6031_:
{
lean_object* v___x_6032_; lean_object* v_env_6033_; lean_object* v_nextMacroScope_6034_; lean_object* v_ngen_6035_; lean_object* v_auxDeclNGen_6036_; lean_object* v_traceState_6037_; lean_object* v_recordedDeps_6038_; lean_object* v_messages_6039_; lean_object* v_infoState_6040_; lean_object* v_snapshotTasks_6041_; lean_object* v___x_6043_; uint8_t v_isShared_6044_; uint8_t v_isSharedCheck_6095_; 
v___x_6032_ = lean_st_ref_take(v___y_6023_);
v_env_6033_ = lean_ctor_get(v___x_6032_, 0);
v_nextMacroScope_6034_ = lean_ctor_get(v___x_6032_, 1);
v_ngen_6035_ = lean_ctor_get(v___x_6032_, 2);
v_auxDeclNGen_6036_ = lean_ctor_get(v___x_6032_, 3);
v_traceState_6037_ = lean_ctor_get(v___x_6032_, 4);
v_recordedDeps_6038_ = lean_ctor_get(v___x_6032_, 6);
v_messages_6039_ = lean_ctor_get(v___x_6032_, 7);
v_infoState_6040_ = lean_ctor_get(v___x_6032_, 8);
v_snapshotTasks_6041_ = lean_ctor_get(v___x_6032_, 9);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6032_);
if (v_isSharedCheck_6095_ == 0)
{
lean_object* v_unused_6096_; 
v_unused_6096_ = lean_ctor_get(v___x_6032_, 5);
lean_dec(v_unused_6096_);
v___x_6043_ = v___x_6032_;
v_isShared_6044_ = v_isSharedCheck_6095_;
goto v_resetjp_6042_;
}
else
{
lean_inc(v_snapshotTasks_6041_);
lean_inc(v_infoState_6040_);
lean_inc(v_messages_6039_);
lean_inc(v_recordedDeps_6038_);
lean_inc(v_traceState_6037_);
lean_inc(v_auxDeclNGen_6036_);
lean_inc(v_ngen_6035_);
lean_inc(v_nextMacroScope_6034_);
lean_inc(v_env_6033_);
lean_dec(v___x_6032_);
v___x_6043_ = lean_box(0);
v_isShared_6044_ = v_isSharedCheck_6095_;
goto v_resetjp_6042_;
}
v_resetjp_6042_:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6048_; 
v___x_6045_ = l_Lean_Environment_setExporting(v_env_6033_, v_isExporting_6019_);
v___x_6046_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
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
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v_nextMacroScope_6034_);
lean_ctor_set(v_reuseFailAlloc_6094_, 2, v_ngen_6035_);
lean_ctor_set(v_reuseFailAlloc_6094_, 3, v_auxDeclNGen_6036_);
lean_ctor_set(v_reuseFailAlloc_6094_, 4, v_traceState_6037_);
lean_ctor_set(v_reuseFailAlloc_6094_, 5, v___x_6046_);
lean_ctor_set(v_reuseFailAlloc_6094_, 6, v_recordedDeps_6038_);
lean_ctor_set(v_reuseFailAlloc_6094_, 7, v_messages_6039_);
lean_ctor_set(v_reuseFailAlloc_6094_, 8, v_infoState_6040_);
lean_ctor_set(v_reuseFailAlloc_6094_, 9, v_snapshotTasks_6041_);
v___x_6048_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v_mctx_6051_; lean_object* v_zetaDeltaFVarIds_6052_; lean_object* v_postponed_6053_; lean_object* v_diag_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6092_; 
v___x_6049_ = lean_st_ref_put(v___y_6023_, v___x_6048_);
v___x_6050_ = lean_st_ref_take(v___y_6021_);
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
v___x_6058_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
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
v___x_6061_ = lean_st_ref_put(v___y_6021_, v___x_6060_);
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v_r_6062_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
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
v___x_6069_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6023_, v_isExporting_6030_, v___x_6046_, v___y_6021_, v___x_6058_, v___x_6068_);
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
v___x_6082_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6023_, v_isExporting_6030_, v___x_6046_, v___y_6021_, v___x_6058_, v___x_6081_);
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
lean_object* v___x_6324_; 
v___x_6324_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6315_, v_a_6317_);
if (lean_obj_tag(v___x_6324_) == 0)
{
lean_object* v_a_6325_; lean_object* v___x_6326_; uint8_t v___x_6327_; 
v_a_6325_ = lean_ctor_get(v___x_6324_, 0);
lean_inc(v_a_6325_);
lean_dec_ref_known(v___x_6324_, 1);
v___x_6326_ = l_Lean_Expr_cleanupAnnotations(v_a_6325_);
v___x_6327_ = l_Lean_Expr_isApp(v___x_6326_);
if (v___x_6327_ == 0)
{
lean_dec_ref(v___x_6326_);
goto v___jp_6321_;
}
else
{
lean_object* v_arg_6328_; lean_object* v___x_6329_; uint8_t v___x_6330_; 
v_arg_6328_ = lean_ctor_get(v___x_6326_, 1);
lean_inc_ref(v_arg_6328_);
v___x_6329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6326_);
v___x_6330_ = l_Lean_Expr_isApp(v___x_6329_);
if (v___x_6330_ == 0)
{
lean_dec_ref(v___x_6329_);
lean_dec_ref(v_arg_6328_);
goto v___jp_6321_;
}
else
{
lean_object* v_arg_6331_; lean_object* v___x_6332_; uint8_t v___x_6333_; 
v_arg_6331_ = lean_ctor_get(v___x_6329_, 1);
lean_inc_ref(v_arg_6331_);
v___x_6332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6329_);
v___x_6333_ = l_Lean_Expr_isApp(v___x_6332_);
if (v___x_6333_ == 0)
{
lean_dec_ref(v___x_6332_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
goto v___jp_6321_;
}
else
{
lean_object* v_arg_6334_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
v_arg_6334_ = lean_ctor_get(v___x_6332_, 1);
lean_inc_ref(v_arg_6334_);
v___x_6335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6332_);
v___x_6336_ = l_Lean_Expr_isApp(v___x_6335_);
if (v___x_6336_ == 0)
{
lean_dec_ref(v___x_6335_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
goto v___jp_6321_;
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; uint8_t v___x_6339_; 
v___x_6337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6335_);
v___x_6338_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6339_ = l_Lean_Expr_isConstOf(v___x_6337_, v___x_6338_);
lean_dec_ref(v___x_6337_);
if (v___x_6339_ == 0)
{
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
goto v___jp_6321_;
}
else
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6341_ = l_Lean_Meta_isExprDefEq(v_arg_6334_, v___x_6340_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_);
if (lean_obj_tag(v___x_6341_) == 0)
{
lean_object* v_a_6342_; lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6375_; 
v_a_6342_ = lean_ctor_get(v___x_6341_, 0);
v_isSharedCheck_6375_ = !lean_is_exclusive(v___x_6341_);
if (v_isSharedCheck_6375_ == 0)
{
v___x_6344_ = v___x_6341_;
v_isShared_6345_ = v_isSharedCheck_6375_;
goto v_resetjp_6343_;
}
else
{
lean_inc(v_a_6342_);
lean_dec(v___x_6341_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6375_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
uint8_t v___x_6346_; 
v___x_6346_ = lean_unbox(v_a_6342_);
lean_dec(v_a_6342_);
if (v___x_6346_ == 0)
{
lean_object* v___x_6347_; lean_object* v___x_6349_; 
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
v___x_6347_ = lean_box(0);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 0, v___x_6347_);
v___x_6349_ = v___x_6344_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v___x_6347_);
v___x_6349_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
return v___x_6349_;
}
}
else
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
lean_del_object(v___x_6344_);
v___x_6351_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6352_ = l_Lean_Meta_isExprDefEq(v_arg_6328_, v___x_6351_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_);
if (lean_obj_tag(v___x_6352_) == 0)
{
lean_object* v_a_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6366_; 
v_a_6353_ = lean_ctor_get(v___x_6352_, 0);
v_isSharedCheck_6366_ = !lean_is_exclusive(v___x_6352_);
if (v_isSharedCheck_6366_ == 0)
{
v___x_6355_ = v___x_6352_;
v_isShared_6356_ = v_isSharedCheck_6366_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_a_6353_);
lean_dec(v___x_6352_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6366_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
uint8_t v___x_6357_; 
v___x_6357_ = lean_unbox(v_a_6353_);
lean_dec(v_a_6353_);
if (v___x_6357_ == 0)
{
lean_object* v___x_6358_; lean_object* v___x_6360_; 
lean_dec_ref(v_arg_6331_);
v___x_6358_ = lean_box(0);
if (v_isShared_6356_ == 0)
{
lean_ctor_set(v___x_6355_, 0, v___x_6358_);
v___x_6360_ = v___x_6355_;
goto v_reusejp_6359_;
}
else
{
lean_object* v_reuseFailAlloc_6361_; 
v_reuseFailAlloc_6361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6361_, 0, v___x_6358_);
v___x_6360_ = v_reuseFailAlloc_6361_;
goto v_reusejp_6359_;
}
v_reusejp_6359_:
{
return v___x_6360_;
}
}
else
{
lean_object* v___x_6362_; lean_object* v___x_6364_; 
v___x_6362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6362_, 0, v_arg_6331_);
if (v_isShared_6356_ == 0)
{
lean_ctor_set(v___x_6355_, 0, v___x_6362_);
v___x_6364_ = v___x_6355_;
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
}
}
else
{
lean_object* v_a_6367_; lean_object* v___x_6369_; uint8_t v_isShared_6370_; uint8_t v_isSharedCheck_6374_; 
lean_dec_ref(v_arg_6331_);
v_a_6367_ = lean_ctor_get(v___x_6352_, 0);
v_isSharedCheck_6374_ = !lean_is_exclusive(v___x_6352_);
if (v_isSharedCheck_6374_ == 0)
{
v___x_6369_ = v___x_6352_;
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
else
{
lean_inc(v_a_6367_);
lean_dec(v___x_6352_);
v___x_6369_ = lean_box(0);
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
v_resetjp_6368_:
{
lean_object* v___x_6372_; 
if (v_isShared_6370_ == 0)
{
v___x_6372_ = v___x_6369_;
goto v_reusejp_6371_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_a_6367_);
v___x_6372_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6371_;
}
v_reusejp_6371_:
{
return v___x_6372_;
}
}
}
}
}
}
else
{
lean_object* v_a_6376_; lean_object* v___x_6378_; uint8_t v_isShared_6379_; uint8_t v_isSharedCheck_6383_; 
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
v_a_6376_ = lean_ctor_get(v___x_6341_, 0);
v_isSharedCheck_6383_ = !lean_is_exclusive(v___x_6341_);
if (v_isSharedCheck_6383_ == 0)
{
v___x_6378_ = v___x_6341_;
v_isShared_6379_ = v_isSharedCheck_6383_;
goto v_resetjp_6377_;
}
else
{
lean_inc(v_a_6376_);
lean_dec(v___x_6341_);
v___x_6378_ = lean_box(0);
v_isShared_6379_ = v_isSharedCheck_6383_;
goto v_resetjp_6377_;
}
v_resetjp_6377_:
{
lean_object* v___x_6381_; 
if (v_isShared_6379_ == 0)
{
v___x_6381_ = v___x_6378_;
goto v_reusejp_6380_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6376_);
v___x_6381_ = v_reuseFailAlloc_6382_;
goto v_reusejp_6380_;
}
v_reusejp_6380_:
{
return v___x_6381_;
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
lean_object* v_a_6384_; lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6391_; 
v_a_6384_ = lean_ctor_get(v___x_6324_, 0);
v_isSharedCheck_6391_ = !lean_is_exclusive(v___x_6324_);
if (v_isSharedCheck_6391_ == 0)
{
v___x_6386_ = v___x_6324_;
v_isShared_6387_ = v_isSharedCheck_6391_;
goto v_resetjp_6385_;
}
else
{
lean_inc(v_a_6384_);
lean_dec(v___x_6324_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6391_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
lean_object* v___x_6389_; 
if (v_isShared_6387_ == 0)
{
v___x_6389_ = v___x_6386_;
goto v_reusejp_6388_;
}
else
{
lean_object* v_reuseFailAlloc_6390_; 
v_reuseFailAlloc_6390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_a_6384_);
v___x_6389_ = v_reuseFailAlloc_6390_;
goto v_reusejp_6388_;
}
v_reusejp_6388_:
{
return v___x_6389_;
}
}
}
v___jp_6321_:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_box(0);
v___x_6323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6323_, 0, v___x_6322_);
return v___x_6323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_){
_start:
{
lean_object* v_res_6398_; 
v_res_6398_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6392_, v_a_6393_, v_a_6394_, v_a_6395_, v_a_6396_);
lean_dec(v_a_6396_);
lean_dec_ref(v_a_6395_);
lean_dec(v_a_6394_);
lean_dec_ref(v_a_6393_);
return v_res_6398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6399_, lean_object* v_maxFVars_x3f_6400_, lean_object* v_k_6401_, uint8_t v_cleanupAnnotations_6402_, uint8_t v_whnfType_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_, lean_object* v___y_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_){
_start:
{
lean_object* v___f_6411_; lean_object* v___x_6412_; 
lean_inc(v___y_6405_);
lean_inc_ref(v___y_6404_);
v___f_6411_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6411_, 0, v_k_6401_);
lean_closure_set(v___f_6411_, 1, v___y_6404_);
lean_closure_set(v___f_6411_, 2, v___y_6405_);
v___x_6412_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6399_, v_maxFVars_x3f_6400_, v___f_6411_, v_cleanupAnnotations_6402_, v_whnfType_6403_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_);
if (lean_obj_tag(v___x_6412_) == 0)
{
return v___x_6412_;
}
else
{
lean_object* v_a_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6420_; 
v_a_6413_ = lean_ctor_get(v___x_6412_, 0);
v_isSharedCheck_6420_ = !lean_is_exclusive(v___x_6412_);
if (v_isSharedCheck_6420_ == 0)
{
v___x_6415_ = v___x_6412_;
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_a_6413_);
lean_dec(v___x_6412_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
lean_object* v___x_6418_; 
if (v_isShared_6416_ == 0)
{
v___x_6418_ = v___x_6415_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_a_6413_);
v___x_6418_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
return v___x_6418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6421_, lean_object* v_maxFVars_x3f_6422_, lean_object* v_k_6423_, lean_object* v_cleanupAnnotations_6424_, lean_object* v_whnfType_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6433_; uint8_t v_whnfType_boxed_6434_; lean_object* v_res_6435_; 
v_cleanupAnnotations_boxed_6433_ = lean_unbox(v_cleanupAnnotations_6424_);
v_whnfType_boxed_6434_ = lean_unbox(v_whnfType_6425_);
v_res_6435_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6421_, v_maxFVars_x3f_6422_, v_k_6423_, v_cleanupAnnotations_boxed_6433_, v_whnfType_boxed_6434_, v___y_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_, v___y_6431_);
lean_dec(v___y_6431_);
lean_dec_ref(v___y_6430_);
lean_dec(v___y_6429_);
lean_dec_ref(v___y_6428_);
lean_dec(v___y_6427_);
lean_dec_ref(v___y_6426_);
return v_res_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6436_, lean_object* v_type_6437_, lean_object* v_maxFVars_x3f_6438_, lean_object* v_k_6439_, uint8_t v_cleanupAnnotations_6440_, uint8_t v_whnfType_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_){
_start:
{
lean_object* v___x_6449_; 
v___x_6449_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6437_, v_maxFVars_x3f_6438_, v_k_6439_, v_cleanupAnnotations_6440_, v_whnfType_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
return v___x_6449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6450_, lean_object* v_type_6451_, lean_object* v_maxFVars_x3f_6452_, lean_object* v_k_6453_, lean_object* v_cleanupAnnotations_6454_, lean_object* v_whnfType_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6463_; uint8_t v_whnfType_boxed_6464_; lean_object* v_res_6465_; 
v_cleanupAnnotations_boxed_6463_ = lean_unbox(v_cleanupAnnotations_6454_);
v_whnfType_boxed_6464_ = lean_unbox(v_whnfType_6455_);
v_res_6465_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6450_, v_type_6451_, v_maxFVars_x3f_6452_, v_k_6453_, v_cleanupAnnotations_boxed_6463_, v_whnfType_boxed_6464_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6460_);
lean_dec(v___y_6459_);
lean_dec_ref(v___y_6458_);
lean_dec(v___y_6457_);
lean_dec_ref(v___y_6456_);
return v_res_6465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6466_, lean_object* v_x_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_){
_start:
{
lean_object* v_keyedConfig_6475_; uint8_t v_trackZetaDelta_6476_; lean_object* v_zetaDeltaSet_6477_; lean_object* v_localInstances_6478_; lean_object* v_defEqCtx_x3f_6479_; lean_object* v_synthPendingDepth_6480_; lean_object* v_customCanUnfoldPredicate_x3f_6481_; uint8_t v_univApprox_6482_; uint8_t v_inTypeClassResolution_6483_; uint8_t v_cacheInferType_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v_keyedConfig_6475_ = lean_ctor_get(v___y_6470_, 0);
v_trackZetaDelta_6476_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*7);
v_zetaDeltaSet_6477_ = lean_ctor_get(v___y_6470_, 1);
v_localInstances_6478_ = lean_ctor_get(v___y_6470_, 3);
v_defEqCtx_x3f_6479_ = lean_ctor_get(v___y_6470_, 4);
v_synthPendingDepth_6480_ = lean_ctor_get(v___y_6470_, 5);
v_customCanUnfoldPredicate_x3f_6481_ = lean_ctor_get(v___y_6470_, 6);
v_univApprox_6482_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6483_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*7 + 2);
v_cacheInferType_6484_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6481_);
lean_inc(v_synthPendingDepth_6480_);
lean_inc(v_defEqCtx_x3f_6479_);
lean_inc_ref(v_localInstances_6478_);
lean_inc(v_zetaDeltaSet_6477_);
lean_inc_ref(v_keyedConfig_6475_);
v___x_6485_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6485_, 0, v_keyedConfig_6475_);
lean_ctor_set(v___x_6485_, 1, v_zetaDeltaSet_6477_);
lean_ctor_set(v___x_6485_, 2, v_lctx_6466_);
lean_ctor_set(v___x_6485_, 3, v_localInstances_6478_);
lean_ctor_set(v___x_6485_, 4, v_defEqCtx_x3f_6479_);
lean_ctor_set(v___x_6485_, 5, v_synthPendingDepth_6480_);
lean_ctor_set(v___x_6485_, 6, v_customCanUnfoldPredicate_x3f_6481_);
lean_ctor_set_uint8(v___x_6485_, sizeof(void*)*7, v_trackZetaDelta_6476_);
lean_ctor_set_uint8(v___x_6485_, sizeof(void*)*7 + 1, v_univApprox_6482_);
lean_ctor_set_uint8(v___x_6485_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6483_);
lean_ctor_set_uint8(v___x_6485_, sizeof(void*)*7 + 3, v_cacheInferType_6484_);
lean_inc(v___y_6473_);
lean_inc_ref(v___y_6472_);
lean_inc(v___y_6471_);
lean_inc(v___y_6469_);
lean_inc_ref(v___y_6468_);
v___x_6486_ = lean_apply_7(v_x_6467_, v___y_6468_, v___y_6469_, v___x_6485_, v___y_6471_, v___y_6472_, v___y_6473_, lean_box(0));
if (lean_obj_tag(v___x_6486_) == 0)
{
lean_object* v_a_6487_; lean_object* v___x_6489_; uint8_t v_isShared_6490_; uint8_t v_isSharedCheck_6494_; 
v_a_6487_ = lean_ctor_get(v___x_6486_, 0);
v_isSharedCheck_6494_ = !lean_is_exclusive(v___x_6486_);
if (v_isSharedCheck_6494_ == 0)
{
v___x_6489_ = v___x_6486_;
v_isShared_6490_ = v_isSharedCheck_6494_;
goto v_resetjp_6488_;
}
else
{
lean_inc(v_a_6487_);
lean_dec(v___x_6486_);
v___x_6489_ = lean_box(0);
v_isShared_6490_ = v_isSharedCheck_6494_;
goto v_resetjp_6488_;
}
v_resetjp_6488_:
{
lean_object* v___x_6492_; 
if (v_isShared_6490_ == 0)
{
v___x_6492_ = v___x_6489_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6493_; 
v_reuseFailAlloc_6493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6493_, 0, v_a_6487_);
v___x_6492_ = v_reuseFailAlloc_6493_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
return v___x_6492_;
}
}
}
else
{
return v___x_6486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6495_, lean_object* v_x_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
lean_object* v_res_6504_; 
v_res_6504_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6495_, v_x_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
lean_dec(v___y_6502_);
lean_dec_ref(v___y_6501_);
lean_dec(v___y_6500_);
lean_dec_ref(v___y_6499_);
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6497_);
return v_res_6504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6505_, lean_object* v_lctx_6506_, lean_object* v_x_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_){
_start:
{
lean_object* v___x_6515_; 
v___x_6515_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6506_, v_x_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_);
return v___x_6515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6516_, lean_object* v_lctx_6517_, lean_object* v_x_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_){
_start:
{
lean_object* v_res_6526_; 
v_res_6526_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6516_, v_lctx_6517_, v_x_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_);
lean_dec(v___y_6524_);
lean_dec_ref(v___y_6523_);
lean_dec(v___y_6522_);
lean_dec_ref(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
return v_res_6526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v_prefixArgs_6527_, lean_object* v_declName_6528_, lean_object* v_x_6529_, lean_object* v_F_6530_, lean_object* v_val_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; 
v___x_6539_ = lean_array_get_size(v_prefixArgs_6527_);
v___x_6540_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6540_, 0, v_declName_6528_);
lean_closure_set(v___x_6540_, 1, v___x_6539_);
v___x_6541_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6529_, v_F_6530_, v_val_6531_, v___x_6540_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_);
return v___x_6541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v_prefixArgs_6542_, lean_object* v_declName_6543_, lean_object* v_x_6544_, lean_object* v_F_6545_, lean_object* v_val_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_){
_start:
{
lean_object* v_res_6554_; 
v_res_6554_ = l_Lean_Elab_WF_mkFix___lam__0(v_prefixArgs_6542_, v_declName_6543_, v_x_6544_, v_F_6545_, v_val_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec(v___y_6550_);
lean_dec_ref(v___y_6549_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
lean_dec_ref(v_prefixArgs_6542_);
return v_res_6554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v___x_6571_, lean_object* v___x_6572_, lean_object* v_wfRel_6573_, lean_object* v_x_6574_, lean_object* v_type_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_){
_start:
{
lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6583_ = lean_unsigned_to_nat(0u);
v___x_6584_ = lean_array_get_borrowed(v___x_6571_, v_x_6574_, v___x_6583_);
v___x_6585_ = l_Lean_Expr_fvarId_x21(v___x_6584_);
v___x_6586_ = l_Lean_FVarId_getUserName___redArg(v___x_6585_, v___y_6578_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_a_6587_; lean_object* v___x_6588_; 
v_a_6587_ = lean_ctor_get(v___x_6586_, 0);
lean_inc(v_a_6587_);
lean_dec_ref_known(v___x_6586_, 1);
lean_inc(v___y_6581_);
lean_inc_ref(v___y_6580_);
lean_inc(v___y_6579_);
lean_inc_ref(v___y_6578_);
lean_inc(v___x_6584_);
v___x_6588_ = lean_infer_type(v___x_6584_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v___x_6590_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
lean_inc_n(v_a_6589_, 2);
lean_dec_ref_known(v___x_6588_, 1);
v___x_6590_ = l_Lean_Meta_getLevel(v_a_6589_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6590_) == 0)
{
lean_object* v_a_6591_; lean_object* v___x_6592_; 
v_a_6591_ = lean_ctor_get(v___x_6590_, 0);
lean_inc(v_a_6591_);
lean_dec_ref_known(v___x_6590_, 1);
lean_inc_ref(v_type_6575_);
v___x_6592_ = l_Lean_Meta_getLevel(v_type_6575_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; uint8_t v___x_6596_; uint8_t v___x_6597_; uint8_t v___x_6598_; lean_object* v___x_6599_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
lean_inc(v_a_6593_);
lean_dec_ref_known(v___x_6592_, 1);
v___x_6594_ = lean_mk_empty_array_with_capacity(v___x_6572_);
lean_inc(v___x_6584_);
lean_inc_ref(v___x_6594_);
v___x_6595_ = lean_array_push(v___x_6594_, v___x_6584_);
v___x_6596_ = 0;
v___x_6597_ = 1;
v___x_6598_ = 1;
v___x_6599_ = l_Lean_Meta_mkLambdaFVars(v___x_6595_, v_type_6575_, v___x_6596_, v___x_6597_, v___x_6596_, v___x_6597_, v___x_6598_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
lean_dec_ref(v___x_6595_);
if (lean_obj_tag(v___x_6599_) == 0)
{
lean_object* v_a_6600_; lean_object* v___x_6601_; 
v_a_6600_ = lean_ctor_get(v___x_6599_, 0);
lean_inc(v_a_6600_);
lean_dec_ref_known(v___x_6599_, 1);
lean_inc_ref(v_wfRel_6573_);
v___x_6601_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6573_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6601_) == 0)
{
lean_object* v_a_6602_; lean_object* v___x_6604_; uint8_t v_isShared_6605_; uint8_t v_isSharedCheck_6646_; 
v_a_6602_ = lean_ctor_get(v___x_6601_, 0);
v_isSharedCheck_6646_ = !lean_is_exclusive(v___x_6601_);
if (v_isSharedCheck_6646_ == 0)
{
v___x_6604_ = v___x_6601_;
v_isShared_6605_ = v_isSharedCheck_6646_;
goto v_resetjp_6603_;
}
else
{
lean_inc(v_a_6602_);
lean_dec(v___x_6601_);
v___x_6604_ = lean_box(0);
v_isShared_6605_ = v_isSharedCheck_6646_;
goto v_resetjp_6603_;
}
v_resetjp_6603_:
{
if (lean_obj_tag(v_a_6602_) == 1)
{
lean_object* v_val_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6615_; 
lean_dec_ref(v___x_6594_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_val_6606_ = lean_ctor_get(v_a_6602_, 0);
lean_inc(v_val_6606_);
lean_dec_ref_known(v_a_6602_, 1);
v___x_6607_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__2));
v___x_6608_ = lean_box(0);
v___x_6609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6609_, 0, v_a_6593_);
lean_ctor_set(v___x_6609_, 1, v___x_6608_);
v___x_6610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6610_, 0, v_a_6591_);
lean_ctor_set(v___x_6610_, 1, v___x_6609_);
v___x_6611_ = l_Lean_mkConst(v___x_6607_, v___x_6610_);
v___x_6612_ = l_Lean_mkApp3(v___x_6611_, v_a_6589_, v_a_6600_, v_val_6606_);
v___x_6613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6612_);
lean_ctor_set(v___x_6613_, 1, v_a_6587_);
if (v_isShared_6605_ == 0)
{
lean_ctor_set(v___x_6604_, 0, v___x_6613_);
v___x_6615_ = v___x_6604_;
goto v_reusejp_6614_;
}
else
{
lean_object* v_reuseFailAlloc_6616_; 
v_reuseFailAlloc_6616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6616_, 0, v___x_6613_);
v___x_6615_ = v_reuseFailAlloc_6616_;
goto v_reusejp_6614_;
}
v_reusejp_6614_:
{
return v___x_6615_;
}
}
else
{
lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; 
lean_del_object(v___x_6604_);
lean_dec(v_a_6602_);
v___x_6617_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__4));
lean_inc_ref(v_wfRel_6573_);
v___x_6618_ = l_Lean_mkProj(v___x_6617_, v___x_6583_, v_wfRel_6573_);
v___x_6619_ = l_Lean_mkProj(v___x_6617_, v___x_6572_, v_wfRel_6573_);
v___x_6620_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__6));
v___x_6621_ = lean_array_push(v___x_6594_, v___x_6619_);
v___x_6622_ = l_Lean_Meta_mkAppM(v___x_6620_, v___x_6621_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
if (lean_obj_tag(v___x_6622_) == 0)
{
lean_object* v_a_6623_; lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6637_; 
v_a_6623_ = lean_ctor_get(v___x_6622_, 0);
v_isSharedCheck_6637_ = !lean_is_exclusive(v___x_6622_);
if (v_isSharedCheck_6637_ == 0)
{
v___x_6625_ = v___x_6622_;
v_isShared_6626_ = v_isSharedCheck_6637_;
goto v_resetjp_6624_;
}
else
{
lean_inc(v_a_6623_);
lean_dec(v___x_6622_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6637_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6635_; 
v___x_6627_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__7));
v___x_6628_ = lean_box(0);
v___x_6629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6629_, 0, v_a_6593_);
lean_ctor_set(v___x_6629_, 1, v___x_6628_);
v___x_6630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6630_, 0, v_a_6591_);
lean_ctor_set(v___x_6630_, 1, v___x_6629_);
v___x_6631_ = l_Lean_mkConst(v___x_6627_, v___x_6630_);
v___x_6632_ = l_Lean_mkApp4(v___x_6631_, v_a_6589_, v_a_6600_, v___x_6618_, v_a_6623_);
v___x_6633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6633_, 0, v___x_6632_);
lean_ctor_set(v___x_6633_, 1, v_a_6587_);
if (v_isShared_6626_ == 0)
{
lean_ctor_set(v___x_6625_, 0, v___x_6633_);
v___x_6635_ = v___x_6625_;
goto v_reusejp_6634_;
}
else
{
lean_object* v_reuseFailAlloc_6636_; 
v_reuseFailAlloc_6636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6636_, 0, v___x_6633_);
v___x_6635_ = v_reuseFailAlloc_6636_;
goto v_reusejp_6634_;
}
v_reusejp_6634_:
{
return v___x_6635_;
}
}
}
else
{
lean_object* v_a_6638_; lean_object* v___x_6640_; uint8_t v_isShared_6641_; uint8_t v_isSharedCheck_6645_; 
lean_dec_ref(v___x_6618_);
lean_dec(v_a_6600_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec(v_a_6587_);
v_a_6638_ = lean_ctor_get(v___x_6622_, 0);
v_isSharedCheck_6645_ = !lean_is_exclusive(v___x_6622_);
if (v_isSharedCheck_6645_ == 0)
{
v___x_6640_ = v___x_6622_;
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
else
{
lean_inc(v_a_6638_);
lean_dec(v___x_6622_);
v___x_6640_ = lean_box(0);
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
v_resetjp_6639_:
{
lean_object* v___x_6643_; 
if (v_isShared_6641_ == 0)
{
v___x_6643_ = v___x_6640_;
goto v_reusejp_6642_;
}
else
{
lean_object* v_reuseFailAlloc_6644_; 
v_reuseFailAlloc_6644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_a_6638_);
v___x_6643_ = v_reuseFailAlloc_6644_;
goto v_reusejp_6642_;
}
v_reusejp_6642_:
{
return v___x_6643_;
}
}
}
}
}
}
else
{
lean_object* v_a_6647_; lean_object* v___x_6649_; uint8_t v_isShared_6650_; uint8_t v_isSharedCheck_6654_; 
lean_dec(v_a_6600_);
lean_dec_ref(v___x_6594_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec(v_a_6587_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6647_ = lean_ctor_get(v___x_6601_, 0);
v_isSharedCheck_6654_ = !lean_is_exclusive(v___x_6601_);
if (v_isSharedCheck_6654_ == 0)
{
v___x_6649_ = v___x_6601_;
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
else
{
lean_inc(v_a_6647_);
lean_dec(v___x_6601_);
v___x_6649_ = lean_box(0);
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
v_resetjp_6648_:
{
lean_object* v___x_6652_; 
if (v_isShared_6650_ == 0)
{
v___x_6652_ = v___x_6649_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_a_6647_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
return v___x_6652_;
}
}
}
}
else
{
lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6662_; 
lean_dec_ref(v___x_6594_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec(v_a_6587_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6655_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6662_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6662_ == 0)
{
v___x_6657_ = v___x_6599_;
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_dec(v___x_6599_);
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
else
{
lean_object* v_a_6663_; lean_object* v___x_6665_; uint8_t v_isShared_6666_; uint8_t v_isSharedCheck_6670_; 
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec(v_a_6587_);
lean_dec_ref(v_type_6575_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6663_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6670_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6670_ == 0)
{
v___x_6665_ = v___x_6592_;
v_isShared_6666_ = v_isSharedCheck_6670_;
goto v_resetjp_6664_;
}
else
{
lean_inc(v_a_6663_);
lean_dec(v___x_6592_);
v___x_6665_ = lean_box(0);
v_isShared_6666_ = v_isSharedCheck_6670_;
goto v_resetjp_6664_;
}
v_resetjp_6664_:
{
lean_object* v___x_6668_; 
if (v_isShared_6666_ == 0)
{
v___x_6668_ = v___x_6665_;
goto v_reusejp_6667_;
}
else
{
lean_object* v_reuseFailAlloc_6669_; 
v_reuseFailAlloc_6669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6669_, 0, v_a_6663_);
v___x_6668_ = v_reuseFailAlloc_6669_;
goto v_reusejp_6667_;
}
v_reusejp_6667_:
{
return v___x_6668_;
}
}
}
}
else
{
lean_object* v_a_6671_; lean_object* v___x_6673_; uint8_t v_isShared_6674_; uint8_t v_isSharedCheck_6678_; 
lean_dec(v_a_6589_);
lean_dec(v_a_6587_);
lean_dec_ref(v_type_6575_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6671_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6678_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6678_ == 0)
{
v___x_6673_ = v___x_6590_;
v_isShared_6674_ = v_isSharedCheck_6678_;
goto v_resetjp_6672_;
}
else
{
lean_inc(v_a_6671_);
lean_dec(v___x_6590_);
v___x_6673_ = lean_box(0);
v_isShared_6674_ = v_isSharedCheck_6678_;
goto v_resetjp_6672_;
}
v_resetjp_6672_:
{
lean_object* v___x_6676_; 
if (v_isShared_6674_ == 0)
{
v___x_6676_ = v___x_6673_;
goto v_reusejp_6675_;
}
else
{
lean_object* v_reuseFailAlloc_6677_; 
v_reuseFailAlloc_6677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_a_6671_);
v___x_6676_ = v_reuseFailAlloc_6677_;
goto v_reusejp_6675_;
}
v_reusejp_6675_:
{
return v___x_6676_;
}
}
}
}
else
{
lean_object* v_a_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6686_; 
lean_dec(v_a_6587_);
lean_dec_ref(v_type_6575_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6679_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6686_ == 0)
{
v___x_6681_ = v___x_6588_;
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_a_6679_);
lean_dec(v___x_6588_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
lean_object* v___x_6684_; 
if (v_isShared_6682_ == 0)
{
v___x_6684_ = v___x_6681_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_a_6679_);
v___x_6684_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
return v___x_6684_;
}
}
}
}
else
{
lean_object* v_a_6687_; lean_object* v___x_6689_; uint8_t v_isShared_6690_; uint8_t v_isSharedCheck_6694_; 
lean_dec_ref(v_type_6575_);
lean_dec_ref(v_wfRel_6573_);
lean_dec(v___x_6572_);
v_a_6687_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6694_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6694_ == 0)
{
v___x_6689_ = v___x_6586_;
v_isShared_6690_ = v_isSharedCheck_6694_;
goto v_resetjp_6688_;
}
else
{
lean_inc(v_a_6687_);
lean_dec(v___x_6586_);
v___x_6689_ = lean_box(0);
v_isShared_6690_ = v_isSharedCheck_6694_;
goto v_resetjp_6688_;
}
v_resetjp_6688_:
{
lean_object* v___x_6692_; 
if (v_isShared_6690_ == 0)
{
v___x_6692_ = v___x_6689_;
goto v_reusejp_6691_;
}
else
{
lean_object* v_reuseFailAlloc_6693_; 
v_reuseFailAlloc_6693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6693_, 0, v_a_6687_);
v___x_6692_ = v_reuseFailAlloc_6693_;
goto v_reusejp_6691_;
}
v_reusejp_6691_:
{
return v___x_6692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v___x_6695_, lean_object* v___x_6696_, lean_object* v_wfRel_6697_, lean_object* v_x_6698_, lean_object* v_type_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_){
_start:
{
lean_object* v_res_6707_; 
v_res_6707_ = l_Lean_Elab_WF_mkFix___lam__1(v___x_6695_, v___x_6696_, v_wfRel_6697_, v_x_6698_, v_type_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
lean_dec(v___y_6705_);
lean_dec_ref(v___y_6704_);
lean_dec(v___y_6703_);
lean_dec_ref(v___y_6702_);
lean_dec(v___y_6701_);
lean_dec_ref(v___y_6700_);
lean_dec_ref(v_x_6698_);
lean_dec_ref(v___x_6695_);
return v_res_6707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6708_, lean_object* v___x_6709_, lean_object* v___x_6710_, lean_object* v___f_6711_, lean_object* v_funNames_6712_, lean_object* v_argsPacker_6713_, lean_object* v_decrTactics_6714_, uint8_t v___x_6715_, lean_object* v_fst_6716_, lean_object* v_prefixArgs_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_, lean_object* v___y_6721_, lean_object* v___y_6722_, lean_object* v___y_6723_){
_start:
{
lean_object* v___x_6725_; 
lean_inc_ref(v___x_6709_);
lean_inc_ref(v___x_6708_);
v___x_6725_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6708_, v___x_6709_, v___x_6710_, v___f_6711_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
if (lean_obj_tag(v___x_6725_) == 0)
{
lean_object* v_a_6726_; lean_object* v___x_6727_; 
v_a_6726_ = lean_ctor_get(v___x_6725_, 0);
lean_inc(v_a_6726_);
lean_dec_ref_known(v___x_6725_, 1);
v___x_6727_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6712_, v_argsPacker_6713_, v_decrTactics_6714_, v_a_6726_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; uint8_t v___x_6733_; uint8_t v___x_6734_; lean_object* v___x_6735_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
lean_inc(v_a_6728_);
lean_dec_ref_known(v___x_6727_, 1);
v___x_6729_ = lean_unsigned_to_nat(2u);
v___x_6730_ = lean_mk_empty_array_with_capacity(v___x_6729_);
v___x_6731_ = lean_array_push(v___x_6730_, v___x_6708_);
v___x_6732_ = lean_array_push(v___x_6731_, v___x_6709_);
v___x_6733_ = 1;
v___x_6734_ = 1;
v___x_6735_ = l_Lean_Meta_mkLambdaFVars(v___x_6732_, v_a_6728_, v___x_6715_, v___x_6733_, v___x_6715_, v___x_6733_, v___x_6734_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
lean_dec_ref(v___x_6732_);
if (lean_obj_tag(v___x_6735_) == 0)
{
lean_object* v_a_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; 
v_a_6736_ = lean_ctor_get(v___x_6735_, 0);
lean_inc(v_a_6736_);
lean_dec_ref_known(v___x_6735_, 1);
v___x_6737_ = l_Lean_Expr_app___override(v_fst_6716_, v_a_6736_);
v___x_6738_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6717_, v___x_6737_, v___x_6715_, v___x_6733_, v___x_6715_, v___x_6733_, v___x_6734_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
return v___x_6738_;
}
else
{
lean_dec_ref(v_fst_6716_);
return v___x_6735_;
}
}
else
{
lean_dec_ref(v_fst_6716_);
lean_dec_ref(v___x_6709_);
lean_dec_ref(v___x_6708_);
return v___x_6727_;
}
}
else
{
lean_dec_ref(v_fst_6716_);
lean_dec_ref(v_decrTactics_6714_);
lean_dec_ref(v_argsPacker_6713_);
lean_dec_ref(v_funNames_6712_);
lean_dec_ref(v___x_6709_);
lean_dec_ref(v___x_6708_);
return v___x_6725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6739_ = _args[0];
lean_object* v___x_6740_ = _args[1];
lean_object* v___x_6741_ = _args[2];
lean_object* v___f_6742_ = _args[3];
lean_object* v_funNames_6743_ = _args[4];
lean_object* v_argsPacker_6744_ = _args[5];
lean_object* v_decrTactics_6745_ = _args[6];
lean_object* v___x_6746_ = _args[7];
lean_object* v_fst_6747_ = _args[8];
lean_object* v_prefixArgs_6748_ = _args[9];
lean_object* v___y_6749_ = _args[10];
lean_object* v___y_6750_ = _args[11];
lean_object* v___y_6751_ = _args[12];
lean_object* v___y_6752_ = _args[13];
lean_object* v___y_6753_ = _args[14];
lean_object* v___y_6754_ = _args[15];
lean_object* v___y_6755_ = _args[16];
_start:
{
uint8_t v___x_5939__boxed_6756_; lean_object* v_res_6757_; 
v___x_5939__boxed_6756_ = lean_unbox(v___x_6746_);
v_res_6757_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6739_, v___x_6740_, v___x_6741_, v___f_6742_, v_funNames_6743_, v_argsPacker_6744_, v_decrTactics_6745_, v___x_5939__boxed_6756_, v_fst_6747_, v_prefixArgs_6748_, v___y_6749_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_, v___y_6754_);
lean_dec(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v_prefixArgs_6748_);
return v_res_6757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6758_, lean_object* v_snd_6759_, lean_object* v___x_6760_, lean_object* v_prefixArgs_6761_, lean_object* v_value_6762_, lean_object* v___f_6763_, lean_object* v_funNames_6764_, lean_object* v_argsPacker_6765_, lean_object* v_decrTactics_6766_, uint8_t v___x_6767_, lean_object* v_fst_6768_, lean_object* v_xs_6769_, lean_object* v_x_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_){
_start:
{
lean_object* v_lctx_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___f_6787_; lean_object* v___x_6788_; 
v_lctx_6778_ = lean_ctor_get(v___y_6773_, 2);
v___x_6779_ = lean_unsigned_to_nat(0u);
v___x_6780_ = lean_array_get_borrowed(v___x_6758_, v_xs_6769_, v___x_6779_);
v___x_6781_ = l_Lean_Expr_fvarId_x21(v___x_6780_);
lean_inc_ref(v_lctx_6778_);
v___x_6782_ = l_Lean_LocalContext_setUserName(v_lctx_6778_, v___x_6781_, v_snd_6759_);
v___x_6783_ = lean_array_get_borrowed(v___x_6758_, v_xs_6769_, v___x_6760_);
lean_inc_n(v___x_6780_, 2);
lean_inc_ref(v_prefixArgs_6761_);
v___x_6784_ = lean_array_push(v_prefixArgs_6761_, v___x_6780_);
v___x_6785_ = l_Lean_Expr_beta(v_value_6762_, v___x_6784_);
v___x_6786_ = lean_box(v___x_6767_);
lean_inc(v___x_6783_);
v___f_6787_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6787_, 0, v___x_6780_);
lean_closure_set(v___f_6787_, 1, v___x_6783_);
lean_closure_set(v___f_6787_, 2, v___x_6785_);
lean_closure_set(v___f_6787_, 3, v___f_6763_);
lean_closure_set(v___f_6787_, 4, v_funNames_6764_);
lean_closure_set(v___f_6787_, 5, v_argsPacker_6765_);
lean_closure_set(v___f_6787_, 6, v_decrTactics_6766_);
lean_closure_set(v___f_6787_, 7, v___x_6786_);
lean_closure_set(v___f_6787_, 8, v_fst_6768_);
lean_closure_set(v___f_6787_, 9, v_prefixArgs_6761_);
v___x_6788_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6782_, v___f_6787_, v___y_6771_, v___y_6772_, v___y_6773_, v___y_6774_, v___y_6775_, v___y_6776_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6789_ = _args[0];
lean_object* v_snd_6790_ = _args[1];
lean_object* v___x_6791_ = _args[2];
lean_object* v_prefixArgs_6792_ = _args[3];
lean_object* v_value_6793_ = _args[4];
lean_object* v___f_6794_ = _args[5];
lean_object* v_funNames_6795_ = _args[6];
lean_object* v_argsPacker_6796_ = _args[7];
lean_object* v_decrTactics_6797_ = _args[8];
lean_object* v___x_6798_ = _args[9];
lean_object* v_fst_6799_ = _args[10];
lean_object* v_xs_6800_ = _args[11];
lean_object* v_x_6801_ = _args[12];
lean_object* v___y_6802_ = _args[13];
lean_object* v___y_6803_ = _args[14];
lean_object* v___y_6804_ = _args[15];
lean_object* v___y_6805_ = _args[16];
lean_object* v___y_6806_ = _args[17];
lean_object* v___y_6807_ = _args[18];
lean_object* v___y_6808_ = _args[19];
_start:
{
uint8_t v___x_6009__boxed_6809_; lean_object* v_res_6810_; 
v___x_6009__boxed_6809_ = lean_unbox(v___x_6798_);
v_res_6810_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6789_, v_snd_6790_, v___x_6791_, v_prefixArgs_6792_, v_value_6793_, v___f_6794_, v_funNames_6795_, v_argsPacker_6796_, v_decrTactics_6797_, v___x_6009__boxed_6809_, v_fst_6799_, v_xs_6800_, v_x_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_);
lean_dec(v___y_6807_);
lean_dec_ref(v___y_6806_);
lean_dec(v___y_6805_);
lean_dec_ref(v___y_6804_);
lean_dec(v___y_6803_);
lean_dec_ref(v___y_6802_);
lean_dec_ref(v_x_6801_);
lean_dec_ref(v_xs_6800_);
lean_dec(v___x_6791_);
lean_dec_ref(v___x_6789_);
return v_res_6810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6815_, lean_object* v_prefixArgs_6816_, lean_object* v_argsPacker_6817_, lean_object* v_wfRel_6818_, lean_object* v_funNames_6819_, lean_object* v_decrTactics_6820_, lean_object* v_a_6821_, lean_object* v_a_6822_, lean_object* v_a_6823_, lean_object* v_a_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_){
_start:
{
lean_object* v_declName_6828_; lean_object* v_type_6829_; lean_object* v_value_6830_; lean_object* v___f_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; 
v_declName_6828_ = lean_ctor_get(v_preDef_6815_, 3);
lean_inc(v_declName_6828_);
v_type_6829_ = lean_ctor_get(v_preDef_6815_, 6);
lean_inc_ref(v_type_6829_);
v_value_6830_ = lean_ctor_get(v_preDef_6815_, 7);
lean_inc_ref(v_value_6830_);
lean_dec_ref(v_preDef_6815_);
lean_inc_ref(v_prefixArgs_6816_);
v___f_6831_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 2);
lean_closure_set(v___f_6831_, 0, v_prefixArgs_6816_);
lean_closure_set(v___f_6831_, 1, v_declName_6828_);
v___x_6832_ = l_Lean_instInhabitedExpr;
v___x_6833_ = l_Lean_Meta_instantiateForall(v_type_6829_, v_prefixArgs_6816_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
if (lean_obj_tag(v___x_6833_) == 0)
{
lean_object* v_a_6834_; lean_object* v___x_6835_; lean_object* v___f_6836_; lean_object* v___x_6837_; uint8_t v___x_6838_; lean_object* v___x_6839_; 
v_a_6834_ = lean_ctor_get(v___x_6833_, 0);
lean_inc(v_a_6834_);
lean_dec_ref_known(v___x_6833_, 1);
v___x_6835_ = lean_unsigned_to_nat(1u);
v___f_6836_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6836_, 0, v___x_6832_);
lean_closure_set(v___f_6836_, 1, v___x_6835_);
lean_closure_set(v___f_6836_, 2, v_wfRel_6818_);
v___x_6837_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6838_ = 0;
v___x_6839_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6834_, v___x_6837_, v___f_6836_, v___x_6838_, v___x_6838_, v_a_6821_, v_a_6822_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
if (lean_obj_tag(v___x_6839_) == 0)
{
lean_object* v_a_6840_; lean_object* v_fst_6841_; lean_object* v_snd_6842_; lean_object* v___x_6843_; lean_object* v___f_6844_; lean_object* v___x_6845_; 
v_a_6840_ = lean_ctor_get(v___x_6839_, 0);
lean_inc(v_a_6840_);
lean_dec_ref_known(v___x_6839_, 1);
v_fst_6841_ = lean_ctor_get(v_a_6840_, 0);
lean_inc_n(v_fst_6841_, 2);
v_snd_6842_ = lean_ctor_get(v_a_6840_, 1);
lean_inc(v_snd_6842_);
lean_dec(v_a_6840_);
v___x_6843_ = lean_box(v___x_6838_);
v___f_6844_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6844_, 0, v___x_6832_);
lean_closure_set(v___f_6844_, 1, v_snd_6842_);
lean_closure_set(v___f_6844_, 2, v___x_6835_);
lean_closure_set(v___f_6844_, 3, v_prefixArgs_6816_);
lean_closure_set(v___f_6844_, 4, v_value_6830_);
lean_closure_set(v___f_6844_, 5, v___f_6831_);
lean_closure_set(v___f_6844_, 6, v_funNames_6819_);
lean_closure_set(v___f_6844_, 7, v_argsPacker_6817_);
lean_closure_set(v___f_6844_, 8, v_decrTactics_6820_);
lean_closure_set(v___f_6844_, 9, v___x_6843_);
lean_closure_set(v___f_6844_, 10, v_fst_6841_);
lean_inc(v_a_6826_);
lean_inc_ref(v_a_6825_);
lean_inc(v_a_6824_);
lean_inc_ref(v_a_6823_);
v___x_6845_ = lean_infer_type(v_fst_6841_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
if (lean_obj_tag(v___x_6845_) == 0)
{
lean_object* v_a_6846_; lean_object* v___x_6847_; 
v_a_6846_ = lean_ctor_get(v___x_6845_, 0);
lean_inc(v_a_6846_);
lean_dec_ref_known(v___x_6845_, 1);
lean_inc(v_a_6826_);
lean_inc_ref(v_a_6825_);
lean_inc(v_a_6824_);
lean_inc_ref(v_a_6823_);
v___x_6847_ = lean_whnf(v_a_6846_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
if (lean_obj_tag(v___x_6847_) == 0)
{
lean_object* v_a_6848_; lean_object* v___x_6849_; lean_object* v___x_6850_; lean_object* v___x_6851_; 
v_a_6848_ = lean_ctor_get(v___x_6847_, 0);
lean_inc(v_a_6848_);
lean_dec_ref_known(v___x_6847_, 1);
v___x_6849_ = l_Lean_Expr_bindingDomain_x21(v_a_6848_);
lean_dec(v_a_6848_);
v___x_6850_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6851_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6849_, v___x_6850_, v___f_6844_, v___x_6838_, v___x_6838_, v_a_6821_, v_a_6822_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
return v___x_6851_;
}
else
{
lean_dec_ref(v___f_6844_);
return v___x_6847_;
}
}
else
{
lean_dec_ref(v___f_6844_);
return v___x_6845_;
}
}
else
{
lean_object* v_a_6852_; lean_object* v___x_6854_; uint8_t v_isShared_6855_; uint8_t v_isSharedCheck_6859_; 
lean_dec_ref(v___f_6831_);
lean_dec_ref(v_value_6830_);
lean_dec_ref(v_decrTactics_6820_);
lean_dec_ref(v_funNames_6819_);
lean_dec_ref(v_argsPacker_6817_);
lean_dec_ref(v_prefixArgs_6816_);
v_a_6852_ = lean_ctor_get(v___x_6839_, 0);
v_isSharedCheck_6859_ = !lean_is_exclusive(v___x_6839_);
if (v_isSharedCheck_6859_ == 0)
{
v___x_6854_ = v___x_6839_;
v_isShared_6855_ = v_isSharedCheck_6859_;
goto v_resetjp_6853_;
}
else
{
lean_inc(v_a_6852_);
lean_dec(v___x_6839_);
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
else
{
lean_dec_ref(v___f_6831_);
lean_dec_ref(v_value_6830_);
lean_dec_ref(v_decrTactics_6820_);
lean_dec_ref(v_funNames_6819_);
lean_dec_ref(v_wfRel_6818_);
lean_dec_ref(v_argsPacker_6817_);
lean_dec_ref(v_prefixArgs_6816_);
return v___x_6833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6860_, lean_object* v_prefixArgs_6861_, lean_object* v_argsPacker_6862_, lean_object* v_wfRel_6863_, lean_object* v_funNames_6864_, lean_object* v_decrTactics_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_){
_start:
{
lean_object* v_res_6873_; 
v_res_6873_ = l_Lean_Elab_WF_mkFix(v_preDef_6860_, v_prefixArgs_6861_, v_argsPacker_6862_, v_wfRel_6863_, v_funNames_6864_, v_decrTactics_6865_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
lean_dec(v_a_6871_);
lean_dec_ref(v_a_6870_);
lean_dec(v_a_6869_);
lean_dec_ref(v_a_6868_);
lean_dec(v_a_6867_);
lean_dec_ref(v_a_6866_);
return v_res_6873_;
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
