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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 217, 178, 28, 107, 212, 157, 131)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(201, 156, 94, 164, 220, 114, 107, 70)}};
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_134_; lean_object* v_env_135_; uint8_t v___x_136_; lean_object* v_env_137_; lean_object* v___x_138_; lean_object* v_toCold_139_; lean_object* v_mctx_140_; lean_object* v_lctx_141_; lean_object* v_options_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = 0;
v_env_137_ = l_Lean_Environment_setRecordingDeps(v_env_135_, v___x_136_);
v___x_138_ = lean_st_ref_get(v___y_130_);
v_toCold_139_ = lean_ctor_get(v___y_131_, 0);
v_mctx_140_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_mctx_140_);
lean_dec(v___x_138_);
v_lctx_141_ = lean_ctor_get(v___y_129_, 2);
v_options_142_ = lean_ctor_get(v_toCold_139_, 2);
lean_inc_ref(v_options_142_);
lean_inc_ref(v_lctx_141_);
v___x_143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_143_, 0, v_env_137_);
lean_ctor_set(v___x_143_, 1, v_mctx_140_);
lean_ctor_set(v___x_143_, 2, v_lctx_141_);
lean_ctor_set(v___x_143_, 3, v_options_142_);
v___x_144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_msgData_128_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msgData_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 2);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_ref_159_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_ref_159_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2));
v___x_181_ = lean_unsigned_to_nat(14u);
v___x_182_ = lean_unsigned_to_nat(22u);
v___x_183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1));
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_199_; lean_object* v_lctx_203_; lean_object* v___x_204_; uint8_t v___x_214_; 
v_lctx_203_ = lean_ctor_get(v_a_189_, 2);
v___x_204_ = lean_box(0);
v___x_214_ = l_Lean_LocalContext_isEmpty(v_lctx_203_);
if (v___x_214_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
v___x_215_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5);
v___x_216_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_215_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = l_Lean_LocalDecl_fvarId(v___y_195_);
lean_dec_ref(v___y_195_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
v___jp_198_:
{
if (lean_obj_tag(v___y_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3);
v___x_201_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(v___x_200_);
v___y_195_ = v___x_201_;
goto v___jp_194_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___y_199_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___y_199_, 1);
v___y_195_ = v_val_202_;
goto v___jp_194_;
}
}
v___jp_205_:
{
lean_object* v_decls_206_; lean_object* v_size_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_decls_206_ = lean_ctor_get(v_lctx_203_, 1);
v_size_207_ = lean_ctor_get(v_decls_206_, 2);
v___x_208_ = l_Lean_LocalContext_size(v_lctx_203_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_sub(v___x_208_, v___x_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_nat_dec_lt(v___x_210_, v_size_207_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
lean_dec(v___x_210_);
v___x_212_ = l_outOfBounds___redArg(v___x_204_);
v___y_199_ = v___x_212_;
goto v___jp_198_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentArray_get_x21___redArg(v___x_204_, v_decls_206_, v___x_210_);
lean_dec(v___x_210_);
v___y_199_ = v___x_213_;
goto v___jp_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___boxed(lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(lean_object* v_00_u03b1_231_, lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___boxed(lean_object* v_00_u03b1_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(v_00_u03b1_239_, v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(lean_object* v_lctxid_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_lctx_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_lctx_250_ = lean_ctor_get(v_a_248_, 2);
v___x_251_ = l_Lean_LocalContext_contains(v_lctx_250_, v_lctxid_247_);
v___x_252_ = lean_box(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg___boxed(lean_object* v_lctxid_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_254_, v_a_255_);
lean_dec_ref(v_a_255_);
lean_dec(v_lctxid_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(lean_object* v_lctxid_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_258_, v_a_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___boxed(lean_object* v_lctxid_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(v_lctxid_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_lctxid_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(lean_object* v_recFnName_272_, lean_object* v_e_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_mk_empty_array_with_capacity(v___x_276_);
v___x_278_ = lean_array_push(v___x_277_, v_recFnName_272_);
v___x_279_ = lean_st_ref_take(v_a_274_);
v___x_280_ = l_Lean_HasConstCache_containsUnsafe(v___x_278_, v_e_273_, v___x_279_);
lean_dec_ref(v___x_278_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = lean_st_ref_put(v_a_274_, v_snd_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_fst_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg___boxed(lean_object* v_recFnName_285_, lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_285_, v_e_286_, v_a_287_);
lean_dec(v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object* v_recFnName_290_, lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_290_, v_e_291_, v_a_292_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object* v_recFnName_302_, lean_object* v_e_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(v_recFnName_302_, v_e_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
return v_res_313_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_314_; double v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_float_of_nat(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object* v_cls_319_, lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_ref_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_373_; 
v_ref_326_ = lean_ctor_get(v___y_323_, 2);
v___x_327_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_373_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_373_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_373_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_traceState_333_; lean_object* v_env_334_; lean_object* v_nextMacroScope_335_; lean_object* v_ngen_336_; lean_object* v_auxDeclNGen_337_; lean_object* v_cache_338_; lean_object* v_recordedDeps_339_; lean_object* v_messages_340_; lean_object* v_infoState_341_; lean_object* v_snapshotTasks_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_372_; 
v___x_332_ = lean_st_ref_take(v___y_324_);
v_traceState_333_ = lean_ctor_get(v___x_332_, 4);
v_env_334_ = lean_ctor_get(v___x_332_, 0);
v_nextMacroScope_335_ = lean_ctor_get(v___x_332_, 1);
v_ngen_336_ = lean_ctor_get(v___x_332_, 2);
v_auxDeclNGen_337_ = lean_ctor_get(v___x_332_, 3);
v_cache_338_ = lean_ctor_get(v___x_332_, 5);
v_recordedDeps_339_ = lean_ctor_get(v___x_332_, 6);
v_messages_340_ = lean_ctor_get(v___x_332_, 7);
v_infoState_341_ = lean_ctor_get(v___x_332_, 8);
v_snapshotTasks_342_ = lean_ctor_get(v___x_332_, 9);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_372_ == 0)
{
v___x_344_ = v___x_332_;
v_isShared_345_ = v_isSharedCheck_372_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snapshotTasks_342_);
lean_inc(v_infoState_341_);
lean_inc(v_messages_340_);
lean_inc(v_recordedDeps_339_);
lean_inc(v_cache_338_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_337_);
lean_inc(v_ngen_336_);
lean_inc(v_nextMacroScope_335_);
lean_inc(v_env_334_);
lean_dec(v___x_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_372_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint64_t v_tid_346_; lean_object* v_traces_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_371_; 
v_tid_346_ = lean_ctor_get_uint64(v_traceState_333_, sizeof(void*)*1);
v_traces_347_ = lean_ctor_get(v_traceState_333_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_traceState_333_);
if (v_isSharedCheck_371_ == 0)
{
v___x_349_ = v_traceState_333_;
v_isShared_350_ = v_isSharedCheck_371_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_traces_347_);
lean_dec(v_traceState_333_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_371_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; double v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_351_ = lean_box(0);
v___x_352_ = lean_box(0);
v___x_353_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_354_ = 0;
v___x_355_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_356_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_356_, 0, v_cls_319_);
lean_ctor_set(v___x_356_, 1, v___x_352_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
lean_ctor_set_float(v___x_356_, sizeof(void*)*3, v___x_353_);
lean_ctor_set_float(v___x_356_, sizeof(void*)*3 + 8, v___x_353_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*3 + 16, v___x_354_);
v___x_357_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_358_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v_a_328_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_inc(v_ref_326_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_ref_326_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_PersistentArray_push___redArg(v_traces_347_, v___x_359_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_360_);
v___x_362_ = v___x_349_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_360_);
lean_ctor_set_uint64(v_reuseFailAlloc_370_, sizeof(void*)*1, v_tid_346_);
v___x_362_ = v_reuseFailAlloc_370_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v___x_362_);
v___x_364_ = v___x_344_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_env_334_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_nextMacroScope_335_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_ngen_336_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_auxDeclNGen_337_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_369_, 5, v_cache_338_);
lean_ctor_set(v_reuseFailAlloc_369_, 6, v_recordedDeps_339_);
lean_ctor_set(v_reuseFailAlloc_369_, 7, v_messages_340_);
lean_ctor_set(v_reuseFailAlloc_369_, 8, v_infoState_341_);
lean_ctor_set(v_reuseFailAlloc_369_, 9, v_snapshotTasks_342_);
v___x_364_ = v_reuseFailAlloc_369_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_st_ref_put(v___y_324_, v___x_364_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_351_);
v___x_367_ = v___x_330_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_351_);
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
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_nbuckets_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_423_ = lean_array_get_size(v_data_422_);
v___x_424_ = lean_unsigned_to_nat(2u);
v_nbuckets_425_ = lean_nat_mul(v___x_423_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_box(0);
v___x_428_ = lean_mk_array(v_nbuckets_425_, v___x_427_);
v___x_429_ = lean_array_propagate_mark(v_data_422_, v___x_428_);
v___x_430_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_426_, v_data_422_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_431_, lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 0;
return v___x_433_;
}
else
{
lean_object* v_key_434_; lean_object* v_tail_435_; uint8_t v___x_436_; 
v_key_434_ = lean_ctor_get(v_x_432_, 0);
v_tail_435_ = lean_ctor_get(v_x_432_, 2);
v___x_436_ = lean_expr_eqv(v_key_434_, v_a_431_);
if (v___x_436_ == 0)
{
v_x_432_ = v_tail_435_;
goto _start;
}
else
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_a_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_442_, lean_object* v_b_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_b_443_);
lean_dec_ref(v_a_442_);
return v_x_444_;
}
else
{
lean_object* v_key_445_; lean_object* v_value_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_459_; 
v_key_445_ = lean_ctor_get(v_x_444_, 0);
v_value_446_ = lean_ctor_get(v_x_444_, 1);
v_tail_447_ = lean_ctor_get(v_x_444_, 2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_459_ == 0)
{
v___x_449_ = v_x_444_;
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_value_446_);
lean_inc(v_key_445_);
lean_dec(v_x_444_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_expr_eqv(v_key_445_, v_a_442_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_442_, v_b_443_, v_tail_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 2, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_key_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_value_446_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v_value_446_);
lean_dec(v_key_445_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_b_443_);
lean_ctor_set(v___x_449_, 0, v_a_442_);
v___x_457_ = v___x_449_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_442_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_b_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_tail_447_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_460_, lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_size_463_; lean_object* v_buckets_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_507_; 
v_size_463_ = lean_ctor_get(v_m_460_, 0);
v_buckets_464_ = lean_ctor_get(v_m_460_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_m_460_);
if (v_isSharedCheck_507_ == 0)
{
v___x_466_ = v_m_460_;
v_isShared_467_ = v_isSharedCheck_507_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_buckets_464_);
lean_inc(v_size_463_);
lean_dec(v_m_460_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_507_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v_fold_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v_bkt_481_; uint8_t v___x_482_; 
v___x_468_ = lean_array_get_size(v_buckets_464_);
v___x_469_ = l_Lean_Expr_hash(v_a_461_);
v___x_470_ = 32ULL;
v___x_471_ = lean_uint64_shift_right(v___x_469_, v___x_470_);
v_fold_472_ = lean_uint64_xor(v___x_469_, v___x_471_);
v___x_473_ = 16ULL;
v___x_474_ = lean_uint64_shift_right(v_fold_472_, v___x_473_);
v___x_475_ = lean_uint64_xor(v_fold_472_, v___x_474_);
v___x_476_ = lean_uint64_to_usize(v___x_475_);
v___x_477_ = lean_usize_of_nat(v___x_468_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_sub(v___x_477_, v___x_478_);
v___x_480_ = lean_usize_land(v___x_476_, v___x_479_);
v_bkt_481_ = lean_array_uget_borrowed(v_buckets_464_, v___x_480_);
v___x_482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_461_, v_bkt_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v_size_x27_484_; lean_object* v___x_485_; lean_object* v_buckets_x27_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v_size_x27_484_ = lean_nat_add(v_size_463_, v___x_483_);
lean_dec(v_size_463_);
lean_inc(v_bkt_481_);
v___x_485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_485_, 0, v_a_461_);
lean_ctor_set(v___x_485_, 1, v_b_462_);
lean_ctor_set(v___x_485_, 2, v_bkt_481_);
v_buckets_x27_486_ = lean_array_uset(v_buckets_464_, v___x_480_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(4u);
v___x_488_ = lean_nat_mul(v_size_x27_484_, v___x_487_);
v___x_489_ = lean_unsigned_to_nat(3u);
v___x_490_ = lean_nat_div(v___x_488_, v___x_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_array_get_size(v_buckets_x27_486_);
v___x_492_ = lean_nat_dec_le(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
if (v___x_492_ == 0)
{
lean_object* v_val_493_; lean_object* v___x_495_; 
v_val_493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_486_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v_val_493_);
lean_ctor_set(v___x_466_, 0, v_size_x27_484_);
v___x_495_ = v___x_466_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_size_x27_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_val_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_498_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v_buckets_x27_486_);
lean_ctor_set(v___x_466_, 0, v_size_x27_484_);
v___x_498_ = v___x_466_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_size_x27_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_buckets_x27_486_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v___x_500_; lean_object* v_buckets_x27_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_bkt_481_);
v___x_500_ = lean_box(0);
v_buckets_x27_501_ = lean_array_uset(v_buckets_464_, v___x_480_, v___x_500_);
v___x_502_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_461_, v_b_462_, v_bkt_481_);
v___x_503_ = lean_array_uset(v_buckets_x27_501_, v___x_480_, v___x_502_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_503_);
v___x_505_ = v___x_466_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_size_463_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_ref_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_ref_514_ = lean_ctor_get(v___y_511_, 2);
v___x_515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc(v_ref_514_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_ref_514_);
lean_ctor_set(v___x_520_, 1, v_a_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 1);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_632_; 
lean_inc_ref(v_a_548_);
v___x_632_ = l_Lean_Meta_isTypeCorrect(v_a_548_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; uint8_t v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_547_);
v___x_636_ = l_Lean_indentExpr(v_e_547_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
lean_inc_ref(v_a_548_);
v___x_640_ = l_Lean_indentExpr(v_a_548_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_641_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref_known(v___x_642_, 1);
goto v___jp_558_;
}
else
{
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
return v___x_642_;
}
}
else
{
goto v___jp_558_;
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v_a_643_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_632_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_632_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
v___jp_558_:
{
lean_object* v___x_559_; 
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc_ref(v_e_547_);
v___x_559_ = lean_infer_type(v_e_547_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc_ref(v_a_548_);
v___x_561_ = lean_infer_type(v_a_548_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_n(v_a_562_, 2);
lean_dec_ref_known(v___x_561_, 1);
lean_inc(v_a_560_);
v___x_563_ = l_Lean_Meta_isExprDefEq(v_a_560_, v_a_562_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_607_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_607_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_607_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_607_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint8_t v___x_568_; 
v___x_568_ = lean_unbox(v_a_564_);
lean_dec(v_a_564_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_del_object(v___x_566_);
v___x_569_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_560_, v_a_562_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_594_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v_fst_571_ = lean_ctor_get(v_a_570_, 0);
v_snd_572_ = lean_ctor_get(v_a_570_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_570_);
if (v_isSharedCheck_594_ == 0)
{
v___x_574_ = v_a_570_;
v_isShared_575_ = v_isSharedCheck_594_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_572_);
lean_inc(v_fst_571_);
lean_dec(v_a_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_594_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_577_ = l_Lean_indentExpr(v_e_547_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 7);
lean_ctor_set(v___x_574_, 1, v___x_577_);
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_577_);
v___x_579_ = v_reuseFailAlloc_593_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_580_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_indentExpr(v_a_548_);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_indentExpr(v_fst_571_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_indentExpr(v_snd_572_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_591_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_592_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v_a_595_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_569_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_569_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec(v_a_562_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v___x_603_ = lean_box(0);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_603_);
v___x_605_ = v___x_566_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
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
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_562_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v_a_608_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_563_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_563_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_560_);
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v_a_616_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_561_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_561_);
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
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_a_548_);
lean_dec_ref(v_e_547_);
v_a_624_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_559_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_559_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_e_651_, lean_object* v_a_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_e_651_, v_a_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec(v___y_653_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
lean_ctor_set(v___x_669_, 3, v___x_668_);
lean_ctor_set(v___x_669_, 4, v___x_667_);
lean_ctor_set(v___x_669_, 5, v___x_667_);
lean_ctor_set(v___x_669_, 6, v___x_667_);
lean_ctor_set(v___x_669_, 7, v___x_667_);
lean_ctor_set(v___x_669_, 8, v___x_667_);
lean_ctor_set(v___x_669_, 9, v___x_667_);
lean_ctor_set(v___x_669_, 10, v___x_667_);
lean_ctor_set(v___x_669_, 11, v___x_666_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_unsigned_to_nat(32u);
v___x_671_ = lean_mk_empty_array_with_capacity(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_673_ = ((size_t)5ULL);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_unsigned_to_nat(32u);
v___x_676_ = lean_mk_empty_array_with_capacity(v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_678_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_674_);
lean_ctor_set(v___x_678_, 3, v___x_674_);
lean_ctor_set_usize(v___x_678_, 4, v___x_673_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(1);
v___x_680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_680_);
lean_ctor_set(v___x_682_, 2, v___x_679_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_704_, lean_object* v_declHint_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_env_710_; uint8_t v___x_711_; 
v___x_708_ = lean_box(0);
v___x_709_ = lean_st_ref_get(v___y_706_);
v_env_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_709_);
v___x_711_ = l_Lean_Name_isAnonymous(v_declHint_705_);
if (v___x_711_ == 0)
{
uint8_t v_isExporting_712_; 
v_isExporting_712_ = lean_ctor_get_uint8(v_env_710_, sizeof(void*)*13);
if (v_isExporting_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_msg_704_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
lean_inc_ref(v_env_710_);
v___x_714_ = l_Lean_Environment_setExporting(v_env_710_, v___x_711_);
lean_inc(v_declHint_705_);
lean_inc_ref(v___x_714_);
v___x_715_ = l_Lean_Environment_contains(v___x_714_, v_declHint_705_, v_isExporting_712_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msg_704_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_c_722_; lean_object* v___x_723_; 
v___x_717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_719_ = l_Lean_Options_empty;
v___x_720_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_720_, 0, v___x_714_);
lean_ctor_set(v___x_720_, 1, v___x_717_);
lean_ctor_set(v___x_720_, 2, v___x_718_);
lean_ctor_set(v___x_720_, 3, v___x_719_);
lean_inc(v_declHint_705_);
v___x_721_ = l_Lean_MessageData_ofConstName(v_declHint_705_, v___x_711_);
v_c_722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_722_, 0, v___x_720_);
lean_ctor_set(v_c_722_, 1, v___x_721_);
v___x_723_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_710_, v_declHint_705_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_c_722_);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_MessageData_note(v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v_msg_704_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_765_; 
v_val_731_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_765_ == 0)
{
v___x_733_ = v___x_723_;
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_723_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v_moduleNames_736_; lean_object* v_mod_737_; uint8_t v___x_738_; 
v___x_735_ = l_Lean_Environment_header(v_env_710_);
lean_dec_ref(v_env_710_);
v_moduleNames_736_ = lean_ctor_get(v___x_735_, 4);
lean_inc_ref(v_moduleNames_736_);
lean_dec_ref(v___x_735_);
v_mod_737_ = lean_array_get(v___x_708_, v_moduleNames_736_, v_val_731_);
lean_dec(v_val_731_);
lean_dec_ref(v_moduleNames_736_);
v___x_738_ = l_Lean_isPrivateName(v_declHint_705_);
lean_dec(v_declHint_705_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_c_722_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_ofName(v_mod_737_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_MessageData_note(v___x_746_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v_msg_704_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_748_);
v___x_750_ = v___x_733_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_c_722_);
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_MessageData_ofName(v_mod_737_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_MessageData_note(v___x_759_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v_msg_704_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_761_);
v___x_763_ = v___x_733_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_766_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_msg_704_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_767_, lean_object* v_declHint_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_767_, v_declHint_768_, v___y_769_);
lean_dec(v___y_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_772_, lean_object* v_declHint_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v___x_783_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_772_, v_declHint_773_, v___y_781_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_793_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = l_Lean_unknownIdentifierMessageTag;
v___x_789_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_a_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_794_, lean_object* v_declHint_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_794_, v_declHint_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_toCold_817_; lean_object* v_currRecDepth_818_; lean_object* v_ref_819_; uint16_t v_optionFlags_820_; uint8_t v_suppressElabErrors_821_; uint8_t v_isRecordingDeps_822_; lean_object* v_ref_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_toCold_817_ = lean_ctor_get(v___y_814_, 0);
v_currRecDepth_818_ = lean_ctor_get(v___y_814_, 1);
v_ref_819_ = lean_ctor_get(v___y_814_, 2);
v_optionFlags_820_ = lean_ctor_get_uint16(v___y_814_, sizeof(void*)*3);
v_suppressElabErrors_821_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 2);
v_isRecordingDeps_822_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 3);
v_ref_823_ = l_Lean_replaceRef(v_ref_806_, v_ref_819_);
lean_inc(v_currRecDepth_818_);
lean_inc_ref(v_toCold_817_);
v___x_824_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_824_, 0, v_toCold_817_);
lean_ctor_set(v___x_824_, 1, v_currRecDepth_818_);
lean_ctor_set(v___x_824_, 2, v_ref_823_);
lean_ctor_set_uint16(v___x_824_, sizeof(void*)*3, v_optionFlags_820_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*3 + 2, v_suppressElabErrors_821_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*3 + 3, v_isRecordingDeps_822_);
v___x_825_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_807_, v___y_812_, v___y_813_, v___x_824_, v___y_815_);
lean_dec_ref_known(v___x_824_, 3);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_826_, lean_object* v_msg_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_826_, v_msg_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v_ref_826_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_838_, lean_object* v_msg_839_, lean_object* v_declHint_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_852_; 
v___x_850_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_839_, v_declHint_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
v___x_852_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_838_, v_a_851_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_853_, lean_object* v_msg_854_, lean_object* v_declHint_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_853_, v_msg_854_, v_declHint_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v_ref_853_);
return v_res_865_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_872_, lean_object* v_constName_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_883_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_884_ = 0;
lean_inc(v_constName_873_);
v___x_885_ = l_Lean_MessageData_ofConstName(v_constName_873_, v___x_884_);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_883_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_872_, v___x_888_, v_constName_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_890_, lean_object* v_constName_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_890_, v_constName_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v_ref_890_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_ref_912_; lean_object* v___x_913_; 
v_ref_912_ = lean_ctor_get(v___y_909_, 2);
v___x_913_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_912_, v_constName_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v_env_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_st_ref_get(v___y_933_);
v_env_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_env_936_);
lean_dec(v___x_935_);
v___x_937_ = 0;
lean_inc(v_constName_925_);
v___x_938_ = l_Lean_Environment_find_x3f(v_env_936_, v_constName_925_, v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_939_;
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_constName_925_);
v_val_940_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_938_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v___x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 0);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_env_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = lean_st_ref_get(v___y_960_);
v_env_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_env_963_);
lean_dec(v___x_962_);
v___x_964_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_963_, v_declName_959_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_966_, v___y_967_);
lean_dec(v___y_967_);
return v_res_969_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_instMonadEIO___redArg();
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_toApplicative_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1082_; 
v___x_987_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_988_ = l_StateRefT_x27_instMonad___redArg(v___x_987_);
v_toApplicative_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_988_, 1);
lean_dec(v_unused_1083_);
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1082_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toApplicative_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1082_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_toFunctor_993_; lean_object* v_toSeq_994_; lean_object* v_toSeqLeft_995_; lean_object* v_toSeqRight_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1080_; 
v_toFunctor_993_ = lean_ctor_get(v_toApplicative_989_, 0);
v_toSeq_994_ = lean_ctor_get(v_toApplicative_989_, 2);
v_toSeqLeft_995_ = lean_ctor_get(v_toApplicative_989_, 3);
v_toSeqRight_996_ = lean_ctor_get(v_toApplicative_989_, 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_toApplicative_989_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_toApplicative_989_, 1);
lean_dec(v_unused_1081_);
v___x_998_ = v_toApplicative_989_;
v_isShared_999_ = v_isSharedCheck_1080_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_toSeqRight_996_);
lean_inc(v_toSeqLeft_995_);
lean_inc(v_toSeq_994_);
lean_inc(v_toFunctor_993_);
lean_dec(v_toApplicative_989_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1080_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1009_; 
v___f_1000_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1001_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_993_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toFunctor_993_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toFunctor_993_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___f_1002_);
lean_ctor_set(v___x_1004_, 1, v___f_1003_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toSeqRight_996_);
v___f_1006_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1006_, 0, v_toSeqLeft_995_);
v___f_1007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1007_, 0, v_toSeq_994_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v___f_1005_);
lean_ctor_set(v___x_998_, 3, v___f_1006_);
lean_ctor_set(v___x_998_, 2, v___f_1007_);
lean_ctor_set(v___x_998_, 1, v___f_1000_);
lean_ctor_set(v___x_998_, 0, v___x_1004_);
v___x_1009_ = v___x_998_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___f_1007_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___f_1005_);
v___x_1009_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___f_1001_);
lean_ctor_set(v___x_991_, 0, v___x_1009_);
v___x_1011_ = v___x_991_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___f_1001_);
v___x_1011_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v_toApplicative_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1076_; 
v___x_1012_ = l_StateRefT_x27_instMonad___redArg(v___x_1011_);
v_toApplicative_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v___x_1012_, 1);
lean_dec(v_unused_1077_);
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1076_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_toApplicative_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1076_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_toFunctor_1017_; lean_object* v_toSeq_1018_; lean_object* v_toSeqLeft_1019_; lean_object* v_toSeqRight_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1074_; 
v_toFunctor_1017_ = lean_ctor_get(v_toApplicative_1013_, 0);
v_toSeq_1018_ = lean_ctor_get(v_toApplicative_1013_, 2);
v_toSeqLeft_1019_ = lean_ctor_get(v_toApplicative_1013_, 3);
v_toSeqRight_1020_ = lean_ctor_get(v_toApplicative_1013_, 4);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_toApplicative_1013_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v_toApplicative_1013_, 1);
lean_dec(v_unused_1075_);
v___x_1022_ = v_toApplicative_1013_;
v_isShared_1023_ = v_isSharedCheck_1074_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_toSeqRight_1020_);
lean_inc(v_toSeqLeft_1019_);
lean_inc(v_toSeq_1018_);
lean_inc(v_toFunctor_1017_);
lean_dec(v_toApplicative_1013_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1074_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1033_; 
v___f_1024_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1025_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1017_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toFunctor_1017_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toFunctor_1017_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___f_1026_);
lean_ctor_set(v___x_1028_, 1, v___f_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeqRight_1020_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toSeqLeft_1019_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toSeq_1018_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 4, v___f_1029_);
lean_ctor_set(v___x_1022_, 3, v___f_1030_);
lean_ctor_set(v___x_1022_, 2, v___f_1031_);
lean_ctor_set(v___x_1022_, 1, v___f_1024_);
lean_ctor_set(v___x_1022_, 0, v___x_1028_);
v___x_1033_ = v___x_1022_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___f_1024_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v___f_1031_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___f_1029_);
v___x_1033_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___f_1025_);
lean_ctor_set(v___x_1015_, 0, v___x_1033_);
v___x_1035_ = v___x_1015_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___f_1025_);
v___x_1035_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v_toApplicative_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1070_; 
v___x_1036_ = l_StateRefT_x27_instMonad___redArg(v___x_1035_);
v_toApplicative_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v___x_1036_, 1);
lean_dec(v_unused_1071_);
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1070_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_toApplicative_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1070_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_toFunctor_1041_; lean_object* v_toSeq_1042_; lean_object* v_toSeqLeft_1043_; lean_object* v_toSeqRight_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1068_; 
v_toFunctor_1041_ = lean_ctor_get(v_toApplicative_1037_, 0);
v_toSeq_1042_ = lean_ctor_get(v_toApplicative_1037_, 2);
v_toSeqLeft_1043_ = lean_ctor_get(v_toApplicative_1037_, 3);
v_toSeqRight_1044_ = lean_ctor_get(v_toApplicative_1037_, 4);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_toApplicative_1037_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_dec(v_unused_1069_);
v___x_1046_ = v_toApplicative_1037_;
v_isShared_1047_ = v_isSharedCheck_1068_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_toSeqRight_1044_);
lean_inc(v_toSeqLeft_1043_);
lean_inc(v_toSeq_1042_);
lean_inc(v_toFunctor_1041_);
lean_dec(v_toApplicative_1037_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1068_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1057_; 
v___f_1048_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1049_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1041_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toFunctor_1041_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toFunctor_1041_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___f_1050_);
lean_ctor_set(v___x_1052_, 1, v___f_1051_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeqRight_1044_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeqLeft_1043_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeq_1042_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v___f_1053_);
lean_ctor_set(v___x_1046_, 3, v___f_1054_);
lean_ctor_set(v___x_1046_, 2, v___f_1055_);
lean_ctor_set(v___x_1046_, 1, v___f_1048_);
lean_ctor_set(v___x_1046_, 0, v___x_1052_);
v___x_1057_ = v___x_1046_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v___f_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v___f_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v___f_1053_);
v___x_1057_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___f_1049_);
lean_ctor_set(v___x_1039_, 0, v___x_1057_);
v___x_1059_ = v___x_1039_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___f_1049_);
v___x_1059_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_49416__overap_1064_; lean_object* v___x_1065_; 
v___x_1060_ = l_StateRefT_x27_instMonad___redArg(v___x_1059_);
v___x_1061_ = l_StateRefT_x27_instMonad___redArg(v___x_1060_);
v___x_1062_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1063_ = l_instInhabitedOfMonad___redArg(v___x_1061_, v___x_1062_);
v___x_49416__overap_1064_ = lean_panic_fn_borrowed(v___x_1063_, v_msg_977_);
lean_dec(v___x_1063_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc(v___y_978_);
v___x_1065_ = lean_apply_9(v___x_49416__overap_1064_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_1065_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
return v_res_1094_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1099_ = lean_unsigned_to_nat(53u);
v___x_1100_ = lean_unsigned_to_nat(62u);
v___x_1101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1103_ = l_mkPanicMessageWithDecl(v___x_1102_, v___x_1101_, v___x_1100_, v___x_1099_, v___x_1098_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1104_, size_t v_i_1105_, lean_object* v_bs_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1105_, v_sz_1104_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_bs_1106_);
return v___x_1117_;
}
else
{
lean_object* v_v_1118_; lean_object* v___x_1119_; lean_object* v_bs_x27_1120_; lean_object* v_a_1122_; lean_object* v___x_1127_; 
v_v_1118_ = lean_array_uget(v_bs_1106_, v_i_1105_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v_bs_x27_1120_ = lean_array_uset(v_bs_1106_, v_i_1105_, v___x_1119_);
v___x_1127_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1118_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
if (lean_obj_tag(v_a_1128_) == 6)
{
lean_object* v_val_1129_; lean_object* v_numFields_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; 
v_val_1129_ = lean_ctor_get(v_a_1128_, 0);
lean_inc_ref(v_val_1129_);
lean_dec_ref_known(v_a_1128_, 1);
v_numFields_1130_ = lean_ctor_get(v_val_1129_, 4);
lean_inc(v_numFields_1130_);
lean_dec_ref(v_val_1129_);
v___x_1131_ = 0;
v___x_1132_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1132_, 0, v_numFields_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1119_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*2, v___x_1131_);
v_a_1122_ = v___x_1132_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_a_1128_);
v___x_1133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1134_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1133_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v_a_1122_ = v_a_1135_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_bs_x27_1120_);
v_a_1136_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1134_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_bs_x27_1120_);
v_a_1144_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1127_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1127_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
v___jp_1121_:
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1105_, v___x_1123_);
v___x_1125_ = lean_array_uset(v_bs_x27_1120_, v_i_1105_, v_a_1122_);
v_i_1105_ = v___x_1124_;
v_bs_1106_ = v___x_1125_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_bs_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1164_, v_i_boxed_1165_, v_bs_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1166_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1167_; lean_object* v_dummy_1168_; 
v___x_1167_ = lean_box(0);
v_dummy_1168_ = l_Lean_Expr_sort___override(v___x_1167_);
return v_dummy_1168_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_unsigned_to_nat(16u);
v___x_1171_ = lean_mk_array(v___x_1170_, v___x_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1177_, uint8_t v_alsoCasesOn_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_Expr_isApp(v_e_1177_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_e_1177_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Expr_getAppFn(v_e_1177_);
if (lean_obj_tag(v___x_1194_) == 4)
{
lean_object* v_declName_1195_; lean_object* v_us_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1351_; 
v_declName_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_n(v_declName_1195_, 2);
v_us_1196_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_us_1196_);
lean_dec_ref_known(v___x_1194_, 2);
v___x_1197_ = l_Lean_instInhabitedExpr;
v___x_1198_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1195_, v___y_1186_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1351_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1351_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
if (lean_obj_tag(v_a_1199_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1244_; 
v_val_1203_ = lean_ctor_get(v_a_1199_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1199_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1205_ = v_a_1199_;
v_isShared_1206_ = v_isSharedCheck_1244_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_val_1203_);
lean_dec(v_a_1199_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1244_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_dummy_1207_; lean_object* v_nargs_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_args_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_dummy_1207_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1208_ = l_Lean_Expr_getAppNumArgs(v_e_1177_);
lean_inc(v_nargs_1208_);
v___x_1209_ = lean_mk_array(v_nargs_1208_, v_dummy_1207_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_sub(v_nargs_1208_, v___x_1210_);
lean_dec(v_nargs_1208_);
v_args_1212_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1177_, v___x_1209_, v___x_1211_);
v___x_1213_ = lean_array_get_size(v_args_1212_);
v___x_1214_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1203_);
v___x_1215_ = lean_nat_dec_lt(v___x_1213_, v___x_1214_);
lean_dec(v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v_numParams_1216_; lean_object* v_numDiscrs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v_numParams_1216_ = lean_ctor_get(v_val_1203_, 0);
v_numDiscrs_1217_ = lean_ctor_get(v_val_1203_, 1);
v___x_1218_ = lean_array_mk(v_us_1196_);
v___x_1219_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1216_);
v___x_1220_ = l_Array_extract___redArg(v_args_1212_, v___x_1219_, v_numParams_1216_);
v___x_1221_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1203_);
v___x_1222_ = lean_array_get(v___x_1197_, v_args_1212_, v___x_1221_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_nat_add(v_numParams_1216_, v___x_1210_);
v___x_1224_ = lean_nat_add(v___x_1223_, v_numDiscrs_1217_);
lean_inc(v___x_1224_);
lean_inc_ref_n(v_args_1212_, 2);
v___x_1225_ = l_Array_toSubarray___redArg(v_args_1212_, v___x_1223_, v___x_1224_);
v___x_1226_ = l_Subarray_copy___redArg(v___x_1225_);
v___x_1227_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1203_);
v___x_1228_ = lean_nat_add(v___x_1224_, v___x_1227_);
lean_dec(v___x_1227_);
lean_inc(v___x_1228_);
v___x_1229_ = l_Array_toSubarray___redArg(v_args_1212_, v___x_1224_, v___x_1228_);
v___x_1230_ = l_Subarray_copy___redArg(v___x_1229_);
v___x_1231_ = l_Array_toSubarray___redArg(v_args_1212_, v___x_1228_, v___x_1213_);
v___x_1232_ = l_Subarray_copy___redArg(v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1233_, 0, v_val_1203_);
lean_ctor_set(v___x_1233_, 1, v_declName_1195_);
lean_ctor_set(v___x_1233_, 2, v___x_1218_);
lean_ctor_set(v___x_1233_, 3, v___x_1220_);
lean_ctor_set(v___x_1233_, 4, v___x_1222_);
lean_ctor_set(v___x_1233_, 5, v___x_1226_);
lean_ctor_set(v___x_1233_, 6, v___x_1230_);
lean_ctor_set(v___x_1233_, 7, v___x_1232_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1233_);
v___x_1235_ = v___x_1205_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1235_);
v___x_1237_ = v___x_1201_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec_ref(v_args_1212_);
lean_del_object(v___x_1205_);
lean_dec(v_val_1203_);
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
v___x_1240_ = lean_box(0);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1240_);
v___x_1242_ = v___x_1201_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; 
lean_del_object(v___x_1201_);
lean_dec(v_a_1199_);
v___x_1245_ = lean_st_ref_get(v___y_1186_);
if (v_alsoCasesOn_1178_ == 0)
{
lean_dec(v___x_1245_);
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
lean_dec_ref(v_e_1177_);
goto v___jp_1188_;
}
else
{
lean_object* v_env_1246_; uint8_t v___x_1247_; 
v_env_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_env_1246_);
lean_dec(v___x_1245_);
lean_inc(v_declName_1195_);
v___x_1247_ = l_Lean_isCasesOnRecursor(v_env_1246_, v_declName_1195_);
if (v___x_1247_ == 0)
{
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
lean_dec_ref(v_e_1177_);
goto v___jp_1188_;
}
else
{
lean_object* v_indName_1248_; lean_object* v___x_1249_; 
v_indName_1248_ = l_Lean_Name_getPrefix(v_declName_1195_);
v___x_1249_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1248_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1342_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1342_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1342_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
if (lean_obj_tag(v_a_1250_) == 5)
{
lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1337_; 
v_val_1254_ = lean_ctor_get(v_a_1250_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_1250_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1256_ = v_a_1250_;
v_isShared_1257_ = v_isSharedCheck_1337_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_dec(v_a_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1337_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_toConstantVal_1258_; lean_object* v_numParams_1259_; lean_object* v_numIndices_1260_; lean_object* v_ctors_1261_; lean_object* v_nargs_1262_; lean_object* v_dummy_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_args_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_toConstantVal_1258_ = lean_ctor_get(v_val_1254_, 0);
lean_inc_ref(v_toConstantVal_1258_);
v_numParams_1259_ = lean_ctor_get(v_val_1254_, 1);
lean_inc(v_numParams_1259_);
v_numIndices_1260_ = lean_ctor_get(v_val_1254_, 2);
lean_inc(v_numIndices_1260_);
v_ctors_1261_ = lean_ctor_get(v_val_1254_, 4);
lean_inc(v_ctors_1261_);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v_e_1177_);
v_dummy_1263_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1262_);
v___x_1264_ = lean_mk_array(v_nargs_1262_, v_dummy_1263_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_sub(v_nargs_1262_, v___x_1265_);
lean_dec(v_nargs_1262_);
v_args_1267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1177_, v___x_1264_, v___x_1266_);
v___x_1268_ = lean_nat_add(v_numParams_1259_, v___x_1265_);
v___x_1269_ = lean_nat_add(v___x_1268_, v_numIndices_1260_);
v___x_1270_ = lean_nat_add(v___x_1269_, v___x_1265_);
lean_dec(v___x_1269_);
v___x_1271_ = l_Lean_InductiveVal_numCtors(v_val_1254_);
lean_dec_ref(v_val_1254_);
v___x_1272_ = lean_nat_add(v___x_1270_, v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = lean_array_get_size(v_args_1267_);
v___x_1274_ = lean_nat_dec_le(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec(v___x_1272_);
lean_dec(v___x_1270_);
lean_dec(v___x_1268_);
lean_dec_ref(v_args_1267_);
lean_dec(v_ctors_1261_);
lean_dec(v_numIndices_1260_);
lean_dec(v_numParams_1259_);
lean_dec_ref(v_toConstantVal_1258_);
lean_del_object(v___x_1256_);
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
v___x_1275_ = lean_box(0);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1275_);
v___x_1277_ = v___x_1252_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v___x_1279_; lean_object* v_params_1280_; lean_object* v_motive_1281_; lean_object* v_discrs_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_discrInfos_1285_; lean_object* v_alts_1286_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v_lower_1328_; lean_object* v_upper_1329_; uint8_t v___x_1336_; 
lean_del_object(v___x_1252_);
v___x_1279_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1259_);
lean_inc_ref_n(v_args_1267_, 3);
v_params_1280_ = l_Array_toSubarray___redArg(v_args_1267_, v___x_1279_, v_numParams_1259_);
v_motive_1281_ = lean_array_get(v___x_1197_, v_args_1267_, v_numParams_1259_);
lean_dec(v_numParams_1259_);
lean_inc(v___x_1270_);
v_discrs_1282_ = l_Array_toSubarray___redArg(v_args_1267_, v___x_1268_, v___x_1270_);
v___x_1283_ = lean_nat_add(v_numIndices_1260_, v___x_1265_);
lean_dec(v_numIndices_1260_);
v___x_1284_ = lean_box(0);
v_discrInfos_1285_ = lean_mk_array(v___x_1283_, v___x_1284_);
lean_inc(v___x_1272_);
v_alts_1286_ = l_Array_toSubarray___redArg(v_args_1267_, v___x_1270_, v___x_1272_);
v___x_1336_ = lean_nat_dec_le(v___x_1272_, v___x_1279_);
if (v___x_1336_ == 0)
{
v_lower_1328_ = v___x_1272_;
v_upper_1329_ = v___x_1273_;
goto v___jp_1327_;
}
else
{
lean_dec(v___x_1272_);
v_lower_1328_ = v___x_1279_;
v_upper_1329_ = v___x_1273_;
goto v___jp_1327_;
}
v___jp_1287_:
{
lean_object* v___x_1290_; size_t v_sz_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_array_mk(v_ctors_1261_);
v_sz_1291_ = lean_array_size(v___x_1290_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1291_, v___x_1292_, v___x_1290_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1318_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1318_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1318_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_start_1298_; lean_object* v_stop_1299_; lean_object* v_start_1300_; lean_object* v_stop_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v_start_1298_ = lean_ctor_get(v_params_1280_, 1);
v_stop_1299_ = lean_ctor_get(v_params_1280_, 2);
v_start_1300_ = lean_ctor_get(v_discrs_1282_, 1);
v_stop_1301_ = lean_ctor_get(v_discrs_1282_, 2);
v___x_1302_ = lean_nat_sub(v_stop_1299_, v_start_1298_);
v___x_1303_ = lean_nat_sub(v_stop_1301_, v_start_1300_);
v___x_1304_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v_a_1294_);
lean_ctor_set(v___x_1305_, 3, v___y_1289_);
lean_ctor_set(v___x_1305_, 4, v_discrInfos_1285_);
lean_ctor_set(v___x_1305_, 5, v___x_1304_);
v___x_1306_ = lean_array_mk(v_us_1196_);
v___x_1307_ = l_Subarray_copy___redArg(v_params_1280_);
v___x_1308_ = l_Subarray_copy___redArg(v_discrs_1282_);
v___x_1309_ = l_Subarray_copy___redArg(v_alts_1286_);
v___x_1310_ = l_Subarray_copy___redArg(v___y_1288_);
v___x_1311_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1305_);
lean_ctor_set(v___x_1311_, 1, v_declName_1195_);
lean_ctor_set(v___x_1311_, 2, v___x_1306_);
lean_ctor_set(v___x_1311_, 3, v___x_1307_);
lean_ctor_set(v___x_1311_, 4, v_motive_1281_);
lean_ctor_set(v___x_1311_, 5, v___x_1308_);
lean_ctor_set(v___x_1311_, 6, v___x_1309_);
lean_ctor_set(v___x_1311_, 7, v___x_1310_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1311_);
v___x_1313_ = v___x_1256_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1313_);
v___x_1315_ = v___x_1296_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_alts_1286_);
lean_dec_ref(v_discrInfos_1285_);
lean_dec_ref(v_discrs_1282_);
lean_dec(v_motive_1281_);
lean_dec_ref(v_params_1280_);
lean_del_object(v___x_1256_);
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
v_a_1319_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1293_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1293_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
v___jp_1327_:
{
lean_object* v_levelParams_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_levelParams_1330_ = lean_ctor_get(v_toConstantVal_1258_, 1);
lean_inc(v_levelParams_1330_);
lean_dec_ref(v_toConstantVal_1258_);
v___x_1331_ = l_Array_toSubarray___redArg(v_args_1267_, v_lower_1328_, v_upper_1329_);
v___x_1332_ = l_List_lengthTR___redArg(v_levelParams_1330_);
lean_dec(v_levelParams_1330_);
v___x_1333_ = l_List_lengthTR___redArg(v_us_1196_);
v___x_1334_ = lean_nat_dec_eq(v___x_1332_, v___x_1333_);
lean_dec(v___x_1333_);
lean_dec(v___x_1332_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1288_ = v___x_1331_;
v___y_1289_ = v___x_1335_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___x_1331_;
v___y_1289_ = v___x_1284_;
goto v___jp_1287_;
}
}
}
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_a_1250_);
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
lean_dec_ref(v_e_1177_);
v___x_1338_ = lean_box(0);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1338_);
v___x_1340_ = v___x_1252_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
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
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_us_1196_);
lean_dec(v_declName_1195_);
lean_dec_ref(v_e_1177_);
v_a_1343_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1249_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1249_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
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
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_e_1177_);
goto v___jp_1188_;
}
}
v___jp_1188_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1352_, lean_object* v_alsoCasesOn_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1363_; lean_object* v_res_1364_; 
v_alsoCasesOn_boxed_1363_ = lean_unbox(v_alsoCasesOn_1353_);
v_res_1364_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1352_, v_alsoCasesOn_boxed_1363_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v_b_1370_, lean_object* v_c_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc(v___y_1366_);
v___x_1377_ = lean_apply_11(v_k_1365_, v_b_1370_, v_c_1371_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, lean_box(0));
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v_b_1383_, lean_object* v_c_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v_b_1383_, v_c_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec(v___y_1379_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1391_, lean_object* v_maxFVars_1392_, lean_object* v_k_1393_, uint8_t v_cleanupAnnotations_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___f_1404_; uint8_t v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc(v___y_1395_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1404_, 0, v_k_1393_);
lean_closure_set(v___f_1404_, 1, v___y_1395_);
lean_closure_set(v___f_1404_, 2, v___y_1396_);
lean_closure_set(v___f_1404_, 3, v___y_1397_);
lean_closure_set(v___f_1404_, 4, v___y_1398_);
v___x_1405_ = 1;
v___x_1406_ = 0;
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_maxFVars_1392_);
v___x_1408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1391_, v___x_1405_, v___x_1406_, v___x_1405_, v___x_1406_, v___x_1407_, v___f_1404_, v_cleanupAnnotations_1394_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref_known(v___x_1407_, 1);
if (lean_obj_tag(v___x_1408_) == 0)
{
return v___x_1408_;
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1417_, lean_object* v_maxFVars_1418_, lean_object* v_k_1419_, lean_object* v_cleanupAnnotations_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1430_; lean_object* v_res_1431_; 
v_cleanupAnnotations_boxed_1430_ = lean_unbox(v_cleanupAnnotations_1420_);
v_res_1431_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1417_, v_maxFVars_1418_, v_k_1419_, v_cleanupAnnotations_boxed_1430_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc(v___y_1433_);
v___x_1443_ = lean_apply_10(v_k_1432_, v_b_1437_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, lean_box(0));
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v_b_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v___y_1445_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1456_, lean_object* v_type_1457_, lean_object* v_val_1458_, lean_object* v_k_1459_, uint8_t v_nondep_1460_, uint8_t v_kind_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; 
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc(v___y_1462_);
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1471_, 0, v_k_1459_);
lean_closure_set(v___f_1471_, 1, v___y_1462_);
lean_closure_set(v___f_1471_, 2, v___y_1463_);
lean_closure_set(v___f_1471_, 3, v___y_1464_);
lean_closure_set(v___f_1471_, 4, v___y_1465_);
v___x_1472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1456_, v_type_1457_, v_val_1458_, v___f_1471_, v_nondep_1460_, v_kind_1461_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1481_, lean_object* v_type_1482_, lean_object* v_val_1483_, lean_object* v_k_1484_, lean_object* v_nondep_1485_, lean_object* v_kind_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v_nondep_boxed_1496_; uint8_t v_kind_boxed_1497_; lean_object* v_res_1498_; 
v_nondep_boxed_1496_ = lean_unbox(v_nondep_1485_);
v_kind_boxed_1497_ = lean_unbox(v_kind_1486_);
v_res_1498_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1481_, v_type_1482_, v_val_1483_, v_k_1484_, v_nondep_boxed_1496_, v_kind_boxed_1497_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v___y_1487_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1499_, uint8_t v_usedLetOnly_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v_x_1501_);
v___x_1511_ = lean_apply_10(v_k_1499_, v_x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_mk_empty_array_with_capacity(v___x_1513_);
v___x_1515_ = lean_array_push(v___x_1514_, v_x_1501_);
v___x_1516_ = 0;
v___x_1517_ = 1;
v___x_1518_ = l_Lean_Meta_mkLetFVars(v___x_1515_, v_a_1512_, v_usedLetOnly_1500_, v___x_1516_, v___x_1517_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec_ref(v___x_1515_);
return v___x_1518_;
}
else
{
lean_dec_ref(v_x_1501_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1519_, lean_object* v_usedLetOnly_1520_, lean_object* v_x_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v_usedLetOnly_boxed_1531_; lean_object* v_res_1532_; 
v_usedLetOnly_boxed_1531_ = lean_unbox(v_usedLetOnly_1520_);
v_res_1532_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1519_, v_usedLetOnly_boxed_1531_, v_x_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v___y_1522_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1533_, lean_object* v_type_1534_, lean_object* v_val_1535_, lean_object* v_k_1536_, uint8_t v_nondep_1537_, uint8_t v_kind_1538_, uint8_t v_usedLetOnly_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_box(v_usedLetOnly_1539_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1550_, 0, v_k_1536_);
lean_closure_set(v___f_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1533_, v_type_1534_, v_val_1535_, v___f_1550_, v_nondep_1537_, v_kind_1538_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1552_, lean_object* v_type_1553_, lean_object* v_val_1554_, lean_object* v_k_1555_, lean_object* v_nondep_1556_, lean_object* v_kind_1557_, lean_object* v_usedLetOnly_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_nondep_boxed_1568_; uint8_t v_kind_boxed_1569_; uint8_t v_usedLetOnly_boxed_1570_; lean_object* v_res_1571_; 
v_nondep_boxed_1568_ = lean_unbox(v_nondep_1556_);
v_kind_boxed_1569_ = lean_unbox(v_kind_1557_);
v_usedLetOnly_boxed_1570_ = lean_unbox(v_usedLetOnly_1558_);
v_res_1571_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1552_, v_type_1553_, v_val_1554_, v_k_1555_, v_nondep_boxed_1568_, v_kind_boxed_1569_, v_usedLetOnly_boxed_1570_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1572_, uint8_t v_bi_1573_, lean_object* v_type_1574_, lean_object* v_k_1575_, uint8_t v_kind_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc(v___y_1577_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1586_, 0, v_k_1575_);
lean_closure_set(v___f_1586_, 1, v___y_1577_);
lean_closure_set(v___f_1586_, 2, v___y_1578_);
lean_closure_set(v___f_1586_, 3, v___y_1579_);
lean_closure_set(v___f_1586_, 4, v___y_1580_);
v___x_1587_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1572_, v_bi_1573_, v_type_1574_, v___f_1586_, v_kind_1576_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1587_) == 0)
{
return v___x_1587_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1596_, lean_object* v_bi_1597_, lean_object* v_type_1598_, lean_object* v_k_1599_, lean_object* v_kind_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_bi_boxed_1610_; uint8_t v_kind_boxed_1611_; lean_object* v_res_1612_; 
v_bi_boxed_1610_ = lean_unbox(v_bi_1597_);
v_kind_boxed_1611_ = lean_unbox(v_kind_1600_);
v_res_1612_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1596_, v_bi_boxed_1610_, v_type_1598_, v_k_1599_, v_kind_boxed_1611_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc(v___y_1614_);
v___x_1623_ = lean_apply_9(v_k_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, lean_box(0));
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___y_1625_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1635_, uint8_t v_allowLevelAssignments_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___f_1646_; lean_object* v___x_1647_; 
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc(v___y_1637_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1646_, 0, v_k_1635_);
lean_closure_set(v___f_1646_, 1, v___y_1637_);
lean_closure_set(v___f_1646_, 2, v___y_1638_);
lean_closure_set(v___f_1646_, 3, v___y_1639_);
lean_closure_set(v___f_1646_, 4, v___y_1640_);
v___x_1647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1636_, v___f_1646_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1647_) == 0)
{
return v___x_1647_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1656_, lean_object* v_allowLevelAssignments_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1667_; lean_object* v_res_1668_; 
v_allowLevelAssignments_boxed_1667_ = lean_unbox(v_allowLevelAssignments_1657_);
v_res_1668_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1656_, v_allowLevelAssignments_boxed_1667_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec(v___y_1658_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1669_, lean_object* v_x_1670_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_box(0);
return v___x_1671_;
}
else
{
lean_object* v_key_1672_; lean_object* v_value_1673_; lean_object* v_tail_1674_; uint8_t v___x_1675_; 
v_key_1672_ = lean_ctor_get(v_x_1670_, 0);
v_value_1673_ = lean_ctor_get(v_x_1670_, 1);
v_tail_1674_ = lean_ctor_get(v_x_1670_, 2);
v___x_1675_ = lean_expr_eqv(v_key_1672_, v_a_1669_);
if (v___x_1675_ == 0)
{
v_x_1670_ = v_tail_1674_;
goto _start;
}
else
{
lean_object* v___x_1677_; 
lean_inc(v_value_1673_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_value_1673_);
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1678_, v_x_1679_);
lean_dec(v_x_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_buckets_1683_; lean_object* v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v_fold_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_buckets_1683_ = lean_ctor_get(v_m_1681_, 1);
v___x_1684_ = lean_array_get_size(v_buckets_1683_);
v___x_1685_ = l_Lean_Expr_hash(v_a_1682_);
v___x_1686_ = 32ULL;
v___x_1687_ = lean_uint64_shift_right(v___x_1685_, v___x_1686_);
v_fold_1688_ = lean_uint64_xor(v___x_1685_, v___x_1687_);
v___x_1689_ = 16ULL;
v___x_1690_ = lean_uint64_shift_right(v_fold_1688_, v___x_1689_);
v___x_1691_ = lean_uint64_xor(v_fold_1688_, v___x_1690_);
v___x_1692_ = lean_uint64_to_usize(v___x_1691_);
v___x_1693_ = lean_usize_of_nat(v___x_1684_);
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_sub(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_usize_land(v___x_1692_, v___x_1695_);
v___x_1697_ = lean_array_uget_borrowed(v_buckets_1683_, v___x_1696_);
v___x_1698_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1682_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1699_, v_a_1700_);
lean_dec_ref(v_a_1700_);
lean_dec_ref(v_m_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1702_, lean_object* v_opt_1703_){
_start:
{
lean_object* v_name_1704_; lean_object* v_defValue_1705_; lean_object* v_map_1706_; lean_object* v___x_1707_; 
v_name_1704_ = lean_ctor_get(v_opt_1703_, 0);
v_defValue_1705_ = lean_ctor_get(v_opt_1703_, 1);
v_map_1706_ = lean_ctor_get(v_opts_1702_, 0);
v___x_1707_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1706_, v_name_1704_);
if (lean_obj_tag(v___x_1707_) == 0)
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_unbox(v_defValue_1705_);
return v___x_1708_;
}
else
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1707_, 1);
if (lean_obj_tag(v_val_1709_) == 1)
{
uint8_t v_v_1710_; 
v_v_1710_ = lean_ctor_get_uint8(v_val_1709_, 0);
lean_dec_ref_known(v_val_1709_, 0);
return v_v_1710_;
}
else
{
uint8_t v___x_1711_; 
lean_dec(v_val_1709_);
v___x_1711_ = lean_unbox(v_defValue_1705_);
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1712_, lean_object* v_opt_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1712_, v_opt_1713_);
lean_dec_ref(v_opt_1713_);
lean_dec_ref(v_opts_1712_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1716_, lean_object* v_b_1717_){
_start:
{
lean_object* v_array_1718_; lean_object* v_start_1719_; lean_object* v_stop_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1733_; 
v_array_1718_ = lean_ctor_get(v_a_1716_, 0);
v_start_1719_ = lean_ctor_get(v_a_1716_, 1);
v_stop_1720_ = lean_ctor_get(v_a_1716_, 2);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1722_ = v_a_1716_;
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_stop_1720_);
lean_inc(v_start_1719_);
lean_inc(v_array_1718_);
lean_dec(v_a_1716_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_lt(v_start_1719_, v_stop_1720_);
if (v___x_1724_ == 0)
{
lean_del_object(v___x_1722_);
lean_dec(v_stop_1720_);
lean_dec(v_start_1719_);
lean_dec_ref(v_array_1718_);
return v_b_1717_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_start_1719_, v___x_1725_);
lean_inc_ref(v_array_1718_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1726_);
v___x_1728_ = v___x_1722_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_array_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_stop_1720_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_array_fget(v_array_1718_, v_start_1719_);
lean_dec(v_start_1719_);
lean_dec_ref(v_array_1718_);
v___x_1730_ = lean_array_push(v_b_1717_, v___x_1729_);
v_a_1716_ = v___x_1728_;
v_b_1717_ = v___x_1730_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1734_, lean_object* v_recFnName_1735_, lean_object* v_fixedPrefixSize_1736_, lean_object* v_F_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_expr_instantiate1(v_body_1734_, v_x_1738_);
v___x_1749_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1735_, v_fixedPrefixSize_1736_, v_F_1737_, v___x_1748_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_array_push(v___x_1752_, v_x_1738_);
v___x_1754_ = 0;
v___x_1755_ = 1;
v___x_1756_ = 1;
v___x_1757_ = l_Lean_Meta_mkLambdaFVars(v___x_1753_, v_a_1750_, v___x_1754_, v___x_1755_, v___x_1754_, v___x_1755_, v___x_1756_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec_ref(v___x_1753_);
return v___x_1757_;
}
else
{
lean_dec_ref(v_x_1738_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1758_, lean_object* v_recFnName_1759_, lean_object* v_fixedPrefixSize_1760_, lean_object* v_F_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1758_, v_recFnName_1759_, v_fixedPrefixSize_1760_, v_F_1761_, v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v_body_1758_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1773_, lean_object* v_recFnName_1774_, lean_object* v_fixedPrefixSize_1775_, lean_object* v_F_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_expr_instantiate1(v_body_1773_, v_x_1777_);
v___x_1788_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1774_, v_fixedPrefixSize_1775_, v_F_1776_, v___x_1787_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_mk_empty_array_with_capacity(v___x_1790_);
v___x_1792_ = lean_array_push(v___x_1791_, v_x_1777_);
v___x_1793_ = 0;
v___x_1794_ = 1;
v___x_1795_ = 1;
v___x_1796_ = l_Lean_Meta_mkForallFVars(v___x_1792_, v_a_1789_, v___x_1793_, v___x_1794_, v___x_1794_, v___x_1795_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec_ref(v___x_1792_);
return v___x_1796_;
}
else
{
lean_dec_ref(v_x_1777_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1797_, lean_object* v_recFnName_1798_, lean_object* v_fixedPrefixSize_1799_, lean_object* v_F_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1797_, v_recFnName_1798_, v_fixedPrefixSize_1799_, v_F_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v_body_1797_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1812_, lean_object* v_recFnName_1813_, lean_object* v_fixedPrefixSize_1814_, lean_object* v_F_1815_, lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1812_, v_recFnName_1813_, v_fixedPrefixSize_1814_, v_F_1815_, v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v_x_1816_);
lean_dec_ref(v_body_1812_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1829_, lean_object* v_fixedPrefixSize_1830_, lean_object* v_F_1831_, size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_bs_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_usize_dec_lt(v_i_1833_, v_sz_1832_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v_F_1831_);
lean_dec(v_fixedPrefixSize_1830_);
lean_dec(v_recFnName_1829_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_bs_1834_);
return v___x_1845_;
}
else
{
lean_object* v_v_1846_; lean_object* v___x_1847_; lean_object* v_bs_x27_1848_; lean_object* v___x_1849_; 
v_v_1846_ = lean_array_uget(v_bs_1834_, v_i_1833_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v_bs_x27_1848_ = lean_array_uset(v_bs_1834_, v_i_1833_, v___x_1847_);
lean_inc_ref(v_F_1831_);
lean_inc(v_fixedPrefixSize_1830_);
lean_inc(v_recFnName_1829_);
v___x_1849_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1829_, v_fixedPrefixSize_1830_, v_F_1831_, v_v_1846_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = lean_usize_add(v_i_1833_, v___x_1851_);
v___x_1853_ = lean_array_uset(v_bs_x27_1848_, v_i_1833_, v_a_1850_);
v_i_1833_ = v___x_1852_;
v_bs_1834_ = v___x_1853_;
goto _start;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_bs_x27_1848_);
lean_dec_ref(v_F_1831_);
lean_dec(v_fixedPrefixSize_1830_);
lean_dec(v_recFnName_1829_);
v_a_1855_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1849_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1849_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_cls_1870_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1872_ = l_Lean_Name_append(v___x_1871_, v_cls_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1876_, lean_object* v_fixedPrefixSize_1877_, lean_object* v_F_1878_, lean_object* v_e_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1901_ = l_Lean_Expr_getAppNumArgs(v_e_1879_);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_fixedPrefixSize_1877_, v___x_1902_);
v___x_1904_ = lean_nat_dec_lt(v___x_1901_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v_dummy_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_args_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1905_ = l_Lean_instInhabitedExpr;
v_dummy_1906_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1901_);
v___x_1907_ = lean_mk_array(v___x_1901_, v_dummy_1906_);
v___x_1908_ = lean_nat_sub(v___x_1901_, v___x_1902_);
lean_dec(v___x_1901_);
v_args_1909_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1879_, v___x_1907_, v___x_1908_);
v___x_1910_ = lean_array_get_borrowed(v___x_1905_, v_args_1909_, v_fixedPrefixSize_1877_);
lean_inc(v___x_1910_);
lean_inc_ref(v_F_1878_);
lean_inc(v_fixedPrefixSize_1877_);
lean_inc(v_recFnName_1876_);
v___x_1911_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1876_, v_fixedPrefixSize_1877_, v_F_1878_, v___x_1910_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
lean_inc_ref(v_F_1878_);
v___x_1913_ = l_Lean_Expr_app___override(v_F_1878_, v_a_1912_);
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
lean_inc(v_a_1885_);
lean_inc_ref(v_a_1884_);
lean_inc_ref(v___x_1913_);
v___x_1914_ = lean_infer_type(v___x_1913_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
lean_inc(v_a_1885_);
lean_inc_ref(v_a_1884_);
v___x_1916_ = lean_whnf(v_a_1915_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l_Lean_Expr_bindingDomain_x21(v_a_1917_);
lean_dec(v_a_1917_);
v___x_1919_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1918_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v_lower_1923_; lean_object* v_upper_1924_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Expr_app___override(v___x_1913_, v_a_1920_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_array_get_size(v_args_1909_);
v___x_1950_ = lean_nat_dec_le(v___x_1903_, v___x_1948_);
if (v___x_1950_ == 0)
{
v_lower_1923_ = v___x_1903_;
v_upper_1924_ = v___x_1949_;
goto v___jp_1922_;
}
else
{
lean_dec(v___x_1903_);
v_lower_1923_ = v___x_1948_;
v_upper_1924_ = v___x_1949_;
goto v___jp_1922_;
}
v___jp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; size_t v_sz_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1925_ = l_Array_toSubarray___redArg(v_args_1909_, v_lower_1923_, v_upper_1924_);
v___x_1926_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1927_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1925_, v___x_1926_);
v_sz_1928_ = lean_array_size(v___x_1927_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1876_, v_fixedPrefixSize_1877_, v_F_1878_, v_sz_1928_, v___x_1929_, v___x_1927_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = l_Lean_mkAppN(v___x_1921_, v_a_1931_);
lean_dec(v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v___x_1921_);
v_a_1940_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1930_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1930_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1913_);
lean_dec_ref(v_args_1909_);
lean_dec(v___x_1903_);
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
return v___x_1919_;
}
}
else
{
lean_dec_ref(v___x_1913_);
lean_dec_ref(v_args_1909_);
lean_dec(v___x_1903_);
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
return v___x_1916_;
}
}
else
{
lean_dec_ref(v___x_1913_);
lean_dec_ref(v_args_1909_);
lean_dec(v___x_1903_);
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
return v___x_1914_;
}
}
else
{
lean_dec_ref(v_args_1909_);
lean_dec(v___x_1903_);
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
return v___x_1911_;
}
}
else
{
lean_object* v_toCold_1951_; lean_object* v_options_1952_; uint8_t v_hasTrace_1953_; 
lean_dec(v___x_1903_);
lean_dec(v___x_1901_);
v_toCold_1951_ = lean_ctor_get(v_a_1886_, 0);
v_options_1952_ = lean_ctor_get(v_toCold_1951_, 2);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_options_1952_, sizeof(void*)*1);
if (v_hasTrace_1953_ == 0)
{
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
goto v___jp_1889_;
}
else
{
lean_object* v_inheritedTraceOptions_1954_; lean_object* v_cls_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_inheritedTraceOptions_1954_ = lean_ctor_get(v_toCold_1951_, 11);
v_cls_1955_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1954_, v_options_1952_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1879_);
v___x_1959_ = l_Lean_indentExpr(v_e_1879_);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1955_, v___x_1960_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
goto v___jp_1889_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_e_1879_);
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
v___jp_1889_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_Meta_etaExpand(v_e_1879_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1876_, v_fixedPrefixSize_1877_, v_F_1878_, v_a_1899_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1900_;
}
else
{
lean_dec_ref(v_F_1878_);
lean_dec(v_fixedPrefixSize_1877_);
lean_dec(v_recFnName_1876_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1970_, lean_object* v_fixedPrefixSize_1971_, lean_object* v_F_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 5)
{
lean_object* v_fn_1985_; lean_object* v_arg_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_fn_1985_ = lean_ctor_get(v_x_1973_, 0);
lean_inc_ref(v_fn_1985_);
v_arg_1986_ = lean_ctor_get(v_x_1973_, 1);
lean_inc_ref(v_arg_1986_);
lean_dec_ref_known(v_x_1973_, 2);
v___x_1987_ = lean_array_set(v_x_1974_, v_x_1975_, v_arg_1986_);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_nat_sub(v_x_1975_, v___x_1988_);
lean_dec(v_x_1975_);
v_x_1973_ = v_fn_1985_;
v_x_1974_ = v___x_1987_;
v_x_1975_ = v___x_1989_;
goto _start;
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_x_1975_);
lean_inc_ref(v_F_1972_);
lean_inc(v_fixedPrefixSize_1971_);
lean_inc(v_recFnName_1970_);
v___x_1991_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1970_, v_fixedPrefixSize_1971_, v_F_1972_, v_x_1973_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_sz_1993_ = lean_array_size(v_x_1974_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1970_, v_fixedPrefixSize_1971_, v_F_1972_, v_sz_1993_, v___x_1994_, v_x_1974_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = l_Lean_mkAppN(v_a_1992_, v_a_1996_);
lean_dec(v_a_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1992_);
v_a_2005_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1995_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1995_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_dec_ref(v_x_1974_);
lean_dec_ref(v_F_1972_);
lean_dec(v_fixedPrefixSize_1971_);
lean_dec(v_recFnName_1970_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2013_, lean_object* v_fixedPrefixSize_2014_, lean_object* v_F_2015_, lean_object* v_e_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Expr_isAppOf(v_e_2016_, v_recFnName_2013_);
if (v___x_2026_ == 0)
{
lean_object* v_dummy_2027_; lean_object* v_nargs_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_dummy_2027_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2028_ = l_Lean_Expr_getAppNumArgs(v_e_2016_);
lean_inc(v_nargs_2028_);
v___x_2029_ = lean_mk_array(v_nargs_2028_, v_dummy_2027_);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_sub(v_nargs_2028_, v___x_2030_);
lean_dec(v_nargs_2028_);
v___x_2032_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2013_, v_fixedPrefixSize_2014_, v_F_2015_, v_e_2016_, v___x_2029_, v___x_2031_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2013_, v_fixedPrefixSize_2014_, v_F_2015_, v_e_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2033_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2040_, lean_object* v_b_2041_, lean_object* v_recFnName_2042_, lean_object* v_fixedPrefixSize_2043_, uint8_t v___x_2044_, lean_object* v___x_2045_, lean_object* v_a_2046_, lean_object* v_e_2047_, lean_object* v_xs_2048_, lean_object* v_altBody_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = lean_array_get_size(v_xs_2048_);
v___x_2067_ = lean_nat_dec_eq(v___x_2066_, v___x_2045_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v_altBody_2049_);
lean_dec(v_fixedPrefixSize_2043_);
lean_dec(v_recFnName_2042_);
v___x_2068_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2069_ = l_Lean_indentExpr(v_a_2046_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = l_Lean_indentExpr(v_e_2047_);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2074_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_dec_ref(v_e_2047_);
lean_dec_ref(v_a_2046_);
goto v___jp_2059_;
}
v___jp_2059_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_array_get_borrowed(v___x_2040_, v_xs_2048_, v_b_2041_);
lean_inc(v___x_2060_);
v___x_2061_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2042_, v_fixedPrefixSize_2043_, v___x_2060_, v_altBody_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; uint8_t v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = 0;
v___x_2064_ = 1;
v___x_2065_ = l_Lean_Meta_mkLambdaFVars(v_xs_2048_, v_a_2062_, v___x_2063_, v___x_2044_, v___x_2063_, v___x_2044_, v___x_2064_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2065_;
}
else
{
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2084_ = _args[0];
lean_object* v_b_2085_ = _args[1];
lean_object* v_recFnName_2086_ = _args[2];
lean_object* v_fixedPrefixSize_2087_ = _args[3];
lean_object* v___x_2088_ = _args[4];
lean_object* v___x_2089_ = _args[5];
lean_object* v_a_2090_ = _args[6];
lean_object* v_e_2091_ = _args[7];
lean_object* v_xs_2092_ = _args[8];
lean_object* v_altBody_2093_ = _args[9];
lean_object* v___y_2094_ = _args[10];
lean_object* v___y_2095_ = _args[11];
lean_object* v___y_2096_ = _args[12];
lean_object* v___y_2097_ = _args[13];
lean_object* v___y_2098_ = _args[14];
lean_object* v___y_2099_ = _args[15];
lean_object* v___y_2100_ = _args[16];
lean_object* v___y_2101_ = _args[17];
lean_object* v___y_2102_ = _args[18];
_start:
{
uint8_t v___x_57422__boxed_2103_; lean_object* v_res_2104_; 
v___x_57422__boxed_2103_ = lean_unbox(v___x_2088_);
v_res_2104_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2084_, v_b_2085_, v_recFnName_2086_, v_fixedPrefixSize_2087_, v___x_57422__boxed_2103_, v___x_2089_, v_a_2090_, v_e_2091_, v_xs_2092_, v_altBody_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v_xs_2092_);
lean_dec(v___x_2089_);
lean_dec(v_b_2085_);
lean_dec_ref(v___x_2084_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2105_, lean_object* v_fixedPrefixSize_2106_, lean_object* v_e_2107_, lean_object* v_as_2108_, lean_object* v_bs_2109_, lean_object* v_i_2110_, lean_object* v_cs_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_array_get_size(v_as_2108_);
v___x_2122_ = lean_nat_dec_lt(v_i_2110_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_i_2110_);
lean_dec_ref(v_e_2107_);
lean_dec(v_fixedPrefixSize_2106_);
lean_dec(v_recFnName_2105_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_cs_2111_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_bs_2109_);
v___x_2125_ = lean_nat_dec_lt(v_i_2110_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_dec(v_i_2110_);
lean_dec_ref(v_e_2107_);
lean_dec(v_fixedPrefixSize_2106_);
lean_dec(v_recFnName_2105_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_cs_2111_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v_a_2128_; lean_object* v_b_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2127_ = l_Lean_instInhabitedExpr;
v_a_2128_ = lean_array_fget_borrowed(v_as_2108_, v_i_2110_);
v_b_2129_ = lean_array_fget_borrowed(v_bs_2109_, v_i_2110_);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v_b_2129_, v___x_2130_);
v___x_2132_ = lean_box(v___x_2125_);
lean_inc_ref(v_e_2107_);
lean_inc_n(v_a_2128_, 2);
lean_inc(v___x_2131_);
lean_inc(v_fixedPrefixSize_2106_);
lean_inc(v_recFnName_2105_);
lean_inc(v_b_2129_);
v___f_2133_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2133_, 0, v___x_2127_);
lean_closure_set(v___f_2133_, 1, v_b_2129_);
lean_closure_set(v___f_2133_, 2, v_recFnName_2105_);
lean_closure_set(v___f_2133_, 3, v_fixedPrefixSize_2106_);
lean_closure_set(v___f_2133_, 4, v___x_2132_);
lean_closure_set(v___f_2133_, 5, v___x_2131_);
lean_closure_set(v___f_2133_, 6, v_a_2128_);
lean_closure_set(v___f_2133_, 7, v_e_2107_);
v___x_2134_ = 0;
v___x_2135_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2128_, v___x_2131_, v___f_2133_, v___x_2134_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = lean_nat_add(v_i_2110_, v___x_2130_);
lean_dec(v_i_2110_);
v___x_2138_ = lean_array_push(v_cs_2111_, v_a_2136_);
v_i_2110_ = v___x_2137_;
v_cs_2111_ = v___x_2138_;
goto _start;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_cs_2111_);
lean_dec(v_i_2110_);
lean_dec_ref(v_e_2107_);
lean_dec(v_fixedPrefixSize_2106_);
lean_dec(v_recFnName_2105_);
v_a_2140_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2135_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2135_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2148_, lean_object* v_fixedPrefixSize_2149_, lean_object* v_F_2150_, lean_object* v_e_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
switch(lean_obj_tag(v_e_2151_))
{
case 6:
{
lean_object* v_binderName_2161_; lean_object* v_binderType_2162_; lean_object* v_body_2163_; uint8_t v_binderInfo_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; 
v_binderName_2161_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_binderName_2161_);
v_binderType_2162_ = lean_ctor_get(v_e_2151_, 1);
lean_inc_ref(v_binderType_2162_);
v_body_2163_ = lean_ctor_get(v_e_2151_, 2);
lean_inc_ref(v_body_2163_);
v_binderInfo_2164_ = lean_ctor_get_uint8(v_e_2151_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2151_, 3);
lean_inc_ref(v_F_2150_);
lean_inc(v_fixedPrefixSize_2149_);
lean_inc(v_recFnName_2148_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2165_, 0, v_body_2163_);
lean_closure_set(v___f_2165_, 1, v_recFnName_2148_);
lean_closure_set(v___f_2165_, 2, v_fixedPrefixSize_2149_);
lean_closure_set(v___f_2165_, 3, v_F_2150_);
v___x_2166_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_binderType_2162_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = 0;
v___x_2169_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2161_, v_binderInfo_2164_, v_a_2167_, v___f_2165_, v___x_2168_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2169_;
}
else
{
lean_dec_ref(v___f_2165_);
lean_dec(v_binderName_2161_);
return v___x_2166_;
}
}
case 7:
{
lean_object* v_binderName_2170_; lean_object* v_binderType_2171_; lean_object* v_body_2172_; uint8_t v_binderInfo_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v_binderName_2170_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_binderName_2170_);
v_binderType_2171_ = lean_ctor_get(v_e_2151_, 1);
lean_inc_ref(v_binderType_2171_);
v_body_2172_ = lean_ctor_get(v_e_2151_, 2);
lean_inc_ref(v_body_2172_);
v_binderInfo_2173_ = lean_ctor_get_uint8(v_e_2151_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2151_, 3);
lean_inc_ref(v_F_2150_);
lean_inc(v_fixedPrefixSize_2149_);
lean_inc(v_recFnName_2148_);
v___f_2174_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2174_, 0, v_body_2172_);
lean_closure_set(v___f_2174_, 1, v_recFnName_2148_);
lean_closure_set(v___f_2174_, 2, v_fixedPrefixSize_2149_);
lean_closure_set(v___f_2174_, 3, v_F_2150_);
v___x_2175_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_binderType_2171_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = 0;
v___x_2178_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2170_, v_binderInfo_2173_, v_a_2176_, v___f_2174_, v___x_2177_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2178_;
}
else
{
lean_dec_ref(v___f_2174_);
lean_dec(v_binderName_2170_);
return v___x_2175_;
}
}
case 8:
{
lean_object* v_declName_2179_; lean_object* v_type_2180_; lean_object* v_value_2181_; lean_object* v_body_2182_; uint8_t v_nondep_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; 
v_declName_2179_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_declName_2179_);
v_type_2180_ = lean_ctor_get(v_e_2151_, 1);
lean_inc_ref(v_type_2180_);
v_value_2181_ = lean_ctor_get(v_e_2151_, 2);
lean_inc_ref(v_value_2181_);
v_body_2182_ = lean_ctor_get(v_e_2151_, 3);
lean_inc_ref(v_body_2182_);
v_nondep_2183_ = lean_ctor_get_uint8(v_e_2151_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2151_, 4);
lean_inc_ref_n(v_F_2150_, 2);
lean_inc_n(v_fixedPrefixSize_2149_, 2);
lean_inc_n(v_recFnName_2148_, 2);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2184_, 0, v_body_2182_);
lean_closure_set(v___f_2184_, 1, v_recFnName_2148_);
lean_closure_set(v___f_2184_, 2, v_fixedPrefixSize_2149_);
lean_closure_set(v___f_2184_, 3, v_F_2150_);
v___x_2185_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_type_2180_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_value_2181_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = 0;
v___x_2190_ = 0;
v___x_2191_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2179_, v_a_2186_, v_a_2188_, v___f_2184_, v_nondep_2183_, v___x_2189_, v___x_2190_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2191_;
}
else
{
lean_dec(v_a_2186_);
lean_dec_ref(v___f_2184_);
lean_dec(v_declName_2179_);
return v___x_2187_;
}
}
else
{
lean_dec_ref(v___f_2184_);
lean_dec_ref(v_value_2181_);
lean_dec(v_declName_2179_);
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
lean_dec(v_recFnName_2148_);
return v___x_2185_;
}
}
case 10:
{
lean_object* v_data_2192_; lean_object* v_expr_2193_; lean_object* v___x_2194_; 
v_data_2192_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_data_2192_);
v_expr_2193_ = lean_ctor_get(v_e_2151_, 1);
lean_inc_ref(v_expr_2193_);
v___x_2194_ = l_Lean_getRecAppSyntax_x3f(v_e_2151_);
lean_dec_ref_known(v_e_2151_, 2);
if (lean_obj_tag(v___x_2194_) == 1)
{
lean_object* v_val_2195_; lean_object* v_toCold_2196_; lean_object* v_currRecDepth_2197_; lean_object* v_ref_2198_; uint16_t v_optionFlags_2199_; uint8_t v_suppressElabErrors_2200_; uint8_t v_isRecordingDeps_2201_; lean_object* v_ref_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_data_2192_);
v_val_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v_toCold_2196_ = lean_ctor_get(v_a_2158_, 0);
v_currRecDepth_2197_ = lean_ctor_get(v_a_2158_, 1);
v_ref_2198_ = lean_ctor_get(v_a_2158_, 2);
v_optionFlags_2199_ = lean_ctor_get_uint16(v_a_2158_, sizeof(void*)*3);
v_suppressElabErrors_2200_ = lean_ctor_get_uint8(v_a_2158_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2201_ = lean_ctor_get_uint8(v_a_2158_, sizeof(void*)*3 + 3);
v_ref_2202_ = l_Lean_replaceRef(v_val_2195_, v_ref_2198_);
lean_dec(v_val_2195_);
lean_inc(v_currRecDepth_2197_);
lean_inc_ref(v_toCold_2196_);
v___x_2203_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2203_, 0, v_toCold_2196_);
lean_ctor_set(v___x_2203_, 1, v_currRecDepth_2197_);
lean_ctor_set(v___x_2203_, 2, v_ref_2202_);
lean_ctor_set_uint16(v___x_2203_, sizeof(void*)*3, v_optionFlags_2199_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*3 + 2, v_suppressElabErrors_2200_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*3 + 3, v_isRecordingDeps_2201_);
v___x_2204_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_expr_2193_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v___x_2203_, v_a_2159_);
lean_dec_ref_known(v___x_2203_, 3);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; 
lean_dec(v___x_2194_);
v___x_2205_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_expr_2193_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = l_Lean_mkMData(v_data_2192_, v_a_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_dec(v_data_2192_);
return v___x_2205_;
}
}
}
case 11:
{
lean_object* v_typeName_2215_; lean_object* v_idx_2216_; lean_object* v_struct_2217_; lean_object* v___x_2218_; 
v_typeName_2215_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_typeName_2215_);
v_idx_2216_ = lean_ctor_get(v_e_2151_, 1);
lean_inc(v_idx_2216_);
v_struct_2217_ = lean_ctor_get(v_e_2151_, 2);
lean_inc_ref(v_struct_2217_);
lean_dec_ref_known(v_e_2151_, 3);
v___x_2218_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_struct_2217_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2227_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = l_Lean_mkProj(v_typeName_2215_, v_idx_2216_, v_a_2219_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2223_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_dec(v_idx_2216_);
lean_dec(v_typeName_2215_);
return v___x_2218_;
}
}
case 4:
{
uint8_t v___x_2228_; 
v___x_2228_ = l_Lean_Expr_isConstOf(v_e_2151_, v_recFnName_2148_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
lean_dec(v_recFnName_2148_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_e_2151_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2230_;
}
}
case 5:
{
uint8_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = 1;
lean_inc_ref(v_e_2151_);
v___x_2232_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2151_, v___x_2231_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
if (lean_obj_tag(v_a_2233_) == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2234_;
}
else
{
lean_object* v_val_2235_; lean_object* v___x_2236_; 
v_val_2235_ = lean_ctor_get(v_a_2233_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v_a_2233_, 1);
lean_inc_ref(v_F_2150_);
v___x_2236_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2235_, v_F_2150_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
if (lean_obj_tag(v_a_2237_) == 1)
{
lean_object* v_val_2238_; lean_object* v_toMatcherInfo_2239_; lean_object* v_matcherName_2240_; lean_object* v_matcherLevels_2241_; lean_object* v_params_2242_; lean_object* v_motive_2243_; lean_object* v_discrs_2244_; lean_object* v_alts_2245_; lean_object* v_remaining_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_val_2238_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_a_2237_, 1);
v_toMatcherInfo_2239_ = lean_ctor_get(v_val_2238_, 0);
lean_inc_ref(v_toMatcherInfo_2239_);
v_matcherName_2240_ = lean_ctor_get(v_val_2238_, 1);
lean_inc(v_matcherName_2240_);
v_matcherLevels_2241_ = lean_ctor_get(v_val_2238_, 2);
lean_inc_ref(v_matcherLevels_2241_);
v_params_2242_ = lean_ctor_get(v_val_2238_, 3);
lean_inc_ref(v_params_2242_);
v_motive_2243_ = lean_ctor_get(v_val_2238_, 4);
lean_inc_ref(v_motive_2243_);
v_discrs_2244_ = lean_ctor_get(v_val_2238_, 5);
lean_inc_ref(v_discrs_2244_);
v_alts_2245_ = lean_ctor_get(v_val_2238_, 6);
lean_inc_ref(v_alts_2245_);
v_remaining_2246_ = lean_ctor_get(v_val_2238_, 7);
lean_inc_ref(v_remaining_2246_);
v___x_2247_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2238_);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2149_);
lean_inc(v_recFnName_2148_);
v___x_2250_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_e_2151_, v_alts_2245_, v___x_2247_, v___x_2248_, v___x_2249_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v_alts_2245_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; size_t v_sz_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v_sz_2252_ = lean_array_size(v_discrs_2244_);
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_sz_2252_, v___x_2253_, v_discrs_2244_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2264_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2264_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2264_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2259_, 0, v_toMatcherInfo_2239_);
lean_ctor_set(v___x_2259_, 1, v_matcherName_2240_);
lean_ctor_set(v___x_2259_, 2, v_matcherLevels_2241_);
lean_ctor_set(v___x_2259_, 3, v_params_2242_);
lean_ctor_set(v___x_2259_, 4, v_motive_2243_);
lean_ctor_set(v___x_2259_, 5, v_a_2255_);
lean_ctor_set(v___x_2259_, 6, v_a_2251_);
lean_ctor_set(v___x_2259_, 7, v_remaining_2246_);
v___x_2260_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2259_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2260_);
v___x_2262_ = v___x_2257_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2251_);
lean_dec_ref(v_remaining_2246_);
lean_dec_ref(v_motive_2243_);
lean_dec_ref(v_params_2242_);
lean_dec_ref(v_matcherLevels_2241_);
lean_dec(v_matcherName_2240_);
lean_dec_ref(v_toMatcherInfo_2239_);
v_a_2265_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2254_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2254_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_remaining_2246_);
lean_dec_ref(v_discrs_2244_);
lean_dec_ref(v_motive_2243_);
lean_dec_ref(v_params_2242_);
lean_dec_ref(v_matcherLevels_2241_);
lean_dec(v_matcherName_2240_);
lean_dec_ref(v_toMatcherInfo_2239_);
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
lean_dec(v_recFnName_2148_);
v_a_2273_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2250_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2250_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v___x_2281_; 
lean_dec(v_a_2237_);
v___x_2281_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2148_, v_fixedPrefixSize_2149_, v_F_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2281_;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref_known(v_e_2151_, 2);
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
lean_dec(v_recFnName_2148_);
v_a_2282_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2236_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2236_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref_known(v_e_2151_, 2);
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
lean_dec(v_recFnName_2148_);
v_a_2290_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2232_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2232_);
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
default: 
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_F_2150_);
lean_dec(v_fixedPrefixSize_2149_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_mk_empty_array_with_capacity(v___x_2298_);
v___x_2300_ = lean_array_push(v___x_2299_, v_recFnName_2148_);
lean_inc_ref(v_e_2151_);
v___x_2301_ = l_Lean_Elab_ensureNoRecFn(v___x_2300_, v_e_2151_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2309_);
v___x_2303_ = v___x_2301_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v___x_2301_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_e_2151_);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_e_2151_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_e_2151_);
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2301_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2318_, lean_object* v_fixedPrefixSize_2319_, lean_object* v_F_2320_, lean_object* v_e_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___x_2350_; 
lean_inc_ref(v_e_2321_);
lean_inc(v_recFnName_2318_);
v___x_2350_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2318_, v_e_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2438_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2438_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2438_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v_F_2320_);
lean_dec(v_fixedPrefixSize_2319_);
lean_dec(v_recFnName_2318_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v_e_2321_);
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_e_2321_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
else
{
uint8_t v___x_2359_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_del_object(v___x_2353_);
v___x_2359_ = 0;
v___x_2415_ = lean_st_ref_get(v_a_2323_);
v___x_2416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2415_, v_e_2321_);
lean_dec(v___x_2415_);
if (lean_obj_tag(v___x_2416_) == 1)
{
lean_object* v_val_2417_; lean_object* v_fst_2418_; lean_object* v_snd_2419_; lean_object* v___x_2420_; 
v_val_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_val_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v_fst_2418_ = lean_ctor_get(v_val_2417_, 0);
lean_inc(v_fst_2418_);
v_snd_2419_ = lean_ctor_get(v_val_2417_, 1);
lean_inc(v_snd_2419_);
lean_dec(v_val_2417_);
v___x_2420_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2419_, v_a_2326_);
lean_dec(v_snd_2419_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_unbox(v_a_2421_);
lean_dec(v_a_2421_);
if (v___x_2425_ == 0)
{
lean_del_object(v___x_2423_);
lean_dec(v_fst_2418_);
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
v___y_2363_ = v_a_2324_;
v___y_2364_ = v_a_2325_;
v___y_2365_ = v_a_2326_;
v___y_2366_ = v_a_2327_;
v___y_2367_ = v_a_2328_;
v___y_2368_ = v_a_2329_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2427_; 
lean_dec_ref(v_e_2321_);
lean_dec_ref(v_F_2320_);
lean_dec(v_fixedPrefixSize_2319_);
lean_dec(v_recFnName_2318_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_fst_2418_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_fst_2418_);
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
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_fst_2418_);
lean_dec_ref(v_e_2321_);
lean_dec_ref(v_F_2320_);
lean_dec(v_fixedPrefixSize_2319_);
lean_dec(v_recFnName_2318_);
v_a_2430_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2420_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2420_);
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
lean_dec(v___x_2416_);
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
v___y_2363_ = v_a_2324_;
v___y_2364_ = v_a_2325_;
v___y_2365_ = v_a_2326_;
v___y_2366_ = v_a_2327_;
v___y_2367_ = v_a_2328_;
v___y_2368_ = v_a_2329_;
goto v___jp_2360_;
}
v___jp_2360_:
{
lean_object* v___x_2369_; 
lean_inc_ref(v_e_2321_);
v___x_2369_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2318_, v_fixedPrefixSize_2319_, v_F_2320_, v_e_2321_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc_n(v_a_2370_, 2);
lean_dec_ref_known(v___x_2369_, 1);
lean_inc_ref(v_e_2321_);
v___f_2371_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2371_, 0, v_e_2321_);
lean_closure_set(v___f_2371_, 1, v_a_2370_);
v___x_2372_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2406_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2406_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2406_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2377_ = lean_st_ref_take(v___y_2362_);
lean_inc(v_a_2370_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2370_);
lean_ctor_set(v___x_2378_, 1, v_a_2373_);
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2377_, v_e_2321_, v___x_2378_);
v___x_2380_ = lean_st_ref_put(v___y_2362_, v___x_2379_);
v___x_2381_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2367_);
v___x_2382_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2383_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_2381_, v___x_2382_);
lean_dec_ref(v___x_2381_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2385_; 
lean_dec_ref(v___f_2371_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v_a_2370_);
v___x_2385_ = v___x_2375_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2370_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
else
{
lean_object* v___x_2387_; uint8_t v_transparency_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; 
lean_del_object(v___x_2375_);
v___x_2387_ = l_Lean_Meta_Context_config(v___y_2365_);
v_transparency_2388_ = lean_ctor_get_uint8(v___x_2387_, 9);
lean_dec_ref(v___x_2387_);
v___x_2389_ = 0;
v___x_2390_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v_keyedConfig_2391_; uint8_t v_trackZetaDelta_2392_; lean_object* v_zetaDeltaSet_2393_; lean_object* v_lctx_2394_; lean_object* v_localInstances_2395_; lean_object* v_defEqCtx_x3f_2396_; lean_object* v_synthPendingDepth_2397_; lean_object* v_customCanUnfoldPredicate_x3f_2398_; uint8_t v_univApprox_2399_; uint8_t v_inTypeClassResolution_2400_; uint8_t v_cacheInferType_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_keyedConfig_2391_ = lean_ctor_get(v___y_2365_, 0);
v_trackZetaDelta_2392_ = lean_ctor_get_uint8(v___y_2365_, sizeof(void*)*7);
v_zetaDeltaSet_2393_ = lean_ctor_get(v___y_2365_, 1);
v_lctx_2394_ = lean_ctor_get(v___y_2365_, 2);
v_localInstances_2395_ = lean_ctor_get(v___y_2365_, 3);
v_defEqCtx_x3f_2396_ = lean_ctor_get(v___y_2365_, 4);
v_synthPendingDepth_2397_ = lean_ctor_get(v___y_2365_, 5);
v_customCanUnfoldPredicate_x3f_2398_ = lean_ctor_get(v___y_2365_, 6);
v_univApprox_2399_ = lean_ctor_get_uint8(v___y_2365_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2400_ = lean_ctor_get_uint8(v___y_2365_, sizeof(void*)*7 + 2);
v_cacheInferType_2401_ = lean_ctor_get_uint8(v___y_2365_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2391_);
v___x_2402_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2389_, v_keyedConfig_2391_);
lean_inc(v_customCanUnfoldPredicate_x3f_2398_);
lean_inc(v_synthPendingDepth_2397_);
lean_inc(v_defEqCtx_x3f_2396_);
lean_inc_ref(v_localInstances_2395_);
lean_inc_ref(v_lctx_2394_);
lean_inc(v_zetaDeltaSet_2393_);
v___x_2403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_zetaDeltaSet_2393_);
lean_ctor_set(v___x_2403_, 2, v_lctx_2394_);
lean_ctor_set(v___x_2403_, 3, v_localInstances_2395_);
lean_ctor_set(v___x_2403_, 4, v_defEqCtx_x3f_2396_);
lean_ctor_set(v___x_2403_, 5, v_synthPendingDepth_2397_);
lean_ctor_set(v___x_2403_, 6, v_customCanUnfoldPredicate_x3f_2398_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7, v_trackZetaDelta_2392_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 1, v_univApprox_2399_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2400_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 3, v_cacheInferType_2401_);
v___x_2404_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2371_, v___x_2359_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___x_2403_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref_known(v___x_2403_, 7);
v___y_2332_ = v_a_2370_;
v___y_2333_ = v___x_2404_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2371_, v___x_2359_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
v___y_2332_ = v_a_2370_;
v___y_2333_ = v___x_2405_;
goto v___jp_2331_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v___f_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_e_2321_);
v_a_2407_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2372_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2372_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_dec_ref(v_e_2321_);
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v_e_2321_);
lean_dec_ref(v_F_2320_);
lean_dec(v_fixedPrefixSize_2319_);
lean_dec(v_recFnName_2318_);
v_a_2439_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2350_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2350_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
v___jp_2331_:
{
if (lean_obj_tag(v___y_2333_) == 0)
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_isSharedCheck_2340_ = !lean_is_exclusive(v___y_2333_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v___y_2333_, 0);
lean_dec(v_unused_2341_);
v___x_2335_ = v___y_2333_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v___y_2333_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___y_2332_);
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___y_2332_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___y_2332_);
v_a_2342_ = lean_ctor_get(v___y_2333_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___y_2333_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___y_2333_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___y_2333_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2447_, lean_object* v_recFnName_2448_, lean_object* v_fixedPrefixSize_2449_, lean_object* v_F_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_expr_instantiate1(v_body_2447_, v_x_2451_);
v___x_2462_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2448_, v_fixedPrefixSize_2449_, v_F_2450_, v___x_2461_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2463_, lean_object* v_fixedPrefixSize_2464_, lean_object* v_F_2465_, lean_object* v_e_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2463_, v_fixedPrefixSize_2464_, v_F_2465_, v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec(v_a_2467_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2477_, lean_object* v_fixedPrefixSize_2478_, lean_object* v_F_2479_, lean_object* v_sz_2480_, lean_object* v_i_2481_, lean_object* v_bs_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
size_t v_sz_boxed_2492_; size_t v_i_boxed_2493_; lean_object* v_res_2494_; 
v_sz_boxed_2492_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2493_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2477_, v_fixedPrefixSize_2478_, v_F_2479_, v_sz_boxed_2492_, v_i_boxed_2493_, v_bs_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2495_, lean_object* v_fixedPrefixSize_2496_, lean_object* v_F_2497_, lean_object* v_x_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2495_, v_fixedPrefixSize_2496_, v_F_2497_, v_x_2498_, v_x_2499_, v_x_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec(v___y_2501_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2511_, lean_object* v_fixedPrefixSize_2512_, lean_object* v_e_2513_, lean_object* v_as_2514_, lean_object* v_bs_2515_, lean_object* v_i_2516_, lean_object* v_cs_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2511_, v_fixedPrefixSize_2512_, v_e_2513_, v_as_2514_, v_bs_2515_, v_i_2516_, v_cs_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v_bs_2515_);
lean_dec_ref(v_as_2514_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2528_, lean_object* v_fixedPrefixSize_2529_, lean_object* v_F_2530_, lean_object* v_e_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2528_, v_fixedPrefixSize_2529_, v_F_2530_, v_e_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec(v_a_2532_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2542_, lean_object* v_fixedPrefixSize_2543_, lean_object* v_F_2544_, lean_object* v_e_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2542_, v_fixedPrefixSize_2543_, v_F_2544_, v_e_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2556_, lean_object* v_fixedPrefixSize_2557_, lean_object* v_F_2558_, lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2556_, v_fixedPrefixSize_2557_, v_F_2558_, v_e_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec(v_a_2560_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2570_, lean_object* v_k_2571_, uint8_t v_allowLevelAssignments_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2571_, v_allowLevelAssignments_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2583_, lean_object* v_k_2584_, lean_object* v_allowLevelAssignments_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2595_; lean_object* v_res_2596_; 
v_allowLevelAssignments_boxed_2595_ = lean_unbox(v_allowLevelAssignments_2585_);
v_res_2596_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2583_, v_k_2584_, v_allowLevelAssignments_boxed_2595_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec(v___y_2586_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2597_, lean_object* v_name_2598_, uint8_t v_bi_2599_, lean_object* v_type_2600_, lean_object* v_k_2601_, uint8_t v_kind_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2598_, v_bi_2599_, v_type_2600_, v_k_2601_, v_kind_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_name_2614_, lean_object* v_bi_2615_, lean_object* v_type_2616_, lean_object* v_k_2617_, lean_object* v_kind_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v_bi_boxed_2628_; uint8_t v_kind_boxed_2629_; lean_object* v_res_2630_; 
v_bi_boxed_2628_ = lean_unbox(v_bi_2615_);
v_kind_boxed_2629_ = lean_unbox(v_kind_2618_);
v_res_2630_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2613_, v_name_2614_, v_bi_boxed_2628_, v_type_2616_, v_k_2617_, v_kind_boxed_2629_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec(v___y_2619_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2631_, lean_object* v_e_2632_, lean_object* v_maxFVars_2633_, lean_object* v_k_2634_, uint8_t v_cleanupAnnotations_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2632_, v_maxFVars_2633_, v_k_2634_, v_cleanupAnnotations_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_e_2647_, lean_object* v_maxFVars_2648_, lean_object* v_k_2649_, lean_object* v_cleanupAnnotations_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2660_; lean_object* v_res_2661_; 
v_cleanupAnnotations_boxed_2660_ = lean_unbox(v_cleanupAnnotations_2650_);
v_res_2661_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2646_, v_e_2647_, v_maxFVars_2648_, v_k_2649_, v_cleanupAnnotations_boxed_2660_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2662_, lean_object* v_R_2663_, lean_object* v_a_2664_, lean_object* v_b_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2664_, v_b_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2667_, lean_object* v_msg_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2667_, v_msg_2668_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2679_, lean_object* v_msg_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2679_, v_msg_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec(v___y_2681_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2691_, lean_object* v_m_2692_, lean_object* v_a_2693_, lean_object* v_b_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2692_, v_a_2693_, v_b_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2697_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_msg_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2708_, v_msg_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2720_, lean_object* v_m_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2721_, v_a_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2724_, lean_object* v_m_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2724_, v_m_2725_, v_a_2726_);
lean_dec_ref(v_a_2726_);
lean_dec_ref(v_m_2725_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2728_, lean_object* v_name_2729_, lean_object* v_type_2730_, lean_object* v_val_2731_, lean_object* v_k_2732_, uint8_t v_nondep_2733_, uint8_t v_kind_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2729_, v_type_2730_, v_val_2731_, v_k_2732_, v_nondep_2733_, v_kind_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_name_2746_, lean_object* v_type_2747_, lean_object* v_val_2748_, lean_object* v_k_2749_, lean_object* v_nondep_2750_, lean_object* v_kind_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v_nondep_boxed_2761_; uint8_t v_kind_boxed_2762_; lean_object* v_res_2763_; 
v_nondep_boxed_2761_ = lean_unbox(v_nondep_2750_);
v_kind_boxed_2762_ = lean_unbox(v_kind_2751_);
v_res_2763_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2745_, v_name_2746_, v_type_2747_, v_val_2748_, v_k_2749_, v_nondep_boxed_2761_, v_kind_boxed_2762_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2764_, v___y_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
return v_res_2785_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2786_, lean_object* v_a_2787_, lean_object* v_x_2788_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2787_, v_x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2790_, lean_object* v_a_2791_, lean_object* v_x_2792_){
_start:
{
uint8_t v_res_2793_; lean_object* v_r_2794_; 
v_res_2793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2790_, v_a_2791_, v_x_2792_);
lean_dec(v_x_2792_);
lean_dec_ref(v_a_2791_);
v_r_2794_ = lean_box(v_res_2793_);
return v_r_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2795_, lean_object* v_data_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_b_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2799_, v_b_2800_, v_x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2803_, lean_object* v_a_2804_, lean_object* v_x_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2804_, v_x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_a_2808_, lean_object* v_x_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2807_, v_a_2808_, v_x_2809_);
lean_dec(v_x_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2811_, lean_object* v_i_2812_, lean_object* v_source_2813_, lean_object* v_target_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2812_, v_source_2813_, v_target_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2816_, lean_object* v_constName_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_constName_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2828_, v_constName_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2830_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2841_, v_x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2844_, lean_object* v_ref_2845_, lean_object* v_constName_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2845_, v_constName_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_ref_2858_, lean_object* v_constName_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2857_, v_ref_2858_, v_constName_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec(v_ref_2858_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2870_, lean_object* v_ref_2871_, lean_object* v_msg_2872_, lean_object* v_declHint_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2871_, v_msg_2872_, v_declHint_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_ref_2885_, lean_object* v_msg_2886_, lean_object* v_declHint_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2884_, v_ref_2885_, v_msg_2886_, v_declHint_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v_ref_2885_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2898_, lean_object* v_declHint_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2898_, v_declHint_2899_, v___y_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2910_, lean_object* v_declHint_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2910_, v_declHint_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2922_, lean_object* v_ref_2923_, lean_object* v_msg_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2923_, v_msg_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2935_, lean_object* v_ref_2936_, lean_object* v_msg_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2935_, v_ref_2936_, v_msg_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v_ref_2936_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2948_, lean_object* v_msg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_ref_2955_; lean_object* v___x_2956_; lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3002_; 
v_ref_2955_ = lean_ctor_get(v___y_2952_, 2);
v___x_2956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_3002_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3002_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v_traceState_2962_; lean_object* v_env_2963_; lean_object* v_nextMacroScope_2964_; lean_object* v_ngen_2965_; lean_object* v_auxDeclNGen_2966_; lean_object* v_cache_2967_; lean_object* v_recordedDeps_2968_; lean_object* v_messages_2969_; lean_object* v_infoState_2970_; lean_object* v_snapshotTasks_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3001_; 
v___x_2961_ = lean_st_ref_take(v___y_2953_);
v_traceState_2962_ = lean_ctor_get(v___x_2961_, 4);
v_env_2963_ = lean_ctor_get(v___x_2961_, 0);
v_nextMacroScope_2964_ = lean_ctor_get(v___x_2961_, 1);
v_ngen_2965_ = lean_ctor_get(v___x_2961_, 2);
v_auxDeclNGen_2966_ = lean_ctor_get(v___x_2961_, 3);
v_cache_2967_ = lean_ctor_get(v___x_2961_, 5);
v_recordedDeps_2968_ = lean_ctor_get(v___x_2961_, 6);
v_messages_2969_ = lean_ctor_get(v___x_2961_, 7);
v_infoState_2970_ = lean_ctor_get(v___x_2961_, 8);
v_snapshotTasks_2971_ = lean_ctor_get(v___x_2961_, 9);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2973_ = v___x_2961_;
v_isShared_2974_ = v_isSharedCheck_3001_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_snapshotTasks_2971_);
lean_inc(v_infoState_2970_);
lean_inc(v_messages_2969_);
lean_inc(v_recordedDeps_2968_);
lean_inc(v_cache_2967_);
lean_inc(v_traceState_2962_);
lean_inc(v_auxDeclNGen_2966_);
lean_inc(v_ngen_2965_);
lean_inc(v_nextMacroScope_2964_);
lean_inc(v_env_2963_);
lean_dec(v___x_2961_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3001_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
uint64_t v_tid_2975_; lean_object* v_traces_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3000_; 
v_tid_2975_ = lean_ctor_get_uint64(v_traceState_2962_, sizeof(void*)*1);
v_traces_2976_ = lean_ctor_get(v_traceState_2962_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_traceState_2962_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2978_ = v_traceState_2962_;
v_isShared_2979_ = v_isSharedCheck_3000_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_traces_2976_);
lean_dec(v_traceState_2962_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3000_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; double v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2983_ = 0;
v___x_2984_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2985_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2985_, 0, v_cls_2948_);
lean_ctor_set(v___x_2985_, 1, v___x_2981_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
lean_ctor_set_float(v___x_2985_, sizeof(void*)*3, v___x_2982_);
lean_ctor_set_float(v___x_2985_, sizeof(void*)*3 + 8, v___x_2982_);
lean_ctor_set_uint8(v___x_2985_, sizeof(void*)*3 + 16, v___x_2983_);
v___x_2986_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2987_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v_a_2957_);
lean_ctor_set(v___x_2987_, 2, v___x_2986_);
lean_inc(v_ref_2955_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_ref_2955_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_PersistentArray_push___redArg(v_traces_2976_, v___x_2988_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2989_);
v___x_2991_ = v___x_2978_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2989_);
lean_ctor_set_uint64(v_reuseFailAlloc_2999_, sizeof(void*)*1, v_tid_2975_);
v___x_2991_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2993_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 4, v___x_2991_);
v___x_2993_ = v___x_2973_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_env_2963_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_nextMacroScope_2964_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_ngen_2965_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_auxDeclNGen_2966_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v_cache_2967_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v_recordedDeps_2968_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v_messages_2969_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v_infoState_2970_);
lean_ctor_set(v_reuseFailAlloc_2998_, 9, v_snapshotTasks_2971_);
v___x_2993_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2994_ = lean_st_ref_put(v___y_2953_, v___x_2993_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2980_);
v___x_2996_ = v___x_2959_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2980_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3003_, lean_object* v_msg_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3003_, v_msg_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_unsigned_to_nat(16u);
v___x_3013_ = lean_mk_array(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3019_ = l_Lean_stringToMessageData(v___x_3018_);
return v___x_3019_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3022_ = l_Lean_stringToMessageData(v___x_3021_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3025_ = l_Lean_stringToMessageData(v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3026_, lean_object* v_fixedPrefixSize_3027_, lean_object* v_F_3028_, lean_object* v_e_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v_toCold_3058_; lean_object* v_options_3059_; uint8_t v_hasTrace_3060_; 
v_toCold_3058_ = lean_ctor_get(v_a_3034_, 0);
v_options_3059_ = lean_ctor_get(v_toCold_3058_, 2);
v_hasTrace_3060_ = lean_ctor_get_uint8(v_options_3059_, sizeof(void*)*1);
if (v_hasTrace_3060_ == 0)
{
v___y_3038_ = v_a_3030_;
v___y_3039_ = v_a_3031_;
v___y_3040_ = v_a_3032_;
v___y_3041_ = v_a_3033_;
v___y_3042_ = v_a_3034_;
v___y_3043_ = v_a_3035_;
goto v___jp_3037_;
}
else
{
lean_object* v_inheritedTraceOptions_3061_; lean_object* v_cls_3062_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v_options_3069_; lean_object* v_inheritedTraceOptions_3070_; lean_object* v___y_3071_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v_inheritedTraceOptions_3061_ = lean_ctor_get(v_toCold_3058_, 11);
v_cls_3062_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3092_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3061_, v_options_3059_, v___x_3092_);
if (v___x_3093_ == 0)
{
v___y_3064_ = v_a_3030_;
v___y_3065_ = v_a_3031_;
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v_options_3069_ = v_options_3059_;
v_inheritedTraceOptions_3070_ = v_inheritedTraceOptions_3061_;
v___y_3071_ = v_a_3035_;
goto v___jp_3063_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3029_);
v___x_3095_ = l_Lean_indentExpr(v_e_3029_);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3062_, v___x_3096_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_dec_ref_known(v___x_3097_, 1);
v___y_3064_ = v_a_3030_;
v___y_3065_ = v_a_3031_;
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v_options_3069_ = v_options_3059_;
v_inheritedTraceOptions_3070_ = v_inheritedTraceOptions_3061_;
v___y_3071_ = v_a_3035_;
goto v___jp_3063_;
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v_e_3029_);
lean_dec_ref(v_F_3028_);
lean_dec(v_fixedPrefixSize_3027_);
lean_dec(v_recFnName_3026_);
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
v___jp_3063_:
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3070_, v_options_3069_, v___x_3072_);
if (v___x_3073_ == 0)
{
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3071_;
goto v___jp_3037_;
}
else
{
lean_object* v___x_3074_; 
lean_inc(v___y_3071_);
lean_inc_ref(v___y_3068_);
lean_inc(v___y_3067_);
lean_inc_ref(v___y_3066_);
lean_inc_ref(v_F_3028_);
v___x_3074_ = lean_infer_type(v_F_3028_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3071_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3028_);
v___x_3077_ = l_Lean_MessageData_ofExpr(v_F_3028_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_indentExpr(v_a_3075_);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3062_, v___x_3082_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3071_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_dec_ref_known(v___x_3083_, 1);
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3071_;
goto v___jp_3037_;
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_e_3029_);
lean_dec_ref(v_F_3028_);
lean_dec(v_fixedPrefixSize_3027_);
lean_dec(v_recFnName_3026_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_dec_ref(v_e_3029_);
lean_dec_ref(v_F_3028_);
lean_dec(v_fixedPrefixSize_3027_);
lean_dec(v_recFnName_3026_);
return v___x_3074_;
}
}
}
}
v___jp_3037_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3045_ = lean_st_mk_ref(v___x_3044_);
v___x_3046_ = lean_st_mk_ref(v___x_3044_);
v___x_3047_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3026_, v_fixedPrefixSize_3027_, v_F_3028_, v_e_3029_, v___x_3046_, v___x_3045_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3057_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3052_ = lean_st_ref_get(v___x_3046_);
lean_dec(v___x_3046_);
lean_dec(v___x_3052_);
v___x_3053_ = lean_st_ref_get(v___x_3045_);
lean_dec(v___x_3045_);
lean_dec(v___x_3053_);
if (v_isShared_3051_ == 0)
{
v___x_3055_ = v___x_3050_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3048_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_dec(v___x_3046_);
lean_dec(v___x_3045_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3106_, lean_object* v_fixedPrefixSize_3107_, lean_object* v_F_3108_, lean_object* v_e_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3106_, v_fixedPrefixSize_3107_, v_F_3108_, v_e_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3118_, lean_object* v_msg_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3118_, v_msg_3119_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3128_, lean_object* v_msg_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3128_, v_msg_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v_b_3141_, lean_object* v_c_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
v___x_3148_ = lean_apply_9(v_k_3138_, v_b_3141_, v_c_3142_, v___y_3139_, v___y_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, lean_box(0));
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v_b_3152_, lean_object* v_c_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3149_, v___y_3150_, v___y_3151_, v_b_3152_, v_c_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3160_, lean_object* v_maxFVars_3161_, lean_object* v_k_3162_, uint8_t v_cleanupAnnotations_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___f_3171_; uint8_t v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v___f_3171_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3171_, 0, v_k_3162_);
lean_closure_set(v___f_3171_, 1, v___y_3164_);
lean_closure_set(v___f_3171_, 2, v___y_3165_);
v___x_3172_ = 1;
v___x_3173_ = 0;
v___x_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3174_, 0, v_maxFVars_3161_);
v___x_3175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3160_, v___x_3172_, v___x_3173_, v___x_3172_, v___x_3173_, v___x_3174_, v___f_3171_, v_cleanupAnnotations_3163_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec_ref_known(v___x_3174_, 1);
if (lean_obj_tag(v___x_3175_) == 0)
{
return v___x_3175_;
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3184_, lean_object* v_maxFVars_3185_, lean_object* v_k_3186_, lean_object* v_cleanupAnnotations_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3195_; lean_object* v_res_3196_; 
v_cleanupAnnotations_boxed_3195_ = lean_unbox(v_cleanupAnnotations_3187_);
v_res_3196_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3184_, v_maxFVars_3185_, v_k_3186_, v_cleanupAnnotations_boxed_3195_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3197_, lean_object* v_e_3198_, lean_object* v_maxFVars_3199_, lean_object* v_k_3200_, uint8_t v_cleanupAnnotations_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3198_, v_maxFVars_3199_, v_k_3200_, v_cleanupAnnotations_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3210_, lean_object* v_e_3211_, lean_object* v_maxFVars_3212_, lean_object* v_k_3213_, lean_object* v_cleanupAnnotations_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3222_; lean_object* v_res_3223_; 
v_cleanupAnnotations_boxed_3222_ = lean_unbox(v_cleanupAnnotations_3214_);
v_res_3223_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3210_, v_e_3211_, v_maxFVars_3212_, v_k_3213_, v_cleanupAnnotations_boxed_3222_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3224_, lean_object* v_k_3225_, uint8_t v_cleanupAnnotations_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___f_3234_; uint8_t v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc(v___y_3228_);
lean_inc_ref(v___y_3227_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3234_, 0, v_k_3225_);
lean_closure_set(v___f_3234_, 1, v___y_3227_);
lean_closure_set(v___f_3234_, 2, v___y_3228_);
v___x_3235_ = 1;
v___x_3236_ = 0;
v___x_3237_ = lean_box(0);
v___x_3238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3224_, v___x_3235_, v___x_3236_, v___x_3235_, v___x_3236_, v___x_3237_, v___f_3234_, v_cleanupAnnotations_3226_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3238_) == 0)
{
return v___x_3238_;
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3247_, lean_object* v_k_3248_, lean_object* v_cleanupAnnotations_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3257_; lean_object* v_res_3258_; 
v_cleanupAnnotations_boxed_3257_ = lean_unbox(v_cleanupAnnotations_3249_);
v_res_3258_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3247_, v_k_3248_, v_cleanupAnnotations_boxed_3257_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3259_, lean_object* v_e_3260_, lean_object* v_k_3261_, uint8_t v_cleanupAnnotations_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3260_, v_k_3261_, v_cleanupAnnotations_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_e_3272_, lean_object* v_k_3273_, lean_object* v_cleanupAnnotations_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3282_; lean_object* v_res_3283_; 
v_cleanupAnnotations_boxed_3282_ = lean_unbox(v_cleanupAnnotations_3274_);
v_res_3283_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3271_, v_e_3272_, v_k_3273_, v_cleanupAnnotations_boxed_3282_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v_x_3287_, uint8_t v___x_3288_, lean_object* v_xs_3289_, lean_object* v_type_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3298_ = l_Lean_LocalDecl_type(v_a_3284_);
v___x_3299_ = lean_array_get_borrowed(v___x_3285_, v_xs_3289_, v___x_3286_);
v___x_3300_ = l_Lean_Expr_replaceFVar(v___x_3298_, v_x_3287_, v___x_3299_);
lean_dec_ref(v___x_3298_);
v___x_3301_ = l_Lean_mkArrow(v___x_3300_, v_type_3290_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; uint8_t v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_n(v_a_3302_, 2);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = 0;
v___x_3304_ = 1;
v___x_3305_ = l_Lean_Meta_mkLambdaFVars(v_xs_3289_, v_a_3302_, v___x_3303_, v___x_3288_, v___x_3303_, v___x_3288_, v___x_3304_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = l_Lean_Meta_getLevel(v_a_3302_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3316_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3316_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3316_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3306_);
lean_ctor_set(v___x_3312_, 1, v_a_3308_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3312_);
v___x_3314_ = v___x_3310_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_a_3306_);
v_a_3317_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3307_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3307_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_a_3302_);
v_a_3325_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3305_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3305_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_a_3333_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3301_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3301_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v_x_3344_, lean_object* v___x_3345_, lean_object* v_xs_3346_, lean_object* v_type_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v___x_6433__boxed_3355_; lean_object* v_res_3356_; 
v___x_6433__boxed_3355_ = lean_unbox(v___x_3345_);
v_res_3356_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3341_, v___x_3342_, v___x_3343_, v_x_3344_, v___x_6433__boxed_3355_, v_xs_3346_, v_type_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v_xs_3346_);
lean_dec(v___x_3343_);
lean_dec_ref(v___x_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v_b_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; 
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
v___x_3366_ = lean_apply_8(v_k_3357_, v_b_3360_, v___y_3358_, v___y_3359_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, lean_box(0));
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3367_, v___y_3368_, v___y_3369_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3377_, uint8_t v_bi_3378_, lean_object* v_type_3379_, lean_object* v_k_3380_, uint8_t v_kind_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___f_3389_; lean_object* v___x_3390_; 
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3389_, 0, v_k_3380_);
lean_closure_set(v___f_3389_, 1, v___y_3382_);
lean_closure_set(v___f_3389_, 2, v___y_3383_);
v___x_3390_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3377_, v_bi_3378_, v_type_3379_, v___f_3389_, v_kind_3381_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3390_) == 0)
{
return v___x_3390_;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3399_, lean_object* v_bi_3400_, lean_object* v_type_3401_, lean_object* v_k_3402_, lean_object* v_kind_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v_bi_boxed_3411_; uint8_t v_kind_boxed_3412_; lean_object* v_res_3413_; 
v_bi_boxed_3411_ = lean_unbox(v_bi_3400_);
v_kind_boxed_3412_ = lean_unbox(v_kind_3403_);
v_res_3413_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3399_, v_bi_boxed_3411_, v_type_3401_, v_k_3402_, v_kind_boxed_3412_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3414_, lean_object* v_type_3415_, lean_object* v_k_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
uint8_t v___x_3424_; uint8_t v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = 0;
v___x_3425_ = 0;
v___x_3426_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3414_, v___x_3424_, v_type_3415_, v_k_3416_, v___x_3425_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3427_, lean_object* v_type_3428_, lean_object* v_k_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3427_, v_type_3428_, v_k_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3451_, lean_object* v_F_3452_, lean_object* v_val_3453_, lean_object* v_k_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = l_Lean_Expr_isFVar(v_x_3451_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
v___x_3463_ = lean_apply_10(v_k_3454_, v_x_3451_, v_F_3452_, v_val_3453_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, lean_box(0));
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3465_ = lean_unsigned_to_nat(6u);
v___x_3466_ = l_Lean_Expr_isAppOfArity(v_val_3453_, v___x_3464_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
v___x_3467_ = lean_apply_10(v_k_3454_, v_x_3451_, v_F_3452_, v_val_3453_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, lean_box(0));
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3468_ = lean_unsigned_to_nat(3u);
v___x_3469_ = l_Lean_Expr_getAppNumArgs(v_val_3453_);
v___x_3470_ = lean_nat_sub(v___x_3469_, v___x_3468_);
v___x_3471_ = lean_unsigned_to_nat(1u);
v___x_3472_ = lean_nat_sub(v___x_3470_, v___x_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = l_Lean_Expr_getRevArg_x21(v_val_3453_, v___x_3472_);
v___x_3474_ = lean_expr_eqv(v___x_3473_, v_x_3451_);
lean_dec_ref(v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
v___x_3475_ = lean_apply_10(v_k_3454_, v_x_3451_, v_F_3452_, v_val_3453_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, lean_box(0));
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3476_ = lean_unsigned_to_nat(4u);
v___x_3477_ = lean_nat_sub(v___x_3469_, v___x_3476_);
v___x_3478_ = lean_nat_sub(v___x_3477_, v___x_3471_);
lean_dec(v___x_3477_);
v___x_3479_ = l_Lean_Expr_getRevArg_x21(v_val_3453_, v___x_3478_);
v___x_3480_ = l_Lean_Expr_isLambda(v___x_3479_);
lean_dec_ref(v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
v___x_3481_ = lean_apply_10(v_k_3454_, v_x_3451_, v_F_3452_, v_val_3453_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, lean_box(0));
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3482_ = lean_unsigned_to_nat(5u);
v___x_3483_ = lean_nat_sub(v___x_3469_, v___x_3482_);
v___x_3484_ = lean_nat_sub(v___x_3483_, v___x_3471_);
lean_dec(v___x_3483_);
v___x_3485_ = l_Lean_Expr_getRevArg_x21(v_val_3453_, v___x_3484_);
v___x_3486_ = l_Lean_Expr_isLambda(v___x_3485_);
lean_dec_ref(v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
v___x_3487_ = lean_apply_10(v_k_3454_, v_x_3451_, v_F_3452_, v_val_3453_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, lean_box(0));
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; lean_object* v_dummy_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v_args_3492_; lean_object* v___x_3493_; lean_object* v_00_u03b1_3494_; lean_object* v_00_u03b2_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3488_ = l_Lean_instInhabitedExpr;
v_dummy_3489_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3469_);
v___x_3490_ = lean_mk_array(v___x_3469_, v_dummy_3489_);
v___x_3491_ = lean_nat_sub(v___x_3469_, v___x_3471_);
lean_dec(v___x_3469_);
v_args_3492_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3453_, v___x_3490_, v___x_3491_);
v___x_3493_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3494_ = lean_array_get(v___x_3488_, v_args_3492_, v___x_3493_);
v_00_u03b2_3495_ = lean_array_get(v___x_3488_, v_args_3492_, v___x_3471_);
v___x_3496_ = l_Lean_Expr_fvarId_x21(v_F_3452_);
v___x_3497_ = l_Lean_FVarId_getDecl___redArg(v___x_3496_, v_a_3457_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc_n(v_a_3498_, 2);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = lean_box(v___x_3480_);
lean_inc_ref(v_x_3451_);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3500_, 0, v_a_3498_);
lean_closure_set(v___f_3500_, 1, v___x_3488_);
lean_closure_set(v___f_3500_, 2, v___x_3493_);
lean_closure_set(v___f_3500_, 3, v_x_3451_);
lean_closure_set(v___f_3500_, 4, v___x_3499_);
v___x_3501_ = lean_unsigned_to_nat(2u);
v___x_3502_ = lean_array_get_borrowed(v___x_3488_, v_args_3492_, v___x_3501_);
v___x_3503_ = 0;
lean_inc(v___x_3502_);
v___x_3504_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3502_, v___f_3500_, v___x_3503_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3563_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
v_fst_3506_ = lean_ctor_get(v_a_3505_, 0);
v_snd_3507_ = lean_ctor_get(v_a_3505_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_a_3505_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3509_ = v_a_3505_;
v_isShared_3510_ = v_isSharedCheck_3563_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_snd_3507_);
lean_inc(v_fst_3506_);
lean_dec(v_a_3505_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3563_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3512_ = lean_array_get_borrowed(v___x_3488_, v_args_3492_, v___x_3476_);
lean_inc(v___x_3512_);
lean_inc_ref(v_x_3451_);
lean_inc(v_a_3498_);
lean_inc(v_00_u03b2_3495_);
lean_inc(v_00_u03b1_3494_);
lean_inc_ref(v_k_3454_);
v___x_3513_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3488_, v___x_3493_, v_k_3454_, v___x_3501_, v___x_3503_, v___x_3480_, v_00_u03b1_3494_, v_00_u03b2_3495_, v___x_3468_, v_a_3498_, v_x_3451_, v___x_3471_, v___x_3511_, v___x_3512_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3516_ = lean_array_get(v___x_3488_, v_args_3492_, v___x_3482_);
lean_dec_ref(v_args_3492_);
lean_inc_ref(v_x_3451_);
lean_inc(v_00_u03b2_3495_);
lean_inc(v_00_u03b1_3494_);
v___x_3517_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3488_, v___x_3493_, v_k_3454_, v___x_3501_, v___x_3503_, v___x_3480_, v_00_u03b1_3494_, v_00_u03b2_3495_, v___x_3468_, v_a_3498_, v_x_3451_, v___x_3471_, v___x_3515_, v___x_3516_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
lean_inc(v_00_u03b1_3494_);
v___x_3519_ = l_Lean_Meta_getLevel(v_00_u03b1_3494_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
lean_inc(v_00_u03b2_3495_);
v___x_3521_ = l_Lean_Meta_getLevel(v_00_u03b2_3495_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3546_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3546_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3546_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 1);
lean_ctor_set(v___x_3509_, 1, v___x_3526_);
lean_ctor_set(v___x_3509_, 0, v_a_3522_);
v___x_3528_ = v___x_3509_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3522_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3520_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_snd_3507_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_mkConst(v___x_3464_, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(7u);
v___x_3533_ = lean_mk_empty_array_with_capacity(v___x_3532_);
v___x_3534_ = lean_array_push(v___x_3533_, v_00_u03b1_3494_);
v___x_3535_ = lean_array_push(v___x_3534_, v_00_u03b2_3495_);
v___x_3536_ = lean_array_push(v___x_3535_, v_fst_3506_);
v___x_3537_ = lean_array_push(v___x_3536_, v_x_3451_);
v___x_3538_ = lean_array_push(v___x_3537_, v_a_3514_);
v___x_3539_ = lean_array_push(v___x_3538_, v_a_3518_);
v___x_3540_ = lean_array_push(v___x_3539_, v_F_3452_);
v___x_3541_ = l_Lean_mkAppN(v___x_3531_, v___x_3540_);
lean_dec_ref(v___x_3540_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3541_);
v___x_3543_ = v___x_3524_;
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
lean_dec(v_a_3520_);
lean_dec(v_a_3518_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_snd_3507_);
lean_dec(v_fst_3506_);
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
v_a_3547_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3521_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3521_);
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
lean_dec(v_a_3518_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_snd_3507_);
lean_dec(v_fst_3506_);
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
v_a_3555_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3519_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3519_);
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
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_snd_3507_);
lean_dec(v_fst_3506_);
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
return v___x_3517_;
}
}
else
{
lean_del_object(v___x_3509_);
lean_dec(v_snd_3507_);
lean_dec(v_fst_3506_);
lean_dec(v_a_3498_);
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_args_3492_);
lean_dec_ref(v_k_3454_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
return v___x_3513_;
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_a_3498_);
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_args_3492_);
lean_dec_ref(v_k_3454_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
v_a_3564_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3504_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3504_);
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
lean_dec(v_00_u03b2_3495_);
lean_dec(v_00_u03b1_3494_);
lean_dec_ref(v_args_3492_);
lean_dec_ref(v_k_3454_);
lean_dec_ref(v_F_3452_);
lean_dec_ref(v_x_3451_);
v_a_3572_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3497_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3497_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3580_, lean_object* v_body_3581_, lean_object* v_k_3582_, lean_object* v___x_3583_, uint8_t v___x_3584_, uint8_t v___x_3585_, lean_object* v_FNew_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
lean_inc_ref(v_FNew_3586_);
lean_inc_ref(v___x_3580_);
v___x_3594_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3580_, v_FNew_3586_, v_body_3581_, v_k_3582_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; lean_object* v___x_3600_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = lean_mk_empty_array_with_capacity(v___x_3583_);
v___x_3597_ = lean_array_push(v___x_3596_, v___x_3580_);
v___x_3598_ = lean_array_push(v___x_3597_, v_FNew_3586_);
v___x_3599_ = 1;
v___x_3600_ = l_Lean_Meta_mkLambdaFVars(v___x_3598_, v_a_3595_, v___x_3584_, v___x_3585_, v___x_3584_, v___x_3585_, v___x_3599_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec_ref(v___x_3598_);
return v___x_3600_;
}
else
{
lean_dec_ref(v_FNew_3586_);
lean_dec_ref(v___x_3580_);
return v___x_3594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3601_, lean_object* v_body_3602_, lean_object* v_k_3603_, lean_object* v___x_3604_, lean_object* v___x_3605_, lean_object* v___x_3606_, lean_object* v_FNew_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
uint8_t v___x_6674__boxed_3615_; uint8_t v___x_6675__boxed_3616_; lean_object* v_res_3617_; 
v___x_6674__boxed_3615_ = lean_unbox(v___x_3605_);
v___x_6675__boxed_3616_ = lean_unbox(v___x_3606_);
v_res_3617_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3601_, v_body_3602_, v_k_3603_, v___x_3604_, v___x_6674__boxed_3615_, v___x_6675__boxed_3616_, v_FNew_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___x_3604_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3618_, lean_object* v___x_3619_, lean_object* v_k_3620_, lean_object* v___x_3621_, uint8_t v___x_3622_, uint8_t v___x_3623_, lean_object* v_00_u03b1_3624_, lean_object* v_00_u03b2_3625_, lean_object* v___x_3626_, lean_object* v_ctorName_3627_, lean_object* v_a_3628_, lean_object* v_x_3629_, lean_object* v_xs_3630_, lean_object* v_body_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3639_ = lean_array_get_borrowed(v___x_3618_, v_xs_3630_, v___x_3619_);
v___x_3640_ = lean_box(v___x_3622_);
v___x_3641_ = lean_box(v___x_3623_);
lean_inc_n(v___x_3639_, 2);
v___f_3642_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3642_, 0, v___x_3639_);
lean_closure_set(v___f_3642_, 1, v_body_3631_);
lean_closure_set(v___f_3642_, 2, v_k_3620_);
lean_closure_set(v___f_3642_, 3, v___x_3621_);
lean_closure_set(v___f_3642_, 4, v___x_3640_);
lean_closure_set(v___f_3642_, 5, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v_00_u03b1_3624_);
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_00_u03b2_3625_);
v___x_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3639_);
v___x_3646_ = lean_mk_empty_array_with_capacity(v___x_3626_);
v___x_3647_ = lean_array_push(v___x_3646_, v___x_3643_);
v___x_3648_ = lean_array_push(v___x_3647_, v___x_3644_);
v___x_3649_ = lean_array_push(v___x_3648_, v___x_3645_);
v___x_3650_ = l_Lean_Meta_mkAppOptM(v_ctorName_3627_, v___x_3649_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = l_Lean_LocalDecl_type(v_a_3628_);
v___x_3653_ = l_Lean_Expr_replaceFVar(v___x_3652_, v_x_3629_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = l_Lean_LocalDecl_userName(v_a_3628_);
v___x_3655_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3654_, v___x_3653_, v___f_3642_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3655_;
}
else
{
lean_dec_ref(v___f_3642_);
lean_dec_ref(v_x_3629_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3656_ = _args[0];
lean_object* v___x_3657_ = _args[1];
lean_object* v_k_3658_ = _args[2];
lean_object* v___x_3659_ = _args[3];
lean_object* v___x_3660_ = _args[4];
lean_object* v___x_3661_ = _args[5];
lean_object* v_00_u03b1_3662_ = _args[6];
lean_object* v_00_u03b2_3663_ = _args[7];
lean_object* v___x_3664_ = _args[8];
lean_object* v_ctorName_3665_ = _args[9];
lean_object* v_a_3666_ = _args[10];
lean_object* v_x_3667_ = _args[11];
lean_object* v_xs_3668_ = _args[12];
lean_object* v_body_3669_ = _args[13];
lean_object* v___y_3670_ = _args[14];
lean_object* v___y_3671_ = _args[15];
lean_object* v___y_3672_ = _args[16];
lean_object* v___y_3673_ = _args[17];
lean_object* v___y_3674_ = _args[18];
lean_object* v___y_3675_ = _args[19];
lean_object* v___y_3676_ = _args[20];
_start:
{
uint8_t v___x_6694__boxed_3677_; uint8_t v___x_6695__boxed_3678_; lean_object* v_res_3679_; 
v___x_6694__boxed_3677_ = lean_unbox(v___x_3660_);
v___x_6695__boxed_3678_ = lean_unbox(v___x_3661_);
v_res_3679_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3656_, v___x_3657_, v_k_3658_, v___x_3659_, v___x_6694__boxed_3677_, v___x_6695__boxed_3678_, v_00_u03b1_3662_, v_00_u03b2_3663_, v___x_3664_, v_ctorName_3665_, v_a_3666_, v_x_3667_, v_xs_3668_, v_body_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec_ref(v_xs_3668_);
lean_dec_ref(v_a_3666_);
lean_dec(v___x_3664_);
lean_dec(v___x_3657_);
lean_dec_ref(v___x_3656_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3680_, lean_object* v___x_3681_, lean_object* v_k_3682_, lean_object* v___x_3683_, uint8_t v___x_3684_, uint8_t v___x_3685_, lean_object* v_00_u03b1_3686_, lean_object* v_00_u03b2_3687_, lean_object* v___x_3688_, lean_object* v_a_3689_, lean_object* v_x_3690_, lean_object* v___x_3691_, lean_object* v_ctorName_3692_, lean_object* v_minor_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___f_3703_; lean_object* v___x_3704_; 
v___x_3701_ = lean_box(v___x_3684_);
v___x_3702_ = lean_box(v___x_3685_);
v___f_3703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3703_, 0, v___x_3680_);
lean_closure_set(v___f_3703_, 1, v___x_3681_);
lean_closure_set(v___f_3703_, 2, v_k_3682_);
lean_closure_set(v___f_3703_, 3, v___x_3683_);
lean_closure_set(v___f_3703_, 4, v___x_3701_);
lean_closure_set(v___f_3703_, 5, v___x_3702_);
lean_closure_set(v___f_3703_, 6, v_00_u03b1_3686_);
lean_closure_set(v___f_3703_, 7, v_00_u03b2_3687_);
lean_closure_set(v___f_3703_, 8, v___x_3688_);
lean_closure_set(v___f_3703_, 9, v_ctorName_3692_);
lean_closure_set(v___f_3703_, 10, v_a_3689_);
lean_closure_set(v___f_3703_, 11, v_x_3690_);
v___x_3704_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3693_, v___x_3691_, v___f_3703_, v___x_3684_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3705_ = _args[0];
lean_object* v___x_3706_ = _args[1];
lean_object* v_k_3707_ = _args[2];
lean_object* v___x_3708_ = _args[3];
lean_object* v___x_3709_ = _args[4];
lean_object* v___x_3710_ = _args[5];
lean_object* v_00_u03b1_3711_ = _args[6];
lean_object* v_00_u03b2_3712_ = _args[7];
lean_object* v___x_3713_ = _args[8];
lean_object* v_a_3714_ = _args[9];
lean_object* v_x_3715_ = _args[10];
lean_object* v___x_3716_ = _args[11];
lean_object* v_ctorName_3717_ = _args[12];
lean_object* v_minor_3718_ = _args[13];
lean_object* v___y_3719_ = _args[14];
lean_object* v___y_3720_ = _args[15];
lean_object* v___y_3721_ = _args[16];
lean_object* v___y_3722_ = _args[17];
lean_object* v___y_3723_ = _args[18];
lean_object* v___y_3724_ = _args[19];
lean_object* v___y_3725_ = _args[20];
_start:
{
uint8_t v___x_6658__boxed_3726_; uint8_t v___x_6659__boxed_3727_; lean_object* v_res_3728_; 
v___x_6658__boxed_3726_ = lean_unbox(v___x_3709_);
v___x_6659__boxed_3727_ = lean_unbox(v___x_3710_);
v_res_3728_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3705_, v___x_3706_, v_k_3707_, v___x_3708_, v___x_6658__boxed_3726_, v___x_6659__boxed_3727_, v_00_u03b1_3711_, v_00_u03b2_3712_, v___x_3713_, v_a_3714_, v_x_3715_, v___x_3716_, v_ctorName_3717_, v_minor_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3729_, lean_object* v_F_3730_, lean_object* v_val_3731_, lean_object* v_k_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3729_, v_F_3730_, v_val_3731_, v_k_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3741_, lean_object* v_name_3742_, uint8_t v_bi_3743_, lean_object* v_type_3744_, lean_object* v_k_3745_, uint8_t v_kind_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3742_, v_bi_3743_, v_type_3744_, v_k_3745_, v_kind_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3755_, lean_object* v_name_3756_, lean_object* v_bi_3757_, lean_object* v_type_3758_, lean_object* v_k_3759_, lean_object* v_kind_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
uint8_t v_bi_boxed_3768_; uint8_t v_kind_boxed_3769_; lean_object* v_res_3770_; 
v_bi_boxed_3768_ = lean_unbox(v_bi_3757_);
v_kind_boxed_3769_ = lean_unbox(v_kind_3760_);
v_res_3770_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3755_, v_name_3756_, v_bi_boxed_3768_, v_type_3758_, v_k_3759_, v_kind_boxed_3769_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3771_, lean_object* v_name_3772_, lean_object* v_type_3773_, lean_object* v_k_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3772_, v_type_3773_, v_k_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3783_, lean_object* v_name_3784_, lean_object* v_type_3785_, lean_object* v_k_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3783_, v_name_3784_, v_type_3785_, v_k_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v_res_3794_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3527__overap_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3527__overap_3805_ = lean_panic_fn_borrowed(v___x_3804_, v_msg_3796_);
lean_inc(v___y_3802_);
lean_inc_ref(v___y_3801_);
lean_inc(v___y_3800_);
lean_inc_ref(v___y_3799_);
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
v___x_3806_ = lean_apply_7(v___x_3527__overap_3805_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, lean_box(0));
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3815_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3819_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3820_ = lean_unsigned_to_nat(49u);
v___x_3821_ = lean_unsigned_to_nat(186u);
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3824_ = l_mkPanicMessageWithDecl(v___x_3823_, v___x_3822_, v___x_3821_, v___x_3820_, v___x_3819_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3829_, lean_object* v_a_3830_, lean_object* v_k_3831_, lean_object* v___x_3832_, lean_object* v___x_3833_, lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v_FNew_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
uint8_t v___x_3693__boxed_3845_; uint8_t v___x_3694__boxed_3846_; uint8_t v___x_3695__boxed_3847_; lean_object* v_res_3848_; 
v___x_3693__boxed_3845_ = lean_unbox(v___x_3834_);
v___x_3694__boxed_3846_ = lean_unbox(v___x_3835_);
v___x_3695__boxed_3847_ = lean_unbox(v___x_3836_);
v_res_3848_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3829_, v_a_3830_, v_k_3831_, v___x_3832_, v___x_3833_, v___x_3693__boxed_3845_, v___x_3694__boxed_3846_, v___x_3695__boxed_3847_, v_FNew_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___x_3832_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v___x_3852_, lean_object* v___x_3853_, uint8_t v___x_3854_, uint8_t v___x_3855_, lean_object* v_k_3856_, lean_object* v___x_3857_, lean_object* v___x_3858_, lean_object* v_00_u03b1_3859_, lean_object* v_00_u03b2_3860_, lean_object* v___x_3861_, lean_object* v_a_3862_, lean_object* v_x_3863_, lean_object* v_xs_3864_, lean_object* v_body_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; lean_object* v___x_3879_; 
v___x_3873_ = lean_array_get(v___x_3850_, v_xs_3864_, v___x_3851_);
v___x_3874_ = lean_array_get(v___x_3850_, v_xs_3864_, v___x_3852_);
v___x_3875_ = lean_array_get_size(v_xs_3864_);
v___x_3876_ = l_Array_toSubarray___redArg(v_xs_3864_, v___x_3853_, v___x_3875_);
v___x_3877_ = l_Subarray_copy___redArg(v___x_3876_);
v___x_3878_ = 1;
v___x_3879_ = l_Lean_Meta_mkLambdaFVars(v___x_3877_, v_body_3865_, v___x_3854_, v___x_3855_, v___x_3854_, v___x_3855_, v___x_3878_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec_ref(v___x_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3907_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3907_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3907_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___f_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3884_ = lean_box(v___x_3854_);
v___x_3885_ = lean_box(v___x_3855_);
v___x_3886_ = lean_box(v___x_3878_);
lean_inc(v___x_3873_);
lean_inc(v___x_3874_);
v___f_3887_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3887_, 0, v___x_3874_);
lean_closure_set(v___f_3887_, 1, v_a_3880_);
lean_closure_set(v___f_3887_, 2, v_k_3856_);
lean_closure_set(v___f_3887_, 3, v___x_3857_);
lean_closure_set(v___f_3887_, 4, v___x_3873_);
lean_closure_set(v___f_3887_, 5, v___x_3884_);
lean_closure_set(v___f_3887_, 6, v___x_3885_);
lean_closure_set(v___f_3887_, 7, v___x_3886_);
v___x_3888_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0));
v___x_3889_ = l_Lean_Name_mkStr2(v___x_3858_, v___x_3888_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
lean_ctor_set(v___x_3882_, 0, v_00_u03b1_3859_);
v___x_3891_ = v___x_3882_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_00_u03b1_3859_);
v___x_3891_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_00_u03b2_3860_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3873_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3874_);
v___x_3895_ = lean_mk_empty_array_with_capacity(v___x_3861_);
v___x_3896_ = lean_array_push(v___x_3895_, v___x_3891_);
v___x_3897_ = lean_array_push(v___x_3896_, v___x_3892_);
v___x_3898_ = lean_array_push(v___x_3897_, v___x_3893_);
v___x_3899_ = lean_array_push(v___x_3898_, v___x_3894_);
v___x_3900_ = l_Lean_Meta_mkAppOptM(v___x_3889_, v___x_3899_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = l_Lean_LocalDecl_type(v_a_3862_);
v___x_3903_ = l_Lean_Expr_replaceFVar(v___x_3902_, v_x_3863_, v_a_3901_);
lean_dec(v_a_3901_);
lean_dec_ref(v___x_3902_);
v___x_3904_ = l_Lean_LocalDecl_userName(v_a_3862_);
v___x_3905_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3904_, v___x_3903_, v___f_3887_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3905_;
}
else
{
lean_dec_ref(v___f_3887_);
lean_dec_ref(v_x_3863_);
return v___x_3900_;
}
}
}
}
else
{
lean_dec(v___x_3874_);
lean_dec(v___x_3873_);
lean_dec_ref(v_x_3863_);
lean_dec_ref(v_00_u03b2_3860_);
lean_dec_ref(v_00_u03b1_3859_);
lean_dec_ref(v___x_3858_);
lean_dec(v___x_3857_);
lean_dec_ref(v_k_3856_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3908_ = _args[0];
lean_object* v___x_3909_ = _args[1];
lean_object* v___x_3910_ = _args[2];
lean_object* v___x_3911_ = _args[3];
lean_object* v___x_3912_ = _args[4];
lean_object* v___x_3913_ = _args[5];
lean_object* v_k_3914_ = _args[6];
lean_object* v___x_3915_ = _args[7];
lean_object* v___x_3916_ = _args[8];
lean_object* v_00_u03b1_3917_ = _args[9];
lean_object* v_00_u03b2_3918_ = _args[10];
lean_object* v___x_3919_ = _args[11];
lean_object* v_a_3920_ = _args[12];
lean_object* v_x_3921_ = _args[13];
lean_object* v_xs_3922_ = _args[14];
lean_object* v_body_3923_ = _args[15];
lean_object* v___y_3924_ = _args[16];
lean_object* v___y_3925_ = _args[17];
lean_object* v___y_3926_ = _args[18];
lean_object* v___y_3927_ = _args[19];
lean_object* v___y_3928_ = _args[20];
lean_object* v___y_3929_ = _args[21];
lean_object* v___y_3930_ = _args[22];
_start:
{
uint8_t v___x_3716__boxed_3931_; uint8_t v___x_3717__boxed_3932_; lean_object* v_res_3933_; 
v___x_3716__boxed_3931_ = lean_unbox(v___x_3912_);
v___x_3717__boxed_3932_ = lean_unbox(v___x_3913_);
v_res_3933_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3908_, v___x_3909_, v___x_3910_, v___x_3911_, v___x_3716__boxed_3931_, v___x_3717__boxed_3932_, v_k_3914_, v___x_3915_, v___x_3916_, v_00_u03b1_3917_, v_00_u03b2_3918_, v___x_3919_, v_a_3920_, v_x_3921_, v_xs_3922_, v_body_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v_a_3920_);
lean_dec(v___x_3919_);
lean_dec(v___x_3910_);
lean_dec(v___x_3909_);
lean_dec_ref(v___x_3908_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3934_, lean_object* v_F_3935_, lean_object* v_val_3936_, lean_object* v_k_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; uint8_t v___x_3954_; 
v___x_3954_ = l_Lean_Expr_isFVar(v_x_3934_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
lean_dec_ref(v_x_3934_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_a_3941_);
lean_inc_ref(v_a_3940_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
v___x_3955_ = lean_apply_9(v_k_3937_, v_F_3935_, v_val_3936_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, lean_box(0));
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5));
v___x_3958_ = lean_unsigned_to_nat(5u);
v___x_3959_ = l_Lean_Expr_isAppOfArity(v_val_3936_, v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v_x_3934_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_a_3941_);
lean_inc_ref(v_a_3940_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
v___x_3960_ = lean_apply_9(v_k_3937_, v_F_3935_, v_val_3936_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, lean_box(0));
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3961_ = lean_unsigned_to_nat(3u);
v___x_3962_ = l_Lean_Expr_getAppNumArgs(v_val_3936_);
v___x_3963_ = lean_nat_sub(v___x_3962_, v___x_3961_);
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_nat_sub(v___x_3963_, v___x_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = l_Lean_Expr_getRevArg_x21(v_val_3936_, v___x_3965_);
v___x_3967_ = lean_expr_eqv(v___x_3966_, v_x_3934_);
lean_dec_ref(v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3934_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_a_3941_);
lean_inc_ref(v_a_3940_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
v___x_3968_ = lean_apply_9(v_k_3937_, v_F_3935_, v_val_3936_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, lean_box(0));
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3969_ = lean_unsigned_to_nat(4u);
v___x_3970_ = lean_nat_sub(v___x_3962_, v___x_3969_);
v___x_3971_ = lean_nat_sub(v___x_3970_, v___x_3964_);
lean_dec(v___x_3970_);
v___x_3972_ = l_Lean_Expr_getRevArg_x21(v_val_3936_, v___x_3971_);
v___x_3973_ = l_Lean_Expr_isLambda(v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec_ref(v___x_3972_);
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3934_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_a_3941_);
lean_inc_ref(v_a_3940_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
v___x_3974_ = lean_apply_9(v_k_3937_, v_F_3935_, v_val_3936_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, lean_box(0));
return v___x_3974_;
}
else
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = l_Lean_Expr_bindingBody_x21(v___x_3972_);
lean_dec_ref(v___x_3972_);
v___x_3976_ = l_Lean_Expr_isLambda(v___x_3975_);
lean_dec_ref(v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3934_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_a_3941_);
lean_inc_ref(v_a_3940_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
v___x_3977_ = lean_apply_9(v_k_3937_, v_F_3935_, v_val_3936_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, lean_box(0));
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = l_Lean_Expr_getAppFn(v_val_3936_);
v___x_3979_ = l_Lean_Expr_constLevels_x21(v___x_3978_);
lean_dec_ref(v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 1)
{
lean_object* v_tail_3980_; 
v_tail_3980_ = lean_ctor_get(v___x_3979_, 1);
lean_inc(v_tail_3980_);
lean_dec_ref_known(v___x_3979_, 2);
if (lean_obj_tag(v_tail_3980_) == 1)
{
lean_object* v_tail_3981_; 
v_tail_3981_ = lean_ctor_get(v_tail_3980_, 1);
lean_inc(v_tail_3981_);
if (lean_obj_tag(v_tail_3981_) == 1)
{
lean_object* v_tail_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4048_; 
v_tail_3982_ = lean_ctor_get(v_tail_3981_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_tail_3981_);
if (v_isSharedCheck_4048_ == 0)
{
lean_object* v_unused_4049_; 
v_unused_4049_ = lean_ctor_get(v_tail_3981_, 0);
lean_dec(v_unused_4049_);
v___x_3984_ = v_tail_3981_;
v_isShared_3985_ = v_isSharedCheck_4048_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_tail_3982_);
lean_dec(v_tail_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4048_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
if (lean_obj_tag(v_tail_3982_) == 0)
{
lean_object* v___x_3986_; lean_object* v_dummy_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_args_3990_; lean_object* v___x_3991_; lean_object* v_00_u03b1_3992_; lean_object* v_00_u03b2_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3986_ = l_Lean_instInhabitedExpr;
v_dummy_3987_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3962_);
v___x_3988_ = lean_mk_array(v___x_3962_, v_dummy_3987_);
v___x_3989_ = lean_nat_sub(v___x_3962_, v___x_3964_);
lean_dec(v___x_3962_);
v_args_3990_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3936_, v___x_3988_, v___x_3989_);
v___x_3991_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3992_ = lean_array_get(v___x_3986_, v_args_3990_, v___x_3991_);
v_00_u03b2_3993_ = lean_array_get(v___x_3986_, v_args_3990_, v___x_3964_);
v___x_3994_ = l_Lean_Expr_fvarId_x21(v_F_3935_);
v___x_3995_ = l_Lean_FVarId_getDecl___redArg(v___x_3994_, v_a_3940_, v_a_3942_, v_a_3943_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3997_; lean_object* v___f_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___f_4004_; lean_object* v___x_4005_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_n(v_a_3996_, 2);
lean_dec_ref_known(v___x_3995_, 1);
v___x_3997_ = lean_box(v___x_3973_);
lean_inc_ref_n(v_x_3934_, 2);
v___f_3998_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3998_, 0, v_a_3996_);
lean_closure_set(v___f_3998_, 1, v___x_3986_);
lean_closure_set(v___f_3998_, 2, v___x_3991_);
lean_closure_set(v___f_3998_, 3, v_x_3934_);
lean_closure_set(v___f_3998_, 4, v___x_3997_);
v___x_3999_ = lean_unsigned_to_nat(2u);
v___x_4000_ = lean_array_get_borrowed(v___x_3986_, v_args_3990_, v___x_3999_);
v___x_4001_ = 0;
v___x_4002_ = lean_box(v___x_4001_);
v___x_4003_ = lean_box(v___x_3973_);
lean_inc(v_00_u03b2_3993_);
lean_inc(v_00_u03b1_3992_);
v___f_4004_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 23, 14);
lean_closure_set(v___f_4004_, 0, v___x_3986_);
lean_closure_set(v___f_4004_, 1, v___x_3991_);
lean_closure_set(v___f_4004_, 2, v___x_3964_);
lean_closure_set(v___f_4004_, 3, v___x_3999_);
lean_closure_set(v___f_4004_, 4, v___x_4002_);
lean_closure_set(v___f_4004_, 5, v___x_4003_);
lean_closure_set(v___f_4004_, 6, v_k_3937_);
lean_closure_set(v___f_4004_, 7, v___x_3961_);
lean_closure_set(v___f_4004_, 8, v___x_3956_);
lean_closure_set(v___f_4004_, 9, v_00_u03b1_3992_);
lean_closure_set(v___f_4004_, 10, v_00_u03b2_3993_);
lean_closure_set(v___f_4004_, 11, v___x_3969_);
lean_closure_set(v___f_4004_, 12, v_a_3996_);
lean_closure_set(v___f_4004_, 13, v_x_3934_);
lean_inc(v___x_4000_);
v___x_4005_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4000_, v___f_3998_, v___x_4001_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v_fst_4007_; lean_object* v_snd_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v_fst_4007_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_fst_4007_);
v_snd_4008_ = lean_ctor_get(v_a_4006_, 1);
lean_inc(v_snd_4008_);
lean_dec(v_a_4006_);
v___x_4009_ = lean_array_get(v___x_3986_, v_args_3990_, v___x_3969_);
lean_dec_ref(v_args_3990_);
v___x_4010_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4009_, v___f_4004_, v___x_4001_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4031_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4031_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4031_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v_tail_3980_);
lean_ctor_set(v___x_3984_, 0, v_snd_4008_);
v___x_4016_ = v___x_3984_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_snd_4008_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_tail_3980_);
v___x_4016_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4017_ = l_Lean_mkConst(v___x_3957_, v___x_4016_);
v___x_4018_ = lean_unsigned_to_nat(6u);
v___x_4019_ = lean_mk_empty_array_with_capacity(v___x_4018_);
v___x_4020_ = lean_array_push(v___x_4019_, v_00_u03b1_3992_);
v___x_4021_ = lean_array_push(v___x_4020_, v_00_u03b2_3993_);
v___x_4022_ = lean_array_push(v___x_4021_, v_fst_4007_);
v___x_4023_ = lean_array_push(v___x_4022_, v_x_3934_);
v___x_4024_ = lean_array_push(v___x_4023_, v_a_4011_);
v___x_4025_ = lean_array_push(v___x_4024_, v_F_3935_);
v___x_4026_ = l_Lean_mkAppN(v___x_4017_, v___x_4025_);
lean_dec_ref(v___x_4025_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4026_);
v___x_4028_ = v___x_4013_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_dec(v_snd_4008_);
lean_dec(v_fst_4007_);
lean_dec(v_00_u03b2_3993_);
lean_dec(v_00_u03b1_3992_);
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
return v___x_4010_;
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v___f_4004_);
lean_dec(v_00_u03b2_3993_);
lean_dec(v_00_u03b1_3992_);
lean_dec_ref(v_args_3990_);
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v_a_4032_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4005_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4005_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_00_u03b2_3993_);
lean_dec(v_00_u03b1_3992_);
lean_dec_ref(v_args_3990_);
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec_ref(v_k_3937_);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v_a_4040_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_3995_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_3995_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
else
{
lean_del_object(v___x_3984_);
lean_dec(v_tail_3982_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3937_);
lean_dec_ref(v_val_3936_);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
goto v___jp_3945_;
}
}
}
else
{
lean_dec(v_tail_3981_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3937_);
lean_dec_ref(v_val_3936_);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
goto v___jp_3945_;
}
}
else
{
lean_dec(v_tail_3980_);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3937_);
lean_dec_ref(v_val_3936_);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
goto v___jp_3945_;
}
}
else
{
lean_dec(v___x_3979_);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3937_);
lean_dec_ref(v_val_3936_);
lean_dec_ref(v_F_3935_);
lean_dec_ref(v_x_3934_);
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
v___y_3948_ = v_a_3940_;
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
goto v___jp_3945_;
}
}
}
}
}
}
v___jp_3945_:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3953_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3952_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3953_;
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
size_t v_x_3984__boxed_4295_; size_t v_x_3985__boxed_4296_; lean_object* v_res_4297_; 
v_x_3984__boxed_4295_ = lean_unbox_usize(v_x_4291_);
lean_dec(v_x_4291_);
v_x_3985__boxed_4296_ = lean_unbox_usize(v_x_4292_);
lean_dec(v_x_4292_);
v_res_4297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4290_, v_x_3984__boxed_4295_, v_x_3985__boxed_4296_, v_x_4293_, v_x_4294_);
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
lean_object* v___x_4309_; lean_object* v_mctx_4310_; lean_object* v_cache_4311_; lean_object* v_zetaDeltaFVarIds_4312_; lean_object* v_postponed_4313_; lean_object* v_diag_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4344_; 
v___x_4309_ = lean_st_ref_take(v___y_4307_);
v_mctx_4310_ = lean_ctor_get(v___x_4309_, 0);
v_cache_4311_ = lean_ctor_get(v___x_4309_, 1);
v_zetaDeltaFVarIds_4312_ = lean_ctor_get(v___x_4309_, 2);
v_postponed_4313_ = lean_ctor_get(v___x_4309_, 3);
v_diag_4314_ = lean_ctor_get(v___x_4309_, 4);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4316_ = v___x_4309_;
v_isShared_4317_ = v_isSharedCheck_4344_;
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
v_isShared_4317_ = v_isSharedCheck_4344_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_depth_4318_; lean_object* v_levelAssignDepth_4319_; lean_object* v_lmvarCounter_4320_; lean_object* v_mvarCounter_4321_; lean_object* v_lDecls_4322_; lean_object* v_decls_4323_; lean_object* v_userNames_4324_; lean_object* v_lAssignment_4325_; lean_object* v_eAssignment_4326_; lean_object* v_dAssignment_4327_; lean_object* v_instanceTypedMVars_4328_; lean_object* v_synthNormMemo_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4343_; 
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
v_synthNormMemo_4329_ = lean_ctor_get(v_mctx_4310_, 11);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_mctx_4310_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4331_ = v_mctx_4310_;
v_isShared_4332_ = v_isSharedCheck_4343_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_synthNormMemo_4329_);
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
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4343_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4333_ = lean_box(0);
v___x_4334_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4326_, v_mvarId_4305_, v_val_4306_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 8, v___x_4334_);
v___x_4336_ = v___x_4331_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_depth_4318_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_levelAssignDepth_4319_);
lean_ctor_set(v_reuseFailAlloc_4342_, 2, v_lmvarCounter_4320_);
lean_ctor_set(v_reuseFailAlloc_4342_, 3, v_mvarCounter_4321_);
lean_ctor_set(v_reuseFailAlloc_4342_, 4, v_lDecls_4322_);
lean_ctor_set(v_reuseFailAlloc_4342_, 5, v_decls_4323_);
lean_ctor_set(v_reuseFailAlloc_4342_, 6, v_userNames_4324_);
lean_ctor_set(v_reuseFailAlloc_4342_, 7, v_lAssignment_4325_);
lean_ctor_set(v_reuseFailAlloc_4342_, 8, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4342_, 9, v_dAssignment_4327_);
lean_ctor_set(v_reuseFailAlloc_4342_, 10, v_instanceTypedMVars_4328_);
lean_ctor_set(v_reuseFailAlloc_4342_, 11, v_synthNormMemo_4329_);
v___x_4336_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4338_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4336_);
v___x_4338_ = v___x_4316_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_cache_4311_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_zetaDeltaFVarIds_4312_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_postponed_4313_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_diag_4314_);
v___x_4338_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_st_ref_put(v___y_4307_, v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4333_);
return v___x_4340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4345_, lean_object* v_val_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4345_, v_val_4346_, v___y_4347_);
lean_dec(v___y_4347_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4354_, lean_object* v_mv_u2082_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4364_; 
lean_inc(v_mv_u2081_4354_);
v___x_4364_ = l_Lean_MVarId_getDecl(v_mv_u2081_4354_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
lean_inc(v_mv_u2082_4355_);
v___x_4366_ = l_Lean_MVarId_getDecl(v_mv_u2082_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v_lctx_4368_; lean_object* v_type_4369_; lean_object* v_lctx_4370_; lean_object* v_type_4371_; uint8_t v___x_4372_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4367_);
lean_dec_ref_known(v___x_4366_, 1);
v_lctx_4368_ = lean_ctor_get(v_a_4365_, 1);
lean_inc_ref(v_lctx_4368_);
v_type_4369_ = lean_ctor_get(v_a_4365_, 2);
lean_inc_ref(v_type_4369_);
lean_dec(v_a_4365_);
v_lctx_4370_ = lean_ctor_get(v_a_4367_, 1);
lean_inc_ref(v_lctx_4370_);
v_type_4371_ = lean_ctor_get(v_a_4367_, 2);
lean_inc_ref(v_type_4371_);
lean_dec(v_a_4367_);
v___x_4372_ = lean_expr_eqv(v_type_4369_, v_type_4371_);
lean_dec_ref(v_type_4371_);
lean_dec_ref(v_type_4369_);
if (v___x_4372_ == 0)
{
lean_dec_ref(v_lctx_4370_);
lean_dec_ref(v_lctx_4368_);
lean_dec(v_mv_u2082_4355_);
lean_dec(v_mv_u2081_4354_);
goto v___jp_4361_;
}
else
{
lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4373_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4374_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4368_, v_lctx_4370_, v___x_4373_);
if (v___x_4374_ == 0)
{
uint8_t v___x_4375_; 
v___x_4375_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4370_, v_lctx_4368_, v___x_4373_);
lean_dec_ref(v_lctx_4368_);
lean_dec_ref(v_lctx_4370_);
if (v___x_4375_ == 0)
{
lean_dec(v_mv_u2082_4355_);
lean_dec(v_mv_u2081_4354_);
goto v___jp_4361_;
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4387_; 
v___x_4376_ = l_Lean_Expr_mvar___override(v_mv_u2082_4355_);
v___x_4377_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4354_, v___x_4376_, v___y_4357_);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; 
v_unused_4388_ = lean_ctor_get(v___x_4377_, 0);
lean_dec(v_unused_4388_);
v___x_4379_ = v___x_4377_;
v_isShared_4380_ = v_isSharedCheck_4387_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v___x_4377_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4387_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4381_ = lean_box(v___x_4374_);
v___x_4382_ = lean_box(v___x_4372_);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4383_);
v___x_4385_ = v___x_4379_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4401_; 
lean_dec_ref(v_lctx_4370_);
lean_dec_ref(v_lctx_4368_);
v___x_4389_ = l_Lean_Expr_mvar___override(v_mv_u2081_4354_);
v___x_4390_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4355_, v___x_4389_, v___y_4357_);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4401_ == 0)
{
lean_object* v_unused_4402_; 
v_unused_4402_ = lean_ctor_get(v___x_4390_, 0);
lean_dec(v_unused_4402_);
v___x_4392_ = v___x_4390_;
v_isShared_4393_ = v_isSharedCheck_4401_;
goto v_resetjp_4391_;
}
else
{
lean_dec(v___x_4390_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4401_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
uint8_t v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4394_ = 0;
v___x_4395_ = lean_box(v___x_4372_);
v___x_4396_ = lean_box(v___x_4394_);
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4397_);
v___x_4399_ = v___x_4392_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4365_);
lean_dec(v_mv_u2082_4355_);
lean_dec(v_mv_u2081_4354_);
v_a_4403_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4366_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4366_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_mv_u2082_4355_);
lean_dec(v_mv_u2081_4354_);
v_a_4411_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4364_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4364_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
v___jp_4361_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
return v___x_4363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4419_, lean_object* v_mv_u2082_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4419_, v_mv_u2082_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v_f_4427_, lean_object* v___x_4428_, lean_object* v___x_4429_, lean_object* v___x_4430_, lean_object* v_a_4431_, uint8_t v___x_4432_, lean_object* v_snd_4433_, lean_object* v_fst_4434_, lean_object* v_next_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_apply_7(v_f_4427_, v___x_4428_, v___x_4429_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, lean_box(0));
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4477_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4444_ = v___x_4441_;
v_isShared_4445_ = v_isSharedCheck_4477_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4441_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4477_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_fst_4446_; lean_object* v_snd_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4476_; 
v_fst_4446_ = lean_ctor_get(v_a_4442_, 0);
v_snd_4447_ = lean_ctor_get(v_a_4442_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_4442_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4449_ = v_a_4442_;
v_isShared_4450_ = v_isSharedCheck_4476_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_snd_4447_);
lean_inc(v_fst_4446_);
lean_dec(v_a_4442_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4476_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v_removed_4452_; lean_object* v_numRemoved_4453_; uint8_t v___x_4472_; 
v___x_4472_ = lean_unbox(v_fst_4446_);
lean_dec(v_fst_4446_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4473_ = lean_nat_add(v_snd_4433_, v___x_4430_);
lean_dec(v_snd_4433_);
v___x_4474_ = lean_box(v___x_4432_);
v___x_4475_ = lean_array_set(v_fst_4434_, v_next_4435_, v___x_4474_);
v_removed_4452_ = v___x_4475_;
v_numRemoved_4453_ = v___x_4473_;
goto v___jp_4451_;
}
else
{
v_removed_4452_ = v_fst_4434_;
v_numRemoved_4453_ = v_snd_4433_;
goto v___jp_4451_;
}
v___jp_4451_:
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_unbox(v_snd_4447_);
lean_dec(v_snd_4447_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4455_ = lean_nat_add(v_numRemoved_4453_, v___x_4430_);
lean_dec(v_numRemoved_4453_);
v___x_4456_ = lean_box(v___x_4432_);
v___x_4457_ = lean_array_set(v_removed_4452_, v_a_4431_, v___x_4456_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v___x_4455_);
lean_ctor_set(v___x_4449_, 0, v___x_4457_);
v___x_4459_ = v___x_4449_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___x_4455_);
v___x_4459_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4460_);
v___x_4462_ = v___x_4444_;
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
else
{
lean_object* v___x_4466_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v_numRemoved_4453_);
lean_ctor_set(v___x_4449_, 0, v_removed_4452_);
v___x_4466_ = v___x_4449_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_removed_4452_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_numRemoved_4453_);
v___x_4466_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4467_);
v___x_4469_ = v___x_4444_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec(v_fst_4434_);
lean_dec(v_snd_4433_);
v_a_4478_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4441_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4441_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v_f_4486_, lean_object* v___x_4487_, lean_object* v___x_4488_, lean_object* v___x_4489_, lean_object* v_a_4490_, lean_object* v___x_4491_, lean_object* v_snd_4492_, lean_object* v_fst_4493_, lean_object* v_next_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v___x_4337__boxed_4500_; lean_object* v_res_4501_; 
v___x_4337__boxed_4500_ = lean_unbox(v___x_4491_);
v_res_4501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v_f_4486_, v___x_4487_, v___x_4488_, v___x_4489_, v_a_4490_, v___x_4337__boxed_4500_, v_snd_4492_, v_fst_4493_, v_next_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v_next_4494_);
lean_dec(v_a_4490_);
lean_dec(v___x_4489_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v___x_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4502_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___x_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v___x_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4516_, lean_object* v_next_4517_, lean_object* v_a_4518_, lean_object* v_f_4519_, lean_object* v_a_4520_, lean_object* v_b_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v___x_4527_; 
v___x_4527_ = lean_nat_dec_lt(v_a_4520_, v_upperBound_4516_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; 
lean_dec(v_a_4520_);
lean_dec_ref(v_f_4519_);
lean_dec(v_next_4517_);
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v_b_4521_);
return v___x_4528_;
}
else
{
lean_object* v_fst_4529_; lean_object* v_snd_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4575_; 
v_fst_4529_ = lean_ctor_get(v_b_4521_, 0);
v_snd_4530_ = lean_ctor_get(v_b_4521_, 1);
v_isSharedCheck_4575_ = !lean_is_exclusive(v_b_4521_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4532_ = v_b_4521_;
v_isShared_4533_ = v_isSharedCheck_4575_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_snd_4530_);
lean_inc(v_fst_4529_);
lean_dec(v_b_4521_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4575_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___y_4536_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
v___x_4534_ = lean_unsigned_to_nat(1u);
v___x_4564_ = 0;
v___x_4565_ = lean_box(v___x_4564_);
v___x_4566_ = lean_array_get(v___x_4565_, v_fst_4529_, v_next_4517_);
lean_dec(v___x_4565_);
v___x_4567_ = lean_unbox(v___x_4566_);
lean_dec(v___x_4566_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v___x_4568_ = lean_box(v___x_4564_);
v___x_4569_ = lean_array_get(v___x_4568_, v_fst_4529_, v_a_4520_);
lean_dec(v___x_4568_);
v___x_4570_ = lean_unbox(v___x_4569_);
lean_dec(v___x_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___f_4574_; 
lean_del_object(v___x_4532_);
v___x_4571_ = lean_array_fget_borrowed(v_a_4518_, v_next_4517_);
v___x_4572_ = lean_array_fget_borrowed(v_a_4518_, v_a_4520_);
v___x_4573_ = lean_box(v___x_4527_);
lean_inc(v_next_4517_);
lean_inc(v_a_4520_);
lean_inc(v___x_4572_);
lean_inc(v___x_4571_);
lean_inc_ref(v_f_4519_);
v___f_4574_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_4574_, 0, v_f_4519_);
lean_closure_set(v___f_4574_, 1, v___x_4571_);
lean_closure_set(v___f_4574_, 2, v___x_4572_);
lean_closure_set(v___f_4574_, 3, v___x_4534_);
lean_closure_set(v___f_4574_, 4, v_a_4520_);
lean_closure_set(v___f_4574_, 5, v___x_4573_);
lean_closure_set(v___f_4574_, 6, v_snd_4530_);
lean_closure_set(v___f_4574_, 7, v_fst_4529_);
lean_closure_set(v___f_4574_, 8, v_next_4517_);
v___y_4536_ = v___f_4574_;
goto v___jp_4535_;
}
else
{
goto v___jp_4558_;
}
}
else
{
goto v___jp_4558_;
}
v___jp_4535_:
{
lean_object* v___x_4537_; 
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc(v___y_4523_);
lean_inc_ref(v___y_4522_);
v___x_4537_ = lean_apply_5(v___y_4536_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, lean_box(0));
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4549_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4549_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4549_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
if (lean_obj_tag(v_a_4538_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; 
lean_dec(v_a_4520_);
lean_dec_ref(v_f_4519_);
lean_dec(v_next_4517_);
v_a_4542_ = lean_ctor_get(v_a_4538_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v_a_4538_, 1);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v_a_4542_);
v___x_4544_ = v___x_4540_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4547_; 
lean_del_object(v___x_4540_);
v_a_4546_ = lean_ctor_get(v_a_4538_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v_a_4538_, 1);
v___x_4547_ = lean_nat_add(v_a_4520_, v___x_4534_);
lean_dec(v_a_4520_);
v_a_4520_ = v___x_4547_;
v_b_4521_ = v_a_4546_;
goto _start;
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4557_; 
lean_dec(v_a_4520_);
lean_dec_ref(v_f_4519_);
lean_dec(v_next_4517_);
v_a_4550_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4552_ = v___x_4537_;
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4537_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4553_ == 0)
{
v___x_4555_ = v___x_4552_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
v___jp_4558_:
{
lean_object* v___x_4560_; 
if (v_isShared_4533_ == 0)
{
v___x_4560_ = v___x_4532_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_fst_4529_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v_snd_4530_);
v___x_4560_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
lean_object* v___x_4561_; lean_object* v___f_4562_; 
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
v___f_4562_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4562_, 0, v___x_4561_);
v___y_4536_ = v___f_4562_;
goto v___jp_4535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4576_, lean_object* v_next_4577_, lean_object* v_a_4578_, lean_object* v_f_4579_, lean_object* v_a_4580_, lean_object* v_b_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4576_, v_next_4577_, v_a_4578_, v_f_4579_, v_a_4580_, v_b_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec_ref(v_a_4578_);
lean_dec(v_upperBound_4576_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4588_, lean_object* v___x_4589_, lean_object* v_a_4590_, lean_object* v_f_4591_, lean_object* v_a_4592_, lean_object* v_b_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
uint8_t v___x_4599_; 
v___x_4599_ = lean_nat_dec_lt(v_a_4592_, v_upperBound_4588_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; 
lean_dec(v_a_4592_);
lean_dec_ref(v_f_4591_);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_b_4593_);
return v___x_4600_;
}
else
{
lean_object* v_fst_4601_; lean_object* v_snd_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4623_; 
v_fst_4601_ = lean_ctor_get(v_b_4593_, 0);
v_snd_4602_ = lean_ctor_get(v_b_4593_, 1);
v_isSharedCheck_4623_ = !lean_is_exclusive(v_b_4593_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4604_ = v_b_4593_;
v_isShared_4605_ = v_isSharedCheck_4623_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_snd_4602_);
lean_inc(v_fst_4601_);
lean_dec(v_b_4593_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4623_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4606_ = lean_unsigned_to_nat(1u);
v___x_4607_ = lean_nat_add(v_a_4592_, v___x_4606_);
if (v_isShared_4605_ == 0)
{
v___x_4609_ = v___x_4604_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_fst_4601_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_snd_4602_);
v___x_4609_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; 
lean_inc(v___x_4607_);
lean_inc_ref(v_f_4591_);
v___x_4610_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4589_, v_a_4592_, v_a_4590_, v_f_4591_, v___x_4607_, v___x_4609_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v_fst_4612_; lean_object* v_snd_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4621_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_a_4611_);
lean_dec_ref_known(v___x_4610_, 1);
v_fst_4612_ = lean_ctor_get(v_a_4611_, 0);
v_snd_4613_ = lean_ctor_get(v_a_4611_, 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_a_4611_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4615_ = v_a_4611_;
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_snd_4613_);
lean_inc(v_fst_4612_);
lean_dec(v_a_4611_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_fst_4612_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_snd_4613_);
v___x_4618_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
v_a_4592_ = v___x_4607_;
v_b_4593_ = v___x_4618_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4607_);
lean_dec_ref(v_f_4591_);
return v___x_4610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4624_, lean_object* v___x_4625_, lean_object* v_a_4626_, lean_object* v_f_4627_, lean_object* v_a_4628_, lean_object* v_b_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4624_, v___x_4625_, v_a_4626_, v_f_4627_, v_a_4628_, v_b_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec_ref(v_a_4626_);
lean_dec(v___x_4625_);
lean_dec(v_upperBound_4624_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4636_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4650_, lean_object* v_removed_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___y_4661_; uint8_t v___x_4684_; 
v___x_4684_ = lean_nat_dec_lt(v_a_4653_, v_upperBound_4650_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; 
lean_dec(v_a_4653_);
v___x_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4685_, 0, v_b_4654_);
return v___x_4685_;
}
else
{
uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v___x_4686_ = 0;
v___x_4687_ = lean_box(v___x_4686_);
v___x_4688_ = lean_array_get(v___x_4687_, v_removed_4651_, v_a_4653_);
lean_dec(v___x_4687_);
v___x_4689_ = lean_unbox(v___x_4688_);
lean_dec(v___x_4688_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___f_4693_; 
v___x_4690_ = lean_array_fget_borrowed(v_a_4652_, v_a_4653_);
lean_inc(v___x_4690_);
v___x_4691_ = lean_array_push(v_b_4654_, v___x_4690_);
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
v___f_4693_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4693_, 0, v___x_4692_);
v___y_4661_ = v___f_4693_;
goto v___jp_4660_;
}
else
{
lean_object* v___x_4694_; lean_object* v___f_4695_; 
v___x_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_b_4654_);
v___f_4695_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4695_, 0, v___x_4694_);
v___y_4661_ = v___f_4695_;
goto v___jp_4660_;
}
}
v___jp_4660_:
{
lean_object* v___x_4662_; 
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
v___x_4662_ = lean_apply_5(v___y_4661_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, lean_box(0));
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4675_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4665_ = v___x_4662_;
v_isShared_4666_ = v_isSharedCheck_4675_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4662_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4675_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
if (lean_obj_tag(v_a_4663_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4669_; 
lean_dec(v_a_4653_);
v_a_4667_ = lean_ctor_get(v_a_4663_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v_a_4663_, 1);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 0, v_a_4667_);
v___x_4669_ = v___x_4665_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_del_object(v___x_4665_);
v_a_4671_ = lean_ctor_get(v_a_4663_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v_a_4663_, 1);
v___x_4672_ = lean_unsigned_to_nat(1u);
v___x_4673_ = lean_nat_add(v_a_4653_, v___x_4672_);
lean_dec(v_a_4653_);
v_a_4653_ = v___x_4673_;
v_b_4654_ = v_a_4671_;
goto _start;
}
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_dec(v_a_4653_);
v_a_4676_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4662_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4662_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4696_, lean_object* v_removed_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_b_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4696_, v_removed_4697_, v_a_4698_, v_a_4699_, v_b_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec_ref(v_a_4698_);
lean_dec_ref(v_removed_4697_);
lean_dec(v_upperBound_4696_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4707_, lean_object* v_f_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; uint8_t v___x_4715_; lean_object* v___x_4716_; lean_object* v_removed_4717_; lean_object* v_numRemoved_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4714_ = lean_array_get_size(v_a_4707_);
v___x_4715_ = 0;
v___x_4716_ = lean_box(v___x_4715_);
v_removed_4717_ = lean_mk_array(v___x_4714_, v___x_4716_);
v_numRemoved_4718_ = lean_unsigned_to_nat(0u);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_removed_4717_);
lean_ctor_set(v___x_4719_, 1, v_numRemoved_4718_);
v___x_4720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4714_, v___x_4714_, v_a_4707_, v_f_4708_, v_numRemoved_4718_, v___x_4719_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_fst_4722_; lean_object* v_snd_4723_; lean_object* v_a_x27_4724_; lean_object* v___x_4725_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v_fst_4722_ = lean_ctor_get(v_a_4721_, 0);
lean_inc(v_fst_4722_);
v_snd_4723_ = lean_ctor_get(v_a_4721_, 1);
lean_inc(v_snd_4723_);
lean_dec(v_a_4721_);
v_a_x27_4724_ = lean_mk_empty_array_with_capacity(v_snd_4723_);
lean_dec(v_snd_4723_);
v___x_4725_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4714_, v_fst_4722_, v_a_4707_, v_numRemoved_4718_, v_a_x27_4724_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v_fst_4722_);
return v___x_4725_;
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
v_a_4726_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4720_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4720_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4734_, lean_object* v_f_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4734_, v_f_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec_ref(v_a_4734_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v___f_4749_; lean_object* v___x_4750_; 
v___f_4749_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4750_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4743_, v___f_4749_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec_ref(v_mvars_4751_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4758_, lean_object* v_val_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4758_, v_val_4759_, v___y_4761_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4766_, lean_object* v_val_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4766_, v_val_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4774_, lean_object* v_a_4775_, lean_object* v_f_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4775_, v_f_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4783_, lean_object* v_a_4784_, lean_object* v_f_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4783_, v_a_4784_, v_f_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec_ref(v_a_4784_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4792_, lean_object* v_x_4793_, lean_object* v_x_4794_, lean_object* v_x_4795_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4793_, v_x_4794_, v_x_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4797_, lean_object* v_next_4798_, lean_object* v_00_u03b1_4799_, lean_object* v_a_4800_, lean_object* v_f_4801_, lean_object* v_inst_4802_, lean_object* v_R_4803_, lean_object* v_a_4804_, lean_object* v_b_4805_, lean_object* v_c_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4797_, v_next_4798_, v_a_4800_, v_f_4801_, v_a_4804_, v_b_4805_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4813_, lean_object* v_next_4814_, lean_object* v_00_u03b1_4815_, lean_object* v_a_4816_, lean_object* v_f_4817_, lean_object* v_inst_4818_, lean_object* v_R_4819_, lean_object* v_a_4820_, lean_object* v_b_4821_, lean_object* v_c_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4813_, v_next_4814_, v_00_u03b1_4815_, v_a_4816_, v_f_4817_, v_inst_4818_, v_R_4819_, v_a_4820_, v_b_4821_, v_c_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec_ref(v_a_4816_);
lean_dec(v_upperBound_4813_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4829_, lean_object* v_upperBound_4830_, lean_object* v_removed_4831_, lean_object* v_a_4832_, lean_object* v_inst_4833_, lean_object* v_R_4834_, lean_object* v_a_4835_, lean_object* v_b_4836_, lean_object* v_c_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4830_, v_removed_4831_, v_a_4832_, v_a_4835_, v_b_4836_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4844_, lean_object* v_upperBound_4845_, lean_object* v_removed_4846_, lean_object* v_a_4847_, lean_object* v_inst_4848_, lean_object* v_R_4849_, lean_object* v_a_4850_, lean_object* v_b_4851_, lean_object* v_c_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4844_, v_upperBound_4845_, v_removed_4846_, v_a_4847_, v_inst_4848_, v_R_4849_, v_a_4850_, v_b_4851_, v_c_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec_ref(v_a_4847_);
lean_dec_ref(v_removed_4846_);
lean_dec(v_upperBound_4845_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4859_, lean_object* v___x_4860_, lean_object* v_00_u03b1_4861_, lean_object* v_a_4862_, lean_object* v_f_4863_, lean_object* v_inst_4864_, lean_object* v_R_4865_, lean_object* v_a_4866_, lean_object* v_b_4867_, lean_object* v_c_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v___x_4874_; 
v___x_4874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4859_, v___x_4860_, v_a_4862_, v_f_4863_, v_a_4866_, v_b_4867_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4875_, lean_object* v___x_4876_, lean_object* v_00_u03b1_4877_, lean_object* v_a_4878_, lean_object* v_f_4879_, lean_object* v_inst_4880_, lean_object* v_R_4881_, lean_object* v_a_4882_, lean_object* v_b_4883_, lean_object* v_c_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4875_, v___x_4876_, v_00_u03b1_4877_, v_a_4878_, v_f_4879_, v_inst_4880_, v_R_4881_, v_a_4882_, v_b_4883_, v_c_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec_ref(v_a_4878_);
lean_dec(v___x_4876_);
lean_dec(v_upperBound_4875_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4891_, lean_object* v_x_4892_, size_t v_x_4893_, size_t v_x_4894_, lean_object* v_x_4895_, lean_object* v_x_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4892_, v_x_4893_, v_x_4894_, v_x_4895_, v_x_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4898_, lean_object* v_x_4899_, lean_object* v_x_4900_, lean_object* v_x_4901_, lean_object* v_x_4902_, lean_object* v_x_4903_){
_start:
{
size_t v_x_4923__boxed_4904_; size_t v_x_4924__boxed_4905_; lean_object* v_res_4906_; 
v_x_4923__boxed_4904_ = lean_unbox_usize(v_x_4900_);
lean_dec(v_x_4900_);
v_x_4924__boxed_4905_ = lean_unbox_usize(v_x_4901_);
lean_dec(v_x_4901_);
v_res_4906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4898_, v_x_4899_, v_x_4923__boxed_4904_, v_x_4924__boxed_4905_, v_x_4902_, v_x_4903_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4907_, lean_object* v_n_4908_, lean_object* v_k_4909_, lean_object* v_v_4910_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4908_, v_k_4909_, v_v_4910_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4912_, size_t v_depth_4913_, lean_object* v_keys_4914_, lean_object* v_vals_4915_, lean_object* v_heq_4916_, lean_object* v_i_4917_, lean_object* v_entries_4918_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4913_, v_keys_4914_, v_vals_4915_, v_i_4917_, v_entries_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4920_, lean_object* v_depth_4921_, lean_object* v_keys_4922_, lean_object* v_vals_4923_, lean_object* v_heq_4924_, lean_object* v_i_4925_, lean_object* v_entries_4926_){
_start:
{
size_t v_depth_boxed_4927_; lean_object* v_res_4928_; 
v_depth_boxed_4927_ = lean_unbox_usize(v_depth_4921_);
lean_dec(v_depth_4921_);
v_res_4928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4920_, v_depth_boxed_4927_, v_keys_4922_, v_vals_4923_, v_heq_4924_, v_i_4925_, v_entries_4926_);
lean_dec_ref(v_vals_4923_);
lean_dec_ref(v_keys_4922_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4929_, lean_object* v_x_4930_, lean_object* v_x_4931_, lean_object* v_x_4932_, lean_object* v_x_4933_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4930_, v_x_4931_, v_x_4932_, v_x_4933_);
return v___x_4934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4937_ = l_Lean_stringToMessageData(v___x_4936_);
return v___x_4937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4940_ = l_Lean_stringToMessageData(v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4941_, lean_object* v_as_4942_, size_t v_sz_4943_, size_t v_i_4944_, lean_object* v_b_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v_a_4952_; uint8_t v___x_4956_; 
v___x_4956_ = lean_usize_dec_lt(v_i_4944_, v_sz_4943_);
if (v___x_4956_ == 0)
{
lean_object* v___x_4957_; 
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_b_4945_);
return v___x_4957_;
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4959_; 
v_a_4958_ = lean_array_uget_borrowed(v_as_4942_, v_i_4944_);
lean_inc(v_a_4958_);
v___x_4959_ = l_Lean_MVarId_getType(v_a_4958_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___y_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4960_);
lean_dec_ref_known(v___x_4959_, 1);
if (lean_obj_tag(v_a_4960_) == 10)
{
lean_object* v_expr_4978_; 
v_expr_4978_ = lean_ctor_get(v_a_4960_, 1);
if (lean_obj_tag(v_expr_4978_) == 5)
{
lean_object* v_arg_4979_; lean_object* v___x_4980_; 
lean_inc_ref(v_expr_4978_);
lean_dec_ref_known(v_a_4960_, 2);
v_arg_4979_ = lean_ctor_get(v_expr_4978_, 1);
lean_inc_ref_n(v_arg_4979_, 2);
lean_dec_ref_known(v_expr_4978_, 2);
v___x_4980_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4941_, v_arg_4979_);
if (lean_obj_tag(v___x_4980_) == 1)
{
lean_object* v_val_4981_; lean_object* v_fst_4982_; lean_object* v___x_4983_; uint8_t v___x_4984_; 
lean_dec_ref(v_arg_4979_);
v_val_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_val_4981_);
lean_dec_ref_known(v___x_4980_, 1);
v_fst_4982_ = lean_ctor_get(v_val_4981_, 0);
lean_inc(v_fst_4982_);
lean_dec(v_val_4981_);
v___x_4983_ = lean_array_get_size(v_b_4945_);
v___x_4984_ = lean_nat_dec_lt(v_fst_4982_, v___x_4983_);
if (v___x_4984_ == 0)
{
lean_dec(v_fst_4982_);
v_a_4952_ = v_b_4945_;
goto v___jp_4951_;
}
else
{
lean_object* v_v_4985_; lean_object* v___x_4986_; lean_object* v_xs_x27_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_v_4985_ = lean_array_fget(v_b_4945_, v_fst_4982_);
v___x_4986_ = lean_box(0);
v_xs_x27_4987_ = lean_array_fset(v_b_4945_, v_fst_4982_, v___x_4986_);
lean_inc(v_a_4958_);
v___x_4988_ = lean_array_push(v_v_4985_, v_a_4958_);
v___x_4989_ = lean_array_fset(v_xs_x27_4987_, v_fst_4982_, v___x_4988_);
lean_dec(v_fst_4982_);
v_a_4952_ = v___x_4989_;
goto v___jp_4951_;
}
}
else
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec(v___x_4980_);
v___x_4990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_4991_ = l_Lean_indentExpr(v_arg_4979_);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4992_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_dec_ref_known(v___x_4993_, 1);
v_a_4952_ = v_b_4945_;
goto v___jp_4951_;
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec_ref(v_b_4945_);
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
v___y_4962_ = v___y_4946_;
v___y_4963_ = v___y_4947_;
v___y_4964_ = v___y_4948_;
v___y_4965_ = v___y_4949_;
goto v___jp_4961_;
}
}
else
{
v___y_4962_ = v___y_4946_;
v___y_4963_ = v___y_4947_;
v___y_4964_ = v___y_4948_;
v___y_4965_ = v___y_4949_;
goto v___jp_4961_;
}
v___jp_4961_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4967_ = l_Lean_indentExpr(v_a_4960_);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4966_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4968_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_dec_ref_known(v___x_4969_, 1);
v_a_4952_ = v_b_4945_;
goto v___jp_4951_;
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_dec_ref(v_b_4945_);
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec_ref(v_b_4945_);
v_a_5002_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4959_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4959_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
v___jp_4951_:
{
size_t v___x_4953_; size_t v___x_4954_; 
v___x_4953_ = ((size_t)1ULL);
v___x_4954_ = lean_usize_add(v_i_4944_, v___x_4953_);
v_i_4944_ = v___x_4954_;
v_b_4945_ = v_a_4952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5010_, lean_object* v_as_5011_, lean_object* v_sz_5012_, lean_object* v_i_5013_, lean_object* v_b_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
size_t v_sz_boxed_5020_; size_t v_i_boxed_5021_; lean_object* v_res_5022_; 
v_sz_boxed_5020_ = lean_unbox_usize(v_sz_5012_);
lean_dec(v_sz_5012_);
v_i_boxed_5021_ = lean_unbox_usize(v_i_5013_);
lean_dec(v_i_5013_);
v_res_5022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5010_, v_as_5011_, v_sz_boxed_5020_, v_i_boxed_5021_, v_b_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec_ref(v_as_5011_);
lean_dec_ref(v_argsPacker_5010_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5023_, lean_object* v_numFuncs_5024_, lean_object* v_goals_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_){
_start:
{
lean_object* v___x_5031_; lean_object* v_r_5032_; size_t v_sz_5033_; size_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5031_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5032_ = lean_mk_array(v_numFuncs_5024_, v___x_5031_);
v_sz_5033_ = lean_array_size(v_goals_5025_);
v___x_5034_ = ((size_t)0ULL);
v___x_5035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5023_, v_goals_5025_, v_sz_5033_, v___x_5034_, v_r_5032_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5036_, lean_object* v_numFuncs_5037_, lean_object* v_goals_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5036_, v_numFuncs_5037_, v_goals_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec_ref(v_goals_5038_);
lean_dec_ref(v_argsPacker_5036_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v___x_5048_; lean_object* v_infoState_5049_; uint8_t v_enabled_5050_; 
v___x_5048_ = lean_st_ref_get(v___y_5046_);
v_infoState_5049_ = lean_ctor_get(v___x_5048_, 8);
lean_inc_ref(v_infoState_5049_);
lean_dec(v___x_5048_);
v_enabled_5050_ = lean_ctor_get_uint8(v_infoState_5049_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5049_);
if (v_enabled_5050_ == 0)
{
lean_object* v___x_5051_; lean_object* v___x_5052_; 
lean_dec_ref(v_t_5045_);
v___x_5051_ = lean_box(0);
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
return v___x_5052_;
}
else
{
lean_object* v___x_5053_; lean_object* v_infoState_5054_; lean_object* v_env_5055_; lean_object* v_nextMacroScope_5056_; lean_object* v_ngen_5057_; lean_object* v_auxDeclNGen_5058_; lean_object* v_traceState_5059_; lean_object* v_cache_5060_; lean_object* v_recordedDeps_5061_; lean_object* v_messages_5062_; lean_object* v_snapshotTasks_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5085_; 
v___x_5053_ = lean_st_ref_take(v___y_5046_);
v_infoState_5054_ = lean_ctor_get(v___x_5053_, 8);
v_env_5055_ = lean_ctor_get(v___x_5053_, 0);
v_nextMacroScope_5056_ = lean_ctor_get(v___x_5053_, 1);
v_ngen_5057_ = lean_ctor_get(v___x_5053_, 2);
v_auxDeclNGen_5058_ = lean_ctor_get(v___x_5053_, 3);
v_traceState_5059_ = lean_ctor_get(v___x_5053_, 4);
v_cache_5060_ = lean_ctor_get(v___x_5053_, 5);
v_recordedDeps_5061_ = lean_ctor_get(v___x_5053_, 6);
v_messages_5062_ = lean_ctor_get(v___x_5053_, 7);
v_snapshotTasks_5063_ = lean_ctor_get(v___x_5053_, 9);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5065_ = v___x_5053_;
v_isShared_5066_ = v_isSharedCheck_5085_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_snapshotTasks_5063_);
lean_inc(v_infoState_5054_);
lean_inc(v_messages_5062_);
lean_inc(v_recordedDeps_5061_);
lean_inc(v_cache_5060_);
lean_inc(v_traceState_5059_);
lean_inc(v_auxDeclNGen_5058_);
lean_inc(v_ngen_5057_);
lean_inc(v_nextMacroScope_5056_);
lean_inc(v_env_5055_);
lean_dec(v___x_5053_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5085_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
uint8_t v_enabled_5067_; lean_object* v_assignment_5068_; lean_object* v_lazyAssignment_5069_; lean_object* v_trees_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5084_; 
v_enabled_5067_ = lean_ctor_get_uint8(v_infoState_5054_, sizeof(void*)*3);
v_assignment_5068_ = lean_ctor_get(v_infoState_5054_, 0);
v_lazyAssignment_5069_ = lean_ctor_get(v_infoState_5054_, 1);
v_trees_5070_ = lean_ctor_get(v_infoState_5054_, 2);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_infoState_5054_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5072_ = v_infoState_5054_;
v_isShared_5073_ = v_isSharedCheck_5084_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_trees_5070_);
lean_inc(v_lazyAssignment_5069_);
lean_inc(v_assignment_5068_);
lean_dec(v_infoState_5054_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5084_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5077_; 
v___x_5074_ = lean_box(0);
v___x_5075_ = l_Lean_PersistentArray_push___redArg(v_trees_5070_, v_t_5045_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 2, v___x_5075_);
v___x_5077_ = v___x_5072_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_assignment_5068_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_lazyAssignment_5069_);
lean_ctor_set(v_reuseFailAlloc_5083_, 2, v___x_5075_);
lean_ctor_set_uint8(v_reuseFailAlloc_5083_, sizeof(void*)*3, v_enabled_5067_);
v___x_5077_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5079_; 
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 8, v___x_5077_);
v___x_5079_ = v___x_5065_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_env_5055_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v_nextMacroScope_5056_);
lean_ctor_set(v_reuseFailAlloc_5082_, 2, v_ngen_5057_);
lean_ctor_set(v_reuseFailAlloc_5082_, 3, v_auxDeclNGen_5058_);
lean_ctor_set(v_reuseFailAlloc_5082_, 4, v_traceState_5059_);
lean_ctor_set(v_reuseFailAlloc_5082_, 5, v_cache_5060_);
lean_ctor_set(v_reuseFailAlloc_5082_, 6, v_recordedDeps_5061_);
lean_ctor_set(v_reuseFailAlloc_5082_, 7, v_messages_5062_);
lean_ctor_set(v_reuseFailAlloc_5082_, 8, v___x_5077_);
lean_ctor_set(v_reuseFailAlloc_5082_, 9, v_snapshotTasks_5063_);
v___x_5079_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5080_ = lean_st_ref_put(v___y_5046_, v___x_5079_);
v___x_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5074_);
return v___x_5081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5086_, v___y_5087_);
lean_dec(v___y_5087_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5090_, v___y_5096_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5108_, lean_object* v___y_5109_){
_start:
{
uint8_t v___x_5111_; 
v___x_5111_ = l_Lean_Expr_hasMVar(v_e_5108_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
v___x_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5112_, 0, v_e_5108_);
return v___x_5112_;
}
else
{
lean_object* v___x_5113_; lean_object* v_mctx_5114_; lean_object* v___x_5115_; lean_object* v_fst_5116_; lean_object* v_snd_5117_; lean_object* v___x_5118_; lean_object* v_cache_5119_; lean_object* v_zetaDeltaFVarIds_5120_; lean_object* v_postponed_5121_; lean_object* v_diag_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5131_; 
v___x_5113_ = lean_st_ref_get(v___y_5109_);
v_mctx_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc_ref(v_mctx_5114_);
lean_dec(v___x_5113_);
v___x_5115_ = l_Lean_instantiateMVarsCore(v_mctx_5114_, v_e_5108_);
v_fst_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_fst_5116_);
v_snd_5117_ = lean_ctor_get(v___x_5115_, 1);
lean_inc(v_snd_5117_);
lean_dec_ref(v___x_5115_);
v___x_5118_ = lean_st_ref_take(v___y_5109_);
v_cache_5119_ = lean_ctor_get(v___x_5118_, 1);
v_zetaDeltaFVarIds_5120_ = lean_ctor_get(v___x_5118_, 2);
v_postponed_5121_ = lean_ctor_get(v___x_5118_, 3);
v_diag_5122_ = lean_ctor_get(v___x_5118_, 4);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5131_ == 0)
{
lean_object* v_unused_5132_; 
v_unused_5132_ = lean_ctor_get(v___x_5118_, 0);
lean_dec(v_unused_5132_);
v___x_5124_ = v___x_5118_;
v_isShared_5125_ = v_isSharedCheck_5131_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_diag_5122_);
lean_inc(v_postponed_5121_);
lean_inc(v_zetaDeltaFVarIds_5120_);
lean_inc(v_cache_5119_);
lean_dec(v___x_5118_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5131_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v_snd_5117_);
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_snd_5117_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v_cache_5119_);
lean_ctor_set(v_reuseFailAlloc_5130_, 2, v_zetaDeltaFVarIds_5120_);
lean_ctor_set(v_reuseFailAlloc_5130_, 3, v_postponed_5121_);
lean_ctor_set(v_reuseFailAlloc_5130_, 4, v_diag_5122_);
v___x_5127_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5128_ = lean_st_ref_put(v___y_5109_, v___x_5127_);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v_fst_5116_);
return v___x_5129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5133_, v___y_5134_);
lean_dec(v___y_5134_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5137_, v___y_5139_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5151_, size_t v_i_5152_, size_t v_stop_5153_, lean_object* v_b_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
uint8_t v___x_5162_; 
v___x_5162_ = lean_usize_dec_eq(v_i_5152_, v_stop_5153_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5163_ = lean_array_uget_borrowed(v_as_5151_, v_i_5152_);
lean_inc(v___x_5163_);
v___x_5164_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5163_);
v___x_5165_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5164_, v___y_5160_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; size_t v___x_5167_; size_t v___x_5168_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
v___x_5167_ = ((size_t)1ULL);
v___x_5168_ = lean_usize_add(v_i_5152_, v___x_5167_);
v_i_5152_ = v___x_5168_;
v_b_5154_ = v_a_5166_;
goto _start;
}
else
{
return v___x_5165_;
}
}
else
{
lean_object* v___x_5170_; 
v___x_5170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5170_, 0, v_b_5154_);
return v___x_5170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5171_, lean_object* v_i_5172_, lean_object* v_stop_5173_, lean_object* v_b_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
size_t v_i_boxed_5182_; size_t v_stop_boxed_5183_; lean_object* v_res_5184_; 
v_i_boxed_5182_ = lean_unbox_usize(v_i_5172_);
lean_dec(v_i_5172_);
v_stop_boxed_5183_ = lean_unbox_usize(v_stop_5173_);
lean_dec(v_stop_5173_);
v_res_5184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5171_, v_i_boxed_5182_, v_stop_boxed_5183_, v_b_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec_ref(v_as_5171_);
return v_res_5184_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5185_ = lean_unsigned_to_nat(32u);
v___x_5186_ = lean_mk_empty_array_with_capacity(v___x_5185_);
v___x_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
return v___x_5187_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5188_ = ((size_t)5ULL);
v___x_5189_ = lean_unsigned_to_nat(0u);
v___x_5190_ = lean_unsigned_to_nat(32u);
v___x_5191_ = lean_mk_empty_array_with_capacity(v___x_5190_);
v___x_5192_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5193_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5193_, 0, v___x_5192_);
lean_ctor_set(v___x_5193_, 1, v___x_5191_);
lean_ctor_set(v___x_5193_, 2, v___x_5189_);
lean_ctor_set(v___x_5193_, 3, v___x_5189_);
lean_ctor_set_usize(v___x_5193_, 4, v___x_5188_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5194_){
_start:
{
lean_object* v___x_5196_; lean_object* v_infoState_5197_; lean_object* v_trees_5198_; lean_object* v___x_5199_; lean_object* v_infoState_5200_; lean_object* v_env_5201_; lean_object* v_nextMacroScope_5202_; lean_object* v_ngen_5203_; lean_object* v_auxDeclNGen_5204_; lean_object* v_traceState_5205_; lean_object* v_cache_5206_; lean_object* v_recordedDeps_5207_; lean_object* v_messages_5208_; lean_object* v_snapshotTasks_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5230_; 
v___x_5196_ = lean_st_ref_get(v___y_5194_);
v_infoState_5197_ = lean_ctor_get(v___x_5196_, 8);
lean_inc_ref(v_infoState_5197_);
lean_dec(v___x_5196_);
v_trees_5198_ = lean_ctor_get(v_infoState_5197_, 2);
lean_inc_ref(v_trees_5198_);
lean_dec_ref(v_infoState_5197_);
v___x_5199_ = lean_st_ref_take(v___y_5194_);
v_infoState_5200_ = lean_ctor_get(v___x_5199_, 8);
v_env_5201_ = lean_ctor_get(v___x_5199_, 0);
v_nextMacroScope_5202_ = lean_ctor_get(v___x_5199_, 1);
v_ngen_5203_ = lean_ctor_get(v___x_5199_, 2);
v_auxDeclNGen_5204_ = lean_ctor_get(v___x_5199_, 3);
v_traceState_5205_ = lean_ctor_get(v___x_5199_, 4);
v_cache_5206_ = lean_ctor_get(v___x_5199_, 5);
v_recordedDeps_5207_ = lean_ctor_get(v___x_5199_, 6);
v_messages_5208_ = lean_ctor_get(v___x_5199_, 7);
v_snapshotTasks_5209_ = lean_ctor_get(v___x_5199_, 9);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5211_ = v___x_5199_;
v_isShared_5212_ = v_isSharedCheck_5230_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_snapshotTasks_5209_);
lean_inc(v_infoState_5200_);
lean_inc(v_messages_5208_);
lean_inc(v_recordedDeps_5207_);
lean_inc(v_cache_5206_);
lean_inc(v_traceState_5205_);
lean_inc(v_auxDeclNGen_5204_);
lean_inc(v_ngen_5203_);
lean_inc(v_nextMacroScope_5202_);
lean_inc(v_env_5201_);
lean_dec(v___x_5199_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5230_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
uint8_t v_enabled_5213_; lean_object* v_assignment_5214_; lean_object* v_lazyAssignment_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5228_; 
v_enabled_5213_ = lean_ctor_get_uint8(v_infoState_5200_, sizeof(void*)*3);
v_assignment_5214_ = lean_ctor_get(v_infoState_5200_, 0);
v_lazyAssignment_5215_ = lean_ctor_get(v_infoState_5200_, 1);
v_isSharedCheck_5228_ = !lean_is_exclusive(v_infoState_5200_);
if (v_isSharedCheck_5228_ == 0)
{
lean_object* v_unused_5229_; 
v_unused_5229_ = lean_ctor_get(v_infoState_5200_, 2);
lean_dec(v_unused_5229_);
v___x_5217_ = v_infoState_5200_;
v_isShared_5218_ = v_isSharedCheck_5228_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_lazyAssignment_5215_);
lean_inc(v_assignment_5214_);
lean_dec(v_infoState_5200_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5228_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5219_; lean_object* v___x_5221_; 
v___x_5219_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 2, v___x_5219_);
v___x_5221_ = v___x_5217_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_assignment_5214_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v_lazyAssignment_5215_);
lean_ctor_set(v_reuseFailAlloc_5227_, 2, v___x_5219_);
lean_ctor_set_uint8(v_reuseFailAlloc_5227_, sizeof(void*)*3, v_enabled_5213_);
v___x_5221_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
lean_object* v___x_5223_; 
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 8, v___x_5221_);
v___x_5223_ = v___x_5211_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_env_5201_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_nextMacroScope_5202_);
lean_ctor_set(v_reuseFailAlloc_5226_, 2, v_ngen_5203_);
lean_ctor_set(v_reuseFailAlloc_5226_, 3, v_auxDeclNGen_5204_);
lean_ctor_set(v_reuseFailAlloc_5226_, 4, v_traceState_5205_);
lean_ctor_set(v_reuseFailAlloc_5226_, 5, v_cache_5206_);
lean_ctor_set(v_reuseFailAlloc_5226_, 6, v_recordedDeps_5207_);
lean_ctor_set(v_reuseFailAlloc_5226_, 7, v_messages_5208_);
lean_ctor_set(v_reuseFailAlloc_5226_, 8, v___x_5221_);
lean_ctor_set(v_reuseFailAlloc_5226_, 9, v_snapshotTasks_5209_);
v___x_5223_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5224_ = lean_st_ref_put(v___y_5194_, v___x_5223_);
v___x_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5225_, 0, v_trees_5198_);
return v___x_5225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5231_);
lean_dec(v___y_5231_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5234_, lean_object* v_mkInfoTree_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v_a_5243_, lean_object* v_a_x3f_5244_){
_start:
{
lean_object* v___x_5246_; lean_object* v_infoState_5247_; lean_object* v_trees_5248_; lean_object* v___x_5249_; 
v___x_5246_ = lean_st_ref_get(v___y_5234_);
v_infoState_5247_ = lean_ctor_get(v___x_5246_, 8);
lean_inc_ref(v_infoState_5247_);
lean_dec(v___x_5246_);
v_trees_5248_ = lean_ctor_get(v_infoState_5247_, 2);
lean_inc_ref(v_trees_5248_);
lean_dec_ref(v_infoState_5247_);
lean_inc(v___y_5234_);
lean_inc_ref(v___y_5242_);
lean_inc(v___y_5241_);
lean_inc_ref(v___y_5240_);
lean_inc(v___y_5239_);
lean_inc_ref(v___y_5238_);
lean_inc(v___y_5237_);
lean_inc_ref(v___y_5236_);
v___x_5249_ = lean_apply_10(v_mkInfoTree_5235_, v_trees_5248_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5234_, lean_box(0));
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5289_; 
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5252_ = v___x_5249_;
v_isShared_5253_ = v_isSharedCheck_5289_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5289_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5254_; lean_object* v_infoState_5255_; lean_object* v_env_5256_; lean_object* v_nextMacroScope_5257_; lean_object* v_ngen_5258_; lean_object* v_auxDeclNGen_5259_; lean_object* v_traceState_5260_; lean_object* v_cache_5261_; lean_object* v_recordedDeps_5262_; lean_object* v_messages_5263_; lean_object* v_snapshotTasks_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5288_; 
v___x_5254_ = lean_st_ref_take(v___y_5234_);
v_infoState_5255_ = lean_ctor_get(v___x_5254_, 8);
v_env_5256_ = lean_ctor_get(v___x_5254_, 0);
v_nextMacroScope_5257_ = lean_ctor_get(v___x_5254_, 1);
v_ngen_5258_ = lean_ctor_get(v___x_5254_, 2);
v_auxDeclNGen_5259_ = lean_ctor_get(v___x_5254_, 3);
v_traceState_5260_ = lean_ctor_get(v___x_5254_, 4);
v_cache_5261_ = lean_ctor_get(v___x_5254_, 5);
v_recordedDeps_5262_ = lean_ctor_get(v___x_5254_, 6);
v_messages_5263_ = lean_ctor_get(v___x_5254_, 7);
v_snapshotTasks_5264_ = lean_ctor_get(v___x_5254_, 9);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5266_ = v___x_5254_;
v_isShared_5267_ = v_isSharedCheck_5288_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_snapshotTasks_5264_);
lean_inc(v_infoState_5255_);
lean_inc(v_messages_5263_);
lean_inc(v_recordedDeps_5262_);
lean_inc(v_cache_5261_);
lean_inc(v_traceState_5260_);
lean_inc(v_auxDeclNGen_5259_);
lean_inc(v_ngen_5258_);
lean_inc(v_nextMacroScope_5257_);
lean_inc(v_env_5256_);
lean_dec(v___x_5254_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5288_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
uint8_t v_enabled_5268_; lean_object* v_assignment_5269_; lean_object* v_lazyAssignment_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5286_; 
v_enabled_5268_ = lean_ctor_get_uint8(v_infoState_5255_, sizeof(void*)*3);
v_assignment_5269_ = lean_ctor_get(v_infoState_5255_, 0);
v_lazyAssignment_5270_ = lean_ctor_get(v_infoState_5255_, 1);
v_isSharedCheck_5286_ = !lean_is_exclusive(v_infoState_5255_);
if (v_isSharedCheck_5286_ == 0)
{
lean_object* v_unused_5287_; 
v_unused_5287_ = lean_ctor_get(v_infoState_5255_, 2);
lean_dec(v_unused_5287_);
v___x_5272_ = v_infoState_5255_;
v_isShared_5273_ = v_isSharedCheck_5286_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_lazyAssignment_5270_);
lean_inc(v_assignment_5269_);
lean_dec(v_infoState_5255_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5286_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5277_; 
v___x_5274_ = lean_box(0);
v___x_5275_ = l_Lean_PersistentArray_push___redArg(v_a_5243_, v_a_5250_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 2, v___x_5275_);
v___x_5277_ = v___x_5272_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_assignment_5269_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v_lazyAssignment_5270_);
lean_ctor_set(v_reuseFailAlloc_5285_, 2, v___x_5275_);
lean_ctor_set_uint8(v_reuseFailAlloc_5285_, sizeof(void*)*3, v_enabled_5268_);
v___x_5277_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
lean_object* v___x_5279_; 
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 8, v___x_5277_);
v___x_5279_ = v___x_5266_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_env_5256_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v_nextMacroScope_5257_);
lean_ctor_set(v_reuseFailAlloc_5284_, 2, v_ngen_5258_);
lean_ctor_set(v_reuseFailAlloc_5284_, 3, v_auxDeclNGen_5259_);
lean_ctor_set(v_reuseFailAlloc_5284_, 4, v_traceState_5260_);
lean_ctor_set(v_reuseFailAlloc_5284_, 5, v_cache_5261_);
lean_ctor_set(v_reuseFailAlloc_5284_, 6, v_recordedDeps_5262_);
lean_ctor_set(v_reuseFailAlloc_5284_, 7, v_messages_5263_);
lean_ctor_set(v_reuseFailAlloc_5284_, 8, v___x_5277_);
lean_ctor_set(v_reuseFailAlloc_5284_, 9, v_snapshotTasks_5264_);
v___x_5279_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
lean_object* v___x_5280_; lean_object* v___x_5282_; 
v___x_5280_ = lean_st_ref_put(v___y_5234_, v___x_5279_);
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 0, v___x_5274_);
v___x_5282_ = v___x_5252_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5274_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
lean_dec_ref(v_a_5243_);
v_a_5290_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5249_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5249_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5298_, lean_object* v_mkInfoTree_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v_a_5307_, lean_object* v_a_x3f_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5298_, v_mkInfoTree_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v_a_5307_, v_a_x3f_5308_);
lean_dec(v_a_x3f_5308_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5298_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5311_, lean_object* v_mkInfoTree_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_){
_start:
{
lean_object* v___x_5322_; lean_object* v_infoState_5323_; uint8_t v_enabled_5324_; 
v___x_5322_ = lean_st_ref_get(v___y_5320_);
v_infoState_5323_ = lean_ctor_get(v___x_5322_, 8);
lean_inc_ref(v_infoState_5323_);
lean_dec(v___x_5322_);
v_enabled_5324_ = lean_ctor_get_uint8(v_infoState_5323_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5323_);
if (v_enabled_5324_ == 0)
{
lean_object* v___x_5325_; 
lean_dec_ref(v_mkInfoTree_5312_);
lean_inc(v___y_5320_);
lean_inc_ref(v___y_5319_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
lean_inc(v___y_5316_);
lean_inc_ref(v___y_5315_);
lean_inc(v___y_5314_);
lean_inc_ref(v___y_5313_);
v___x_5325_ = lean_apply_9(v_x_5311_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, lean_box(0));
return v___x_5325_;
}
else
{
lean_object* v___x_5326_; lean_object* v_a_5327_; lean_object* v_r_5328_; 
v___x_5326_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5320_);
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_a_5327_);
lean_dec_ref(v___x_5326_);
lean_inc(v___y_5320_);
lean_inc_ref(v___y_5319_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
lean_inc(v___y_5316_);
lean_inc_ref(v___y_5315_);
lean_inc(v___y_5314_);
lean_inc_ref(v___y_5313_);
v_r_5328_ = lean_apply_9(v_x_5311_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, lean_box(0));
if (lean_obj_tag(v_r_5328_) == 0)
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5353_; 
v_a_5329_ = lean_ctor_get(v_r_5328_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_r_5328_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5331_ = v_r_5328_;
v_isShared_5332_ = v_isSharedCheck_5353_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v_r_5328_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5353_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
lean_inc(v_a_5329_);
if (v_isShared_5332_ == 0)
{
lean_ctor_set_tag(v___x_5331_, 1);
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
lean_object* v___x_5335_; 
v___x_5335_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5320_, v_mkInfoTree_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v_a_5327_, v___x_5334_);
lean_dec_ref(v___x_5334_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5342_ == 0)
{
lean_object* v_unused_5343_; 
v_unused_5343_ = lean_ctor_get(v___x_5335_, 0);
lean_dec(v_unused_5343_);
v___x_5337_ = v___x_5335_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_dec(v___x_5335_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 0, v_a_5329_);
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5329_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec(v_a_5329_);
v_a_5344_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5335_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5335_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
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
else
{
lean_object* v_a_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v_a_5354_ = lean_ctor_get(v_r_5328_, 0);
lean_inc(v_a_5354_);
lean_dec_ref_known(v_r_5328_, 1);
v___x_5355_ = lean_box(0);
v___x_5356_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5320_, v_mkInfoTree_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v_a_5327_, v___x_5355_);
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
lean_ctor_set_tag(v___x_5358_, 1);
lean_ctor_set(v___x_5358_, 0, v_a_5354_);
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5354_);
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
lean_dec(v_a_5354_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5373_, lean_object* v_mkInfoTree_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5373_, v_mkInfoTree_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v___y_5379_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5385_, lean_object* v_trees_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v___x_5396_; 
lean_inc(v___y_5394_);
lean_inc_ref(v___y_5393_);
lean_inc(v___y_5392_);
lean_inc_ref(v___y_5391_);
lean_inc(v___y_5390_);
lean_inc_ref(v___y_5389_);
lean_inc(v___y_5388_);
lean_inc_ref(v___y_5387_);
v___x_5396_ = lean_apply_9(v_a_5385_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, lean_box(0));
if (lean_obj_tag(v___x_5396_) == 0)
{
lean_object* v_a_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5405_; 
v_a_5397_ = lean_ctor_get(v___x_5396_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5399_ = v___x_5396_;
v_isShared_5400_ = v_isSharedCheck_5405_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_a_5397_);
lean_dec(v___x_5396_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5405_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5401_, 0, v_a_5397_);
lean_ctor_set(v___x_5401_, 1, v_trees_5386_);
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 0, v___x_5401_);
v___x_5403_ = v___x_5399_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5401_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_dec_ref(v_trees_5386_);
v_a_5406_ = lean_ctor_get(v___x_5396_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5396_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5396_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5414_, lean_object* v_trees_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5414_, v_trees_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5426_, lean_object* v_tactic_5427_, lean_object* v_ref_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5426_, v___y_5430_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v___x_5439_; 
lean_dec_ref_known(v___x_5438_, 1);
v___x_5439_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
lean_dec_ref_known(v___x_5439_, 1);
v___x_5440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5440_, 0, v_tactic_5427_);
v___x_5441_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; lean_object* v___f_5443_; lean_object* v___x_5444_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v___x_5441_, 1);
v___f_5443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5443_, 0, v_a_5442_);
v___x_5444_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5440_, v___f_5443_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
return v___x_5444_;
}
else
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_dec_ref(v___x_5440_);
v_a_5445_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5441_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5441_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5445_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
}
else
{
lean_dec(v_ref_5428_);
lean_dec(v_tactic_5427_);
return v___x_5439_;
}
}
else
{
lean_dec(v_ref_5428_);
lean_dec(v_tactic_5427_);
return v___x_5438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5453_, lean_object* v_tactic_5454_, lean_object* v_ref_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5453_, v_tactic_5454_, v_ref_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
return v_res_5465_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5466_; lean_object* v___x_5467_; 
v___x_5466_ = lean_box(1);
v___x_5467_ = l_Lean_MessageData_ofFormat(v___x_5466_);
return v___x_5467_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5472_ = l_Lean_MessageData_ofFormat(v___x_5471_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5473_, lean_object* v_x_5474_){
_start:
{
if (lean_obj_tag(v_x_5474_) == 0)
{
return v_x_5473_;
}
else
{
lean_object* v_head_5475_; lean_object* v_tail_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5498_; 
v_head_5475_ = lean_ctor_get(v_x_5474_, 0);
v_tail_5476_ = lean_ctor_get(v_x_5474_, 1);
v_isSharedCheck_5498_ = !lean_is_exclusive(v_x_5474_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5478_ = v_x_5474_;
v_isShared_5479_ = v_isSharedCheck_5498_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_tail_5476_);
lean_inc(v_head_5475_);
lean_dec(v_x_5474_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5498_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v_before_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5496_; 
v_before_5480_ = lean_ctor_get(v_head_5475_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v_head_5475_);
if (v_isSharedCheck_5496_ == 0)
{
lean_object* v_unused_5497_; 
v_unused_5497_ = lean_ctor_get(v_head_5475_, 1);
lean_dec(v_unused_5497_);
v___x_5482_ = v_head_5475_;
v_isShared_5483_ = v_isSharedCheck_5496_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_before_5480_);
lean_dec(v_head_5475_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5496_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5483_ == 0)
{
lean_ctor_set_tag(v___x_5482_, 7);
lean_ctor_set(v___x_5482_, 1, v___x_5484_);
lean_ctor_set(v___x_5482_, 0, v_x_5473_);
v___x_5486_ = v___x_5482_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_x_5473_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v___x_5484_);
v___x_5486_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5487_; lean_object* v___x_5489_; 
v___x_5487_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5479_ == 0)
{
lean_ctor_set_tag(v___x_5478_, 7);
lean_ctor_set(v___x_5478_, 1, v___x_5487_);
lean_ctor_set(v___x_5478_, 0, v___x_5486_);
v___x_5489_ = v___x_5478_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v___x_5487_);
v___x_5489_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5490_ = l_Lean_MessageData_ofSyntax(v_before_5480_);
v___x_5491_ = l_Lean_indentD(v___x_5490_);
v___x_5492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5489_);
lean_ctor_set(v___x_5492_, 1, v___x_5491_);
v_x_5473_ = v___x_5492_;
v_x_5474_ = v_tail_5476_;
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
lean_object* v___x_5502_; lean_object* v___x_5503_; 
v___x_5502_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5503_ = l_Lean_MessageData_ofFormat(v___x_5502_);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5504_, lean_object* v_macroStack_5505_, lean_object* v___y_5506_){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; uint8_t v___x_5510_; 
v___x_5508_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5506_);
v___x_5509_ = l_Lean_Elab_pp_macroStack;
v___x_5510_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_5508_, v___x_5509_);
lean_dec_ref(v___x_5508_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; 
lean_dec(v_macroStack_5505_);
v___x_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5511_, 0, v_msgData_5504_);
return v___x_5511_;
}
else
{
if (lean_obj_tag(v_macroStack_5505_) == 0)
{
lean_object* v___x_5512_; 
v___x_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5512_, 0, v_msgData_5504_);
return v___x_5512_;
}
else
{
lean_object* v_head_5513_; lean_object* v_after_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5529_; 
v_head_5513_ = lean_ctor_get(v_macroStack_5505_, 0);
lean_inc(v_head_5513_);
v_after_5514_ = lean_ctor_get(v_head_5513_, 1);
v_isSharedCheck_5529_ = !lean_is_exclusive(v_head_5513_);
if (v_isSharedCheck_5529_ == 0)
{
lean_object* v_unused_5530_; 
v_unused_5530_ = lean_ctor_get(v_head_5513_, 0);
lean_dec(v_unused_5530_);
v___x_5516_ = v_head_5513_;
v_isShared_5517_ = v_isSharedCheck_5529_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_after_5514_);
lean_dec(v_head_5513_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5529_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5518_; lean_object* v___x_5520_; 
v___x_5518_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5517_ == 0)
{
lean_ctor_set_tag(v___x_5516_, 7);
lean_ctor_set(v___x_5516_, 1, v___x_5518_);
lean_ctor_set(v___x_5516_, 0, v_msgData_5504_);
v___x_5520_ = v___x_5516_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_msgData_5504_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v_msgData_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5521_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5520_);
lean_ctor_set(v___x_5522_, 1, v___x_5521_);
v___x_5523_ = l_Lean_MessageData_ofSyntax(v_after_5514_);
v___x_5524_ = l_Lean_indentD(v___x_5523_);
v_msgData_5525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5525_, 0, v___x_5522_);
lean_ctor_set(v_msgData_5525_, 1, v___x_5524_);
v___x_5526_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5525_, v_macroStack_5505_);
v___x_5527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5526_);
return v___x_5527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5531_, lean_object* v_macroStack_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5531_, v_macroStack_5532_, v___y_5533_);
lean_dec_ref(v___y_5533_);
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_){
_start:
{
lean_object* v_ref_5544_; lean_object* v_macroStack_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v_a_5548_; lean_object* v___x_5549_; lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5558_; 
v_ref_5544_ = lean_ctor_get(v___y_5541_, 2);
v_macroStack_5545_ = lean_ctor_get(v___y_5537_, 1);
v___x_5546_ = l_Lean_Elab_getBetterRef(v_ref_5544_, v_macroStack_5545_);
v___x_5547_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5536_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_);
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_a_5548_);
lean_dec_ref(v___x_5547_);
lean_inc(v_macroStack_5545_);
v___x_5549_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5548_, v_macroStack_5545_, v___y_5541_);
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5552_ = v___x_5549_;
v_isShared_5553_ = v_isSharedCheck_5558_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5549_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5558_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5554_; lean_object* v___x_5556_; 
v___x_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5546_);
lean_ctor_set(v___x_5554_, 1, v_a_5550_);
if (v_isShared_5553_ == 0)
{
lean_ctor_set_tag(v___x_5552_, 1);
lean_ctor_set(v___x_5552_, 0, v___x_5554_);
v___x_5556_ = v___x_5552_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
return v_res_5567_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5570_ = l_Lean_stringToMessageData(v___x_5569_);
return v___x_5570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5571_, size_t v_sz_5572_, size_t v_i_5573_, lean_object* v_b_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
lean_object* v_a_5583_; uint8_t v___x_5587_; 
v___x_5587_ = lean_usize_dec_lt(v_i_5573_, v_sz_5572_);
if (v___x_5587_ == 0)
{
lean_object* v___x_5588_; 
v___x_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5588_, 0, v_b_5574_);
return v___x_5588_;
}
else
{
lean_object* v___x_5589_; lean_object* v_a_5590_; lean_object* v___x_5591_; 
v___x_5589_ = lean_box(0);
v_a_5590_ = lean_array_uget_borrowed(v_as_5571_, v_i_5573_);
lean_inc(v_a_5590_);
v___x_5591_ = l_Lean_MVarId_getType(v_a_5590_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; lean_object* v___x_5593_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_a_5592_);
lean_dec_ref_known(v___x_5591_, 1);
lean_inc(v_a_5590_);
v___x_5593_ = l_Lean_MVarId_getType(v_a_5590_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
if (lean_obj_tag(v___x_5593_) == 0)
{
lean_object* v_a_5594_; lean_object* v___x_5595_; 
v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
lean_inc(v_a_5594_);
lean_dec_ref_known(v___x_5593_, 1);
v___x_5595_ = l_Lean_getRecAppSyntax_x3f(v_a_5594_);
lean_dec(v_a_5594_);
if (lean_obj_tag(v___x_5595_) == 1)
{
lean_object* v_val_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v_val_5596_ = lean_ctor_get(v___x_5595_, 0);
lean_inc(v_val_5596_);
lean_dec_ref_known(v___x_5595_, 1);
v___x_5597_ = l_Lean_Expr_mdataExpr_x21(v_a_5592_);
lean_dec(v_a_5592_);
lean_inc(v_a_5590_);
v___x_5598_ = l_Lean_MVarId_setType___redArg(v_a_5590_, v___x_5597_, v___y_5578_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_object* v_toCold_5599_; lean_object* v_currRecDepth_5600_; lean_object* v_ref_5601_; uint16_t v_optionFlags_5602_; uint8_t v_suppressElabErrors_5603_; uint8_t v_isRecordingDeps_5604_; lean_object* v_ref_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
lean_dec_ref_known(v___x_5598_, 1);
v_toCold_5599_ = lean_ctor_get(v___y_5579_, 0);
v_currRecDepth_5600_ = lean_ctor_get(v___y_5579_, 1);
v_ref_5601_ = lean_ctor_get(v___y_5579_, 2);
v_optionFlags_5602_ = lean_ctor_get_uint16(v___y_5579_, sizeof(void*)*3);
v_suppressElabErrors_5603_ = lean_ctor_get_uint8(v___y_5579_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5604_ = lean_ctor_get_uint8(v___y_5579_, sizeof(void*)*3 + 3);
v_ref_5605_ = l_Lean_replaceRef(v_val_5596_, v_ref_5601_);
lean_dec(v_val_5596_);
lean_inc(v_currRecDepth_5600_);
lean_inc_ref(v_toCold_5599_);
v___x_5606_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5606_, 0, v_toCold_5599_);
lean_ctor_set(v___x_5606_, 1, v_currRecDepth_5600_);
lean_ctor_set(v___x_5606_, 2, v_ref_5605_);
lean_ctor_set_uint16(v___x_5606_, sizeof(void*)*3, v_optionFlags_5602_);
lean_ctor_set_uint8(v___x_5606_, sizeof(void*)*3 + 2, v_suppressElabErrors_5603_);
lean_ctor_set_uint8(v___x_5606_, sizeof(void*)*3 + 3, v_isRecordingDeps_5604_);
lean_inc(v_a_5590_);
v___x_5607_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5590_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___x_5606_, v___y_5580_);
lean_dec_ref_known(v___x_5606_, 3);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_dec_ref_known(v___x_5607_, 1);
v_a_5583_ = v___x_5589_;
goto v___jp_5582_;
}
else
{
return v___x_5607_;
}
}
else
{
lean_dec(v_val_5596_);
return v___x_5598_;
}
}
else
{
lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
lean_dec(v___x_5595_);
v___x_5608_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5609_ = l_Lean_indentExpr(v_a_5592_);
v___x_5610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5608_);
lean_ctor_set(v___x_5610_, 1, v___x_5609_);
v___x_5611_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5610_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_dec_ref_known(v___x_5611_, 1);
v_a_5583_ = v___x_5589_;
goto v___jp_5582_;
}
else
{
return v___x_5611_;
}
}
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec(v_a_5592_);
v_a_5612_ = lean_ctor_get(v___x_5593_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5593_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5593_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5593_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
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
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
v_a_5620_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5591_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5591_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
if (v_isShared_5623_ == 0)
{
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
}
v___jp_5582_:
{
size_t v___x_5584_; size_t v___x_5585_; 
v___x_5584_ = ((size_t)1ULL);
v___x_5585_ = lean_usize_add(v_i_5573_, v___x_5584_);
v_i_5573_ = v___x_5585_;
v_b_5574_ = v_a_5583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5628_, lean_object* v_sz_5629_, lean_object* v_i_5630_, lean_object* v_b_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
size_t v_sz_boxed_5639_; size_t v_i_boxed_5640_; lean_object* v_res_5641_; 
v_sz_boxed_5639_ = lean_unbox_usize(v_sz_5629_);
lean_dec(v_sz_5629_);
v_i_boxed_5640_ = lean_unbox_usize(v_i_5630_);
lean_dec(v_i_5630_);
v_res_5641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5628_, v_sz_boxed_5639_, v_i_boxed_5640_, v_b_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec_ref(v_as_5628_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5642_, size_t v_i_5643_, size_t v_stop_5644_, lean_object* v_b_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_){
_start:
{
uint8_t v___x_5651_; 
v___x_5651_ = lean_usize_dec_eq(v_i_5643_, v_stop_5644_);
if (v___x_5651_ == 0)
{
lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5652_ = lean_array_uget_borrowed(v_as_5642_, v_i_5643_);
lean_inc(v___x_5652_);
v___x_5653_ = l_Lean_MVarId_getType(v___x_5652_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_a_5654_);
lean_dec_ref_known(v___x_5653_, 1);
v___x_5655_ = l_Lean_Expr_mdataExpr_x21(v_a_5654_);
lean_dec(v_a_5654_);
lean_inc(v___x_5652_);
v___x_5656_ = l_Lean_MVarId_setType___redArg(v___x_5652_, v___x_5655_, v___y_5647_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; size_t v___x_5658_; size_t v___x_5659_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = ((size_t)1ULL);
v___x_5659_ = lean_usize_add(v_i_5643_, v___x_5658_);
v_i_5643_ = v___x_5659_;
v_b_5645_ = v_a_5657_;
goto _start;
}
else
{
return v___x_5656_;
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
v_a_5661_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5653_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5653_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v___x_5669_; 
v___x_5669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5669_, 0, v_b_5645_);
return v___x_5669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5670_, lean_object* v_i_5671_, lean_object* v_stop_5672_, lean_object* v_b_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_){
_start:
{
size_t v_i_boxed_5679_; size_t v_stop_boxed_5680_; lean_object* v_res_5681_; 
v_i_boxed_5679_ = lean_unbox_usize(v_i_5671_);
lean_dec(v_i_5671_);
v_stop_boxed_5680_ = lean_unbox_usize(v_stop_5672_);
lean_dec(v_stop_5672_);
v_res_5681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5670_, v_i_boxed_5679_, v_stop_boxed_5680_, v_b_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec_ref(v_as_5670_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5682_, lean_object* v___x_5683_, lean_object* v___x_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v___x_5692_; size_t v_sz_5693_; size_t v___x_5694_; lean_object* v___x_5695_; 
v___x_5692_ = lean_box(0);
v_sz_5693_ = lean_array_size(v___x_5683_);
v___x_5694_ = ((size_t)0ULL);
v___x_5695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5683_, v_sz_5693_, v___x_5694_, v___x_5692_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
lean_dec_ref(v___x_5683_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5702_ == 0)
{
lean_object* v_unused_5703_; 
v_unused_5703_ = lean_ctor_get(v___x_5695_, 0);
lean_dec(v_unused_5703_);
v___x_5697_ = v___x_5695_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_dec(v___x_5695_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
lean_ctor_set(v___x_5697_, 0, v___x_5692_);
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5692_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
else
{
return v___x_5695_;
}
}
else
{
lean_object* v_val_5704_; lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5760_; 
v_val_5704_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5706_ = v___x_5682_;
v_isShared_5707_ = v_isSharedCheck_5760_;
goto v_resetjp_5705_;
}
else
{
lean_inc(v_val_5704_);
lean_dec(v___x_5682_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5760_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v_ref_5708_; lean_object* v_tactic_5709_; lean_object* v_toCold_5710_; lean_object* v_currRecDepth_5711_; lean_object* v_ref_5712_; uint16_t v_optionFlags_5713_; uint8_t v_suppressElabErrors_5714_; uint8_t v_isRecordingDeps_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v_ref_5718_; lean_object* v___x_5719_; uint8_t v___x_5755_; 
v_ref_5708_ = lean_ctor_get(v_val_5704_, 0);
lean_inc(v_ref_5708_);
v_tactic_5709_ = lean_ctor_get(v_val_5704_, 1);
lean_inc(v_tactic_5709_);
lean_dec(v_val_5704_);
v_toCold_5710_ = lean_ctor_get(v___y_5689_, 0);
v_currRecDepth_5711_ = lean_ctor_get(v___y_5689_, 1);
v_ref_5712_ = lean_ctor_get(v___y_5689_, 2);
v_optionFlags_5713_ = lean_ctor_get_uint16(v___y_5689_, sizeof(void*)*3);
v_suppressElabErrors_5714_ = lean_ctor_get_uint8(v___y_5689_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5715_ = lean_ctor_get_uint8(v___y_5689_, sizeof(void*)*3 + 3);
v___x_5716_ = lean_unsigned_to_nat(0u);
v___x_5717_ = lean_array_get_size(v___x_5683_);
v_ref_5718_ = l_Lean_replaceRef(v_ref_5708_, v_ref_5712_);
lean_inc(v_currRecDepth_5711_);
lean_inc_ref(v_toCold_5710_);
v___x_5719_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5719_, 0, v_toCold_5710_);
lean_ctor_set(v___x_5719_, 1, v_currRecDepth_5711_);
lean_ctor_set(v___x_5719_, 2, v_ref_5718_);
lean_ctor_set_uint16(v___x_5719_, sizeof(void*)*3, v_optionFlags_5713_);
lean_ctor_set_uint8(v___x_5719_, sizeof(void*)*3 + 2, v_suppressElabErrors_5714_);
lean_ctor_set_uint8(v___x_5719_, sizeof(void*)*3 + 3, v_isRecordingDeps_5715_);
v___x_5755_ = lean_nat_dec_lt(v___x_5716_, v___x_5717_);
if (v___x_5755_ == 0)
{
goto v___jp_5744_;
}
else
{
lean_object* v___x_5756_; size_t v___x_5757_; size_t v___x_5758_; lean_object* v___x_5759_; 
v___x_5756_ = lean_box(0);
v___x_5757_ = ((size_t)0ULL);
v___x_5758_ = lean_usize_of_nat(v___x_5717_);
v___x_5759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5683_, v___x_5757_, v___x_5758_, v___x_5756_, v___y_5687_, v___y_5688_, v___x_5719_, v___y_5690_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_dec_ref_known(v___x_5759_, 1);
goto v___jp_5744_;
}
else
{
lean_dec_ref_known(v___x_5719_, 3);
lean_dec(v_tactic_5709_);
lean_dec(v_ref_5708_);
lean_del_object(v___x_5706_);
lean_dec_ref(v___x_5683_);
return v___x_5759_;
}
}
v___jp_5720_:
{
lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___f_5723_; lean_object* v___x_5724_; 
v___x_5721_ = lean_array_get(v___x_5684_, v___x_5683_, v___x_5716_);
v___x_5722_ = lean_array_to_list(v___x_5683_);
v___f_5723_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5723_, 0, v___x_5722_);
lean_closure_set(v___f_5723_, 1, v_tactic_5709_);
lean_closure_set(v___f_5723_, 2, v_ref_5708_);
v___x_5724_ = l_Lean_Elab_Tactic_run(v___x_5721_, v___f_5723_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___x_5719_, v___y_5690_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5735_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5735_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5735_ == 0)
{
v___x_5727_ = v___x_5724_;
v_isShared_5728_ = v_isSharedCheck_5735_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_a_5725_);
lean_dec(v___x_5724_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5735_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
uint8_t v___x_5729_; 
v___x_5729_ = l_List_isEmpty___redArg(v_a_5725_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; 
lean_del_object(v___x_5727_);
v___x_5730_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5725_, v___y_5687_, v___y_5688_, v___x_5719_, v___y_5690_);
lean_dec_ref_known(v___x_5719_, 3);
return v___x_5730_;
}
else
{
lean_object* v___x_5731_; lean_object* v___x_5733_; 
lean_dec(v_a_5725_);
lean_dec_ref_known(v___x_5719_, 3);
v___x_5731_ = lean_box(0);
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 0, v___x_5731_);
v___x_5733_ = v___x_5727_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v___x_5731_);
v___x_5733_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
return v___x_5733_;
}
}
}
}
else
{
lean_object* v_a_5736_; lean_object* v___x_5738_; uint8_t v_isShared_5739_; uint8_t v_isSharedCheck_5743_; 
lean_dec_ref_known(v___x_5719_, 3);
v_a_5736_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5743_ == 0)
{
v___x_5738_ = v___x_5724_;
v_isShared_5739_ = v_isSharedCheck_5743_;
goto v_resetjp_5737_;
}
else
{
lean_inc(v_a_5736_);
lean_dec(v___x_5724_);
v___x_5738_ = lean_box(0);
v_isShared_5739_ = v_isSharedCheck_5743_;
goto v_resetjp_5737_;
}
v_resetjp_5737_:
{
lean_object* v___x_5741_; 
if (v_isShared_5739_ == 0)
{
v___x_5741_ = v___x_5738_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_a_5736_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
}
v___jp_5744_:
{
uint8_t v___x_5745_; 
v___x_5745_ = lean_nat_dec_eq(v___x_5717_, v___x_5716_);
if (v___x_5745_ == 0)
{
uint8_t v___x_5746_; 
lean_del_object(v___x_5706_);
v___x_5746_ = lean_nat_dec_lt(v___x_5716_, v___x_5717_);
if (v___x_5746_ == 0)
{
goto v___jp_5720_;
}
else
{
lean_object* v___x_5747_; size_t v___x_5748_; size_t v___x_5749_; lean_object* v___x_5750_; 
v___x_5747_ = lean_box(0);
v___x_5748_ = ((size_t)0ULL);
v___x_5749_ = lean_usize_of_nat(v___x_5717_);
v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5683_, v___x_5748_, v___x_5749_, v___x_5747_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___x_5719_, v___y_5690_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_dec_ref_known(v___x_5750_, 1);
goto v___jp_5720_;
}
else
{
lean_dec_ref_known(v___x_5719_, 3);
lean_dec(v_tactic_5709_);
lean_dec(v_ref_5708_);
lean_dec_ref(v___x_5683_);
return v___x_5750_;
}
}
}
else
{
lean_object* v___x_5751_; lean_object* v___x_5753_; 
lean_dec_ref_known(v___x_5719_, 3);
lean_dec(v_tactic_5709_);
lean_dec(v_ref_5708_);
lean_dec_ref(v___x_5683_);
v___x_5751_ = lean_box(0);
if (v_isShared_5707_ == 0)
{
lean_ctor_set_tag(v___x_5706_, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5751_);
v___x_5753_ = v___x_5706_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5761_, lean_object* v___x_5762_, lean_object* v___x_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5761_, v___x_5762_, v___x_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___x_5763_);
return v_res_5771_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5772_){
_start:
{
uint8_t v___x_5773_; 
v___x_5773_ = 0;
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5774_){
_start:
{
uint8_t v_res_5775_; lean_object* v_r_5776_; 
v_res_5775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5774_);
lean_dec(v_x_5774_);
v_r_5776_ = lean_box(v_res_5775_);
return v_r_5776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5783_, size_t v_sz_5784_, size_t v_i_5785_, lean_object* v_b_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
uint8_t v___x_5792_; 
v___x_5792_ = lean_usize_dec_lt(v_i_5785_, v_sz_5784_);
if (v___x_5792_ == 0)
{
lean_object* v___x_5793_; 
v___x_5793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5793_, 0, v_b_5786_);
return v___x_5793_;
}
else
{
lean_object* v_snd_5794_; lean_object* v_fst_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5867_; 
v_snd_5794_ = lean_ctor_get(v_b_5786_, 1);
v_fst_5795_ = lean_ctor_get(v_b_5786_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v_b_5786_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5797_ = v_b_5786_;
v_isShared_5798_ = v_isSharedCheck_5867_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_snd_5794_);
lean_inc(v_fst_5795_);
lean_dec(v_b_5786_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5867_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v_array_5799_; lean_object* v_start_5800_; lean_object* v_stop_5801_; uint8_t v___x_5802_; 
v_array_5799_ = lean_ctor_get(v_snd_5794_, 0);
v_start_5800_ = lean_ctor_get(v_snd_5794_, 1);
v_stop_5801_ = lean_ctor_get(v_snd_5794_, 2);
v___x_5802_ = lean_nat_dec_lt(v_start_5800_, v_stop_5801_);
if (v___x_5802_ == 0)
{
lean_object* v___x_5804_; 
if (v_isShared_5798_ == 0)
{
v___x_5804_ = v___x_5797_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_fst_5795_);
lean_ctor_set(v_reuseFailAlloc_5806_, 1, v_snd_5794_);
v___x_5804_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
lean_object* v___x_5805_; 
v___x_5805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5805_, 0, v___x_5804_);
return v___x_5805_;
}
}
else
{
lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5863_; 
lean_inc(v_stop_5801_);
lean_inc(v_start_5800_);
lean_inc_ref(v_array_5799_);
v_isSharedCheck_5863_ = !lean_is_exclusive(v_snd_5794_);
if (v_isSharedCheck_5863_ == 0)
{
lean_object* v_unused_5864_; lean_object* v_unused_5865_; lean_object* v_unused_5866_; 
v_unused_5864_ = lean_ctor_get(v_snd_5794_, 2);
lean_dec(v_unused_5864_);
v_unused_5865_ = lean_ctor_get(v_snd_5794_, 1);
lean_dec(v_unused_5865_);
v_unused_5866_ = lean_ctor_get(v_snd_5794_, 0);
lean_dec(v_unused_5866_);
v___x_5808_ = v_snd_5794_;
v_isShared_5809_ = v_isSharedCheck_5863_;
goto v_resetjp_5807_;
}
else
{
lean_dec(v_snd_5794_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5863_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v_array_5810_; lean_object* v_start_5811_; lean_object* v_stop_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5817_; 
v_array_5810_ = lean_ctor_get(v_fst_5795_, 0);
v_start_5811_ = lean_ctor_get(v_fst_5795_, 1);
v_stop_5812_ = lean_ctor_get(v_fst_5795_, 2);
v___x_5813_ = lean_array_fget(v_array_5799_, v_start_5800_);
v___x_5814_ = lean_unsigned_to_nat(1u);
v___x_5815_ = lean_nat_add(v_start_5800_, v___x_5814_);
lean_dec(v_start_5800_);
if (v_isShared_5809_ == 0)
{
lean_ctor_set(v___x_5808_, 1, v___x_5815_);
v___x_5817_ = v___x_5808_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_array_5799_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v___x_5815_);
lean_ctor_set(v_reuseFailAlloc_5862_, 2, v_stop_5801_);
v___x_5817_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
uint8_t v___x_5818_; 
v___x_5818_ = lean_nat_dec_lt(v_start_5811_, v_stop_5812_);
if (v___x_5818_ == 0)
{
lean_object* v___x_5820_; 
lean_dec(v___x_5813_);
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 1, v___x_5817_);
v___x_5820_ = v___x_5797_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_fst_5795_);
lean_ctor_set(v_reuseFailAlloc_5822_, 1, v___x_5817_);
v___x_5820_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5821_; 
v___x_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5820_);
return v___x_5821_;
}
}
else
{
lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5858_; 
lean_inc(v_stop_5812_);
lean_inc(v_start_5811_);
lean_inc_ref(v_array_5810_);
v_isSharedCheck_5858_ = !lean_is_exclusive(v_fst_5795_);
if (v_isSharedCheck_5858_ == 0)
{
lean_object* v_unused_5859_; lean_object* v_unused_5860_; lean_object* v_unused_5861_; 
v_unused_5859_ = lean_ctor_get(v_fst_5795_, 2);
lean_dec(v_unused_5859_);
v_unused_5860_ = lean_ctor_get(v_fst_5795_, 1);
lean_dec(v_unused_5860_);
v_unused_5861_ = lean_ctor_get(v_fst_5795_, 0);
lean_dec(v_unused_5861_);
v___x_5824_ = v_fst_5795_;
v_isShared_5825_ = v_isSharedCheck_5858_;
goto v_resetjp_5823_;
}
else
{
lean_dec(v_fst_5795_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5858_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___f_5826_; lean_object* v___x_5827_; lean_object* v_a_5828_; lean_object* v___x_5829_; lean_object* v___y_5830_; lean_object* v___x_5831_; lean_object* v___x_5833_; 
v___f_5826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5827_ = lean_box(0);
v_a_5828_ = lean_array_uget_borrowed(v_as_5783_, v_i_5785_);
v___x_5829_ = lean_array_fget_borrowed(v_array_5810_, v_start_5811_);
lean_inc(v___x_5829_);
v___y_5830_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5830_, 0, v___x_5813_);
lean_closure_set(v___y_5830_, 1, v___x_5829_);
lean_closure_set(v___y_5830_, 2, v___x_5827_);
v___x_5831_ = lean_nat_add(v_start_5811_, v___x_5814_);
lean_dec(v_start_5811_);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 1, v___x_5831_);
v___x_5833_ = v___x_5824_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_array_5810_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v___x_5831_);
lean_ctor_set(v_reuseFailAlloc_5857_, 2, v_stop_5812_);
v___x_5833_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; uint8_t v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; 
lean_inc(v_a_5828_);
v___x_5834_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5834_, 0, lean_box(0));
lean_closure_set(v___x_5834_, 1, v_a_5828_);
lean_closure_set(v___x_5834_, 2, v___y_5830_);
v___x_5835_ = lean_box(0);
v___x_5836_ = lean_box(0);
v___x_5837_ = lean_box(1);
v___x_5838_ = 0;
v___x_5839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5840_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5840_, 0, v___x_5835_);
lean_ctor_set(v___x_5840_, 1, v___x_5836_);
lean_ctor_set(v___x_5840_, 2, v___x_5835_);
lean_ctor_set(v___x_5840_, 3, v___f_5826_);
lean_ctor_set(v___x_5840_, 4, v___x_5837_);
lean_ctor_set(v___x_5840_, 5, v___x_5837_);
lean_ctor_set(v___x_5840_, 6, v___x_5835_);
lean_ctor_set(v___x_5840_, 7, v___x_5839_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8, v___x_5818_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 1, v___x_5818_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 2, v___x_5818_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 3, v___x_5818_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 4, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 5, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 6, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 7, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 8, v___x_5818_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 9, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*8 + 10, v___x_5818_);
v___x_5841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5842_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5834_, v___x_5840_, v___x_5841_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v___x_5844_; 
lean_dec_ref_known(v___x_5842_, 1);
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 1, v___x_5817_);
lean_ctor_set(v___x_5797_, 0, v___x_5833_);
v___x_5844_ = v___x_5797_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5833_);
lean_ctor_set(v_reuseFailAlloc_5848_, 1, v___x_5817_);
v___x_5844_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
size_t v___x_5845_; size_t v___x_5846_; 
v___x_5845_ = ((size_t)1ULL);
v___x_5846_ = lean_usize_add(v_i_5785_, v___x_5845_);
v_i_5785_ = v___x_5846_;
v_b_5786_ = v___x_5844_;
goto _start;
}
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_dec_ref(v___x_5833_);
lean_dec_ref(v___x_5817_);
lean_del_object(v___x_5797_);
v_a_5849_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5842_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5842_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5868_, lean_object* v_sz_5869_, lean_object* v_i_5870_, lean_object* v_b_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
size_t v_sz_boxed_5877_; size_t v_i_boxed_5878_; lean_object* v_res_5879_; 
v_sz_boxed_5877_ = lean_unbox_usize(v_sz_5869_);
lean_dec(v_sz_5869_);
v_i_boxed_5878_ = lean_unbox_usize(v_i_5870_);
lean_dec(v_i_5870_);
v_res_5879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5868_, v_sz_boxed_5877_, v_i_boxed_5878_, v_b_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec_ref(v_as_5868_);
return v_res_5879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5880_, lean_object* v_decrTactics_5881_, lean_object* v_argsPacker_5882_, lean_object* v_funNames_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_){
_start:
{
lean_object* v___x_5889_; 
lean_inc_ref(v_value_5880_);
v___x_5889_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5880_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
if (lean_obj_tag(v___x_5889_) == 0)
{
lean_object* v_a_5890_; lean_object* v___x_5891_; 
v_a_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5890_);
lean_dec_ref_known(v___x_5889_, 1);
v___x_5891_ = l_Lean_Elab_WF_assignSubsumed(v_a_5890_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
lean_dec(v_a_5890_);
if (lean_obj_tag(v___x_5891_) == 0)
{
lean_object* v_a_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
v_a_5892_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_a_5892_);
lean_dec_ref_known(v___x_5891_, 1);
v___x_5893_ = lean_array_get_size(v_decrTactics_5881_);
v___x_5894_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5882_, v___x_5893_, v_a_5892_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
lean_dec(v_a_5892_);
if (lean_obj_tag(v___x_5894_) == 0)
{
lean_object* v_a_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; size_t v_sz_5901_; size_t v___x_5902_; lean_object* v___x_5903_; 
v_a_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_a_5895_);
lean_dec_ref_known(v___x_5894_, 1);
v___x_5896_ = lean_unsigned_to_nat(0u);
v___x_5897_ = lean_array_get_size(v_a_5895_);
v___x_5898_ = l_Array_toSubarray___redArg(v_a_5895_, v___x_5896_, v___x_5897_);
v___x_5899_ = l_Array_toSubarray___redArg(v_decrTactics_5881_, v___x_5896_, v___x_5893_);
v___x_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v_sz_5901_ = lean_array_size(v_funNames_5883_);
v___x_5902_ = ((size_t)0ULL);
v___x_5903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5883_, v_sz_5901_, v___x_5902_, v___x_5900_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v___x_5904_; 
lean_dec_ref_known(v___x_5903_, 1);
v___x_5904_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5880_, v___y_5885_);
return v___x_5904_;
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec_ref(v_value_5880_);
v_a_5905_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5903_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5903_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
lean_dec_ref(v_decrTactics_5881_);
lean_dec_ref(v_value_5880_);
v_a_5913_ = lean_ctor_get(v___x_5894_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5894_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5894_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5894_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
}
else
{
lean_object* v_a_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5928_; 
lean_dec_ref(v_decrTactics_5881_);
lean_dec_ref(v_value_5880_);
v_a_5921_ = lean_ctor_get(v___x_5891_, 0);
v_isSharedCheck_5928_ = !lean_is_exclusive(v___x_5891_);
if (v_isSharedCheck_5928_ == 0)
{
v___x_5923_ = v___x_5891_;
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_a_5921_);
lean_dec(v___x_5891_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5926_; 
if (v_isShared_5924_ == 0)
{
v___x_5926_ = v___x_5923_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_a_5921_);
v___x_5926_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
return v___x_5926_;
}
}
}
}
else
{
lean_object* v_a_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5936_; 
lean_dec_ref(v_decrTactics_5881_);
lean_dec_ref(v_value_5880_);
v_a_5929_ = lean_ctor_get(v___x_5889_, 0);
v_isSharedCheck_5936_ = !lean_is_exclusive(v___x_5889_);
if (v_isSharedCheck_5936_ == 0)
{
v___x_5931_ = v___x_5889_;
v_isShared_5932_ = v_isSharedCheck_5936_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_a_5929_);
lean_dec(v___x_5889_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5936_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v___x_5934_; 
if (v_isShared_5932_ == 0)
{
v___x_5934_ = v___x_5931_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_a_5929_);
v___x_5934_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
return v___x_5934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5937_, lean_object* v_decrTactics_5938_, lean_object* v_argsPacker_5939_, lean_object* v_funNames_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_){
_start:
{
lean_object* v_res_5946_; 
v_res_5946_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5937_, v_decrTactics_5938_, v_argsPacker_5939_, v_funNames_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
lean_dec(v___y_5944_);
lean_dec_ref(v___y_5943_);
lean_dec(v___y_5942_);
lean_dec_ref(v___y_5941_);
lean_dec_ref(v_funNames_5940_);
lean_dec_ref(v_argsPacker_5939_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5947_, uint8_t v_isExporting_5948_, lean_object* v___x_5949_, lean_object* v___y_5950_, lean_object* v___x_5951_, lean_object* v_a_x3f_5952_){
_start:
{
lean_object* v___x_5954_; lean_object* v_env_5955_; lean_object* v_nextMacroScope_5956_; lean_object* v_ngen_5957_; lean_object* v_auxDeclNGen_5958_; lean_object* v_traceState_5959_; lean_object* v_recordedDeps_5960_; lean_object* v_messages_5961_; lean_object* v_infoState_5962_; lean_object* v_snapshotTasks_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5988_; 
v___x_5954_ = lean_st_ref_take(v___y_5947_);
v_env_5955_ = lean_ctor_get(v___x_5954_, 0);
v_nextMacroScope_5956_ = lean_ctor_get(v___x_5954_, 1);
v_ngen_5957_ = lean_ctor_get(v___x_5954_, 2);
v_auxDeclNGen_5958_ = lean_ctor_get(v___x_5954_, 3);
v_traceState_5959_ = lean_ctor_get(v___x_5954_, 4);
v_recordedDeps_5960_ = lean_ctor_get(v___x_5954_, 6);
v_messages_5961_ = lean_ctor_get(v___x_5954_, 7);
v_infoState_5962_ = lean_ctor_get(v___x_5954_, 8);
v_snapshotTasks_5963_ = lean_ctor_get(v___x_5954_, 9);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_5988_ == 0)
{
lean_object* v_unused_5989_; 
v_unused_5989_ = lean_ctor_get(v___x_5954_, 5);
lean_dec(v_unused_5989_);
v___x_5965_ = v___x_5954_;
v_isShared_5966_ = v_isSharedCheck_5988_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_snapshotTasks_5963_);
lean_inc(v_infoState_5962_);
lean_inc(v_messages_5961_);
lean_inc(v_recordedDeps_5960_);
lean_inc(v_traceState_5959_);
lean_inc(v_auxDeclNGen_5958_);
lean_inc(v_ngen_5957_);
lean_inc(v_nextMacroScope_5956_);
lean_inc(v_env_5955_);
lean_dec(v___x_5954_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5988_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5967_; lean_object* v___x_5969_; 
v___x_5967_ = l_Lean_Environment_setExporting(v_env_5955_, v_isExporting_5948_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 5, v___x_5949_);
lean_ctor_set(v___x_5965_, 0, v___x_5967_);
v___x_5969_ = v___x_5965_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5987_, 1, v_nextMacroScope_5956_);
lean_ctor_set(v_reuseFailAlloc_5987_, 2, v_ngen_5957_);
lean_ctor_set(v_reuseFailAlloc_5987_, 3, v_auxDeclNGen_5958_);
lean_ctor_set(v_reuseFailAlloc_5987_, 4, v_traceState_5959_);
lean_ctor_set(v_reuseFailAlloc_5987_, 5, v___x_5949_);
lean_ctor_set(v_reuseFailAlloc_5987_, 6, v_recordedDeps_5960_);
lean_ctor_set(v_reuseFailAlloc_5987_, 7, v_messages_5961_);
lean_ctor_set(v_reuseFailAlloc_5987_, 8, v_infoState_5962_);
lean_ctor_set(v_reuseFailAlloc_5987_, 9, v_snapshotTasks_5963_);
v___x_5969_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v_mctx_5972_; lean_object* v_zetaDeltaFVarIds_5973_; lean_object* v_postponed_5974_; lean_object* v_diag_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_5985_; 
v___x_5970_ = lean_st_ref_put(v___y_5947_, v___x_5969_);
v___x_5971_ = lean_st_ref_take(v___y_5950_);
v_mctx_5972_ = lean_ctor_get(v___x_5971_, 0);
v_zetaDeltaFVarIds_5973_ = lean_ctor_get(v___x_5971_, 2);
v_postponed_5974_ = lean_ctor_get(v___x_5971_, 3);
v_diag_5975_ = lean_ctor_get(v___x_5971_, 4);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5971_);
if (v_isSharedCheck_5985_ == 0)
{
lean_object* v_unused_5986_; 
v_unused_5986_ = lean_ctor_get(v___x_5971_, 1);
lean_dec(v_unused_5986_);
v___x_5977_ = v___x_5971_;
v_isShared_5978_ = v_isSharedCheck_5985_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_diag_5975_);
lean_inc(v_postponed_5974_);
lean_inc(v_zetaDeltaFVarIds_5973_);
lean_inc(v_mctx_5972_);
lean_dec(v___x_5971_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_5985_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v___x_5979_; lean_object* v___x_5981_; 
v___x_5979_ = lean_box(0);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 1, v___x_5951_);
v___x_5981_ = v___x_5977_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_mctx_5972_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5984_, 2, v_zetaDeltaFVarIds_5973_);
lean_ctor_set(v_reuseFailAlloc_5984_, 3, v_postponed_5974_);
lean_ctor_set(v_reuseFailAlloc_5984_, 4, v_diag_5975_);
v___x_5981_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = lean_st_ref_put(v___y_5950_, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5979_);
return v___x_5983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_5990_, lean_object* v_isExporting_5991_, lean_object* v___x_5992_, lean_object* v___y_5993_, lean_object* v___x_5994_, lean_object* v_a_x3f_5995_, lean_object* v___y_5996_){
_start:
{
uint8_t v_isExporting_boxed_5997_; lean_object* v_res_5998_; 
v_isExporting_boxed_5997_ = lean_unbox(v_isExporting_5991_);
v_res_5998_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_5990_, v_isExporting_boxed_5997_, v___x_5992_, v___y_5993_, v___x_5994_, v_a_x3f_5995_);
lean_dec(v_a_x3f_5995_);
lean_dec(v___y_5993_);
lean_dec(v___y_5990_);
return v_res_5998_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_6000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
return v___x_6000_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; 
v___x_6001_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6001_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
return v___x_6002_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_6003_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6004_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
lean_ctor_set(v___x_6004_, 2, v___x_6003_);
lean_ctor_set(v___x_6004_, 3, v___x_6003_);
lean_ctor_set(v___x_6004_, 4, v___x_6003_);
lean_ctor_set(v___x_6004_, 5, v___x_6003_);
return v___x_6004_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6005_, uint8_t v_isExporting_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v___x_6012_; lean_object* v_env_6013_; lean_object* v___x_6014_; uint8_t v_isModule_6015_; 
v___x_6012_ = lean_st_ref_get(v___y_6010_);
v_env_6013_ = lean_ctor_get(v___x_6012_, 0);
lean_inc_ref(v_env_6013_);
lean_dec(v___x_6012_);
v___x_6014_ = l_Lean_Environment_header(v_env_6013_);
v_isModule_6015_ = lean_ctor_get_uint8(v___x_6014_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_6014_);
if (v_isModule_6015_ == 0)
{
lean_object* v___x_6016_; 
lean_dec_ref(v_env_6013_);
lean_inc(v___y_6010_);
lean_inc_ref(v___y_6009_);
lean_inc(v___y_6008_);
lean_inc_ref(v___y_6007_);
v___x_6016_ = lean_apply_5(v_x_6005_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, lean_box(0));
return v___x_6016_;
}
else
{
uint8_t v_isExporting_6017_; 
v_isExporting_6017_ = lean_ctor_get_uint8(v_env_6013_, sizeof(void*)*13);
lean_dec_ref(v_env_6013_);
if (v_isExporting_6006_ == 0)
{
if (v_isExporting_6017_ == 0)
{
lean_object* v___x_6084_; 
lean_inc(v___y_6010_);
lean_inc_ref(v___y_6009_);
lean_inc(v___y_6008_);
lean_inc_ref(v___y_6007_);
v___x_6084_ = lean_apply_5(v_x_6005_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, lean_box(0));
return v___x_6084_;
}
else
{
goto v___jp_6018_;
}
}
else
{
if (v_isExporting_6017_ == 0)
{
goto v___jp_6018_;
}
else
{
lean_object* v___x_6085_; 
lean_inc(v___y_6010_);
lean_inc_ref(v___y_6009_);
lean_inc(v___y_6008_);
lean_inc_ref(v___y_6007_);
v___x_6085_ = lean_apply_5(v_x_6005_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, lean_box(0));
return v___x_6085_;
}
}
v___jp_6018_:
{
lean_object* v___x_6019_; lean_object* v_env_6020_; lean_object* v_nextMacroScope_6021_; lean_object* v_ngen_6022_; lean_object* v_auxDeclNGen_6023_; lean_object* v_traceState_6024_; lean_object* v_recordedDeps_6025_; lean_object* v_messages_6026_; lean_object* v_infoState_6027_; lean_object* v_snapshotTasks_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6082_; 
v___x_6019_ = lean_st_ref_take(v___y_6010_);
v_env_6020_ = lean_ctor_get(v___x_6019_, 0);
v_nextMacroScope_6021_ = lean_ctor_get(v___x_6019_, 1);
v_ngen_6022_ = lean_ctor_get(v___x_6019_, 2);
v_auxDeclNGen_6023_ = lean_ctor_get(v___x_6019_, 3);
v_traceState_6024_ = lean_ctor_get(v___x_6019_, 4);
v_recordedDeps_6025_ = lean_ctor_get(v___x_6019_, 6);
v_messages_6026_ = lean_ctor_get(v___x_6019_, 7);
v_infoState_6027_ = lean_ctor_get(v___x_6019_, 8);
v_snapshotTasks_6028_ = lean_ctor_get(v___x_6019_, 9);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6019_);
if (v_isSharedCheck_6082_ == 0)
{
lean_object* v_unused_6083_; 
v_unused_6083_ = lean_ctor_get(v___x_6019_, 5);
lean_dec(v_unused_6083_);
v___x_6030_ = v___x_6019_;
v_isShared_6031_ = v_isSharedCheck_6082_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_snapshotTasks_6028_);
lean_inc(v_infoState_6027_);
lean_inc(v_messages_6026_);
lean_inc(v_recordedDeps_6025_);
lean_inc(v_traceState_6024_);
lean_inc(v_auxDeclNGen_6023_);
lean_inc(v_ngen_6022_);
lean_inc(v_nextMacroScope_6021_);
lean_inc(v_env_6020_);
lean_dec(v___x_6019_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6082_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6035_; 
v___x_6032_ = l_Lean_Environment_setExporting(v_env_6020_, v_isExporting_6006_);
v___x_6033_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
if (v_isShared_6031_ == 0)
{
lean_ctor_set(v___x_6030_, 5, v___x_6033_);
lean_ctor_set(v___x_6030_, 0, v___x_6032_);
v___x_6035_ = v___x_6030_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6032_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v_nextMacroScope_6021_);
lean_ctor_set(v_reuseFailAlloc_6081_, 2, v_ngen_6022_);
lean_ctor_set(v_reuseFailAlloc_6081_, 3, v_auxDeclNGen_6023_);
lean_ctor_set(v_reuseFailAlloc_6081_, 4, v_traceState_6024_);
lean_ctor_set(v_reuseFailAlloc_6081_, 5, v___x_6033_);
lean_ctor_set(v_reuseFailAlloc_6081_, 6, v_recordedDeps_6025_);
lean_ctor_set(v_reuseFailAlloc_6081_, 7, v_messages_6026_);
lean_ctor_set(v_reuseFailAlloc_6081_, 8, v_infoState_6027_);
lean_ctor_set(v_reuseFailAlloc_6081_, 9, v_snapshotTasks_6028_);
v___x_6035_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v_mctx_6038_; lean_object* v_zetaDeltaFVarIds_6039_; lean_object* v_postponed_6040_; lean_object* v_diag_6041_; lean_object* v___x_6043_; uint8_t v_isShared_6044_; uint8_t v_isSharedCheck_6079_; 
v___x_6036_ = lean_st_ref_put(v___y_6010_, v___x_6035_);
v___x_6037_ = lean_st_ref_take(v___y_6008_);
v_mctx_6038_ = lean_ctor_get(v___x_6037_, 0);
v_zetaDeltaFVarIds_6039_ = lean_ctor_get(v___x_6037_, 2);
v_postponed_6040_ = lean_ctor_get(v___x_6037_, 3);
v_diag_6041_ = lean_ctor_get(v___x_6037_, 4);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6079_ == 0)
{
lean_object* v_unused_6080_; 
v_unused_6080_ = lean_ctor_get(v___x_6037_, 1);
lean_dec(v_unused_6080_);
v___x_6043_ = v___x_6037_;
v_isShared_6044_ = v_isSharedCheck_6079_;
goto v_resetjp_6042_;
}
else
{
lean_inc(v_diag_6041_);
lean_inc(v_postponed_6040_);
lean_inc(v_zetaDeltaFVarIds_6039_);
lean_inc(v_mctx_6038_);
lean_dec(v___x_6037_);
v___x_6043_ = lean_box(0);
v_isShared_6044_ = v_isSharedCheck_6079_;
goto v_resetjp_6042_;
}
v_resetjp_6042_:
{
lean_object* v___x_6045_; lean_object* v___x_6047_; 
v___x_6045_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6044_ == 0)
{
lean_ctor_set(v___x_6043_, 1, v___x_6045_);
v___x_6047_ = v___x_6043_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_mctx_6038_);
lean_ctor_set(v_reuseFailAlloc_6078_, 1, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6078_, 2, v_zetaDeltaFVarIds_6039_);
lean_ctor_set(v_reuseFailAlloc_6078_, 3, v_postponed_6040_);
lean_ctor_set(v_reuseFailAlloc_6078_, 4, v_diag_6041_);
v___x_6047_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
lean_object* v___x_6048_; lean_object* v_r_6049_; 
v___x_6048_ = lean_st_ref_put(v___y_6008_, v___x_6047_);
lean_inc(v___y_6010_);
lean_inc_ref(v___y_6009_);
lean_inc(v___y_6008_);
lean_inc_ref(v___y_6007_);
v_r_6049_ = lean_apply_5(v_x_6005_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, lean_box(0));
if (lean_obj_tag(v_r_6049_) == 0)
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6066_; 
v_a_6050_ = lean_ctor_get(v_r_6049_, 0);
v_isSharedCheck_6066_ = !lean_is_exclusive(v_r_6049_);
if (v_isSharedCheck_6066_ == 0)
{
v___x_6052_ = v_r_6049_;
v_isShared_6053_ = v_isSharedCheck_6066_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v_r_6049_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6066_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
lean_inc(v_a_6050_);
if (v_isShared_6053_ == 0)
{
lean_ctor_set_tag(v___x_6052_, 1);
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
lean_object* v___x_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6063_; 
v___x_6056_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6010_, v_isExporting_6017_, v___x_6033_, v___y_6008_, v___x_6045_, v___x_6055_);
lean_dec_ref(v___x_6055_);
v_isSharedCheck_6063_ = !lean_is_exclusive(v___x_6056_);
if (v_isSharedCheck_6063_ == 0)
{
lean_object* v_unused_6064_; 
v_unused_6064_ = lean_ctor_get(v___x_6056_, 0);
lean_dec(v_unused_6064_);
v___x_6058_ = v___x_6056_;
v_isShared_6059_ = v_isSharedCheck_6063_;
goto v_resetjp_6057_;
}
else
{
lean_dec(v___x_6056_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6063_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6061_; 
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 0, v_a_6050_);
v___x_6061_ = v___x_6058_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6062_; 
v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6050_);
v___x_6061_ = v_reuseFailAlloc_6062_;
goto v_reusejp_6060_;
}
v_reusejp_6060_:
{
return v___x_6061_;
}
}
}
}
}
else
{
lean_object* v_a_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6071_; uint8_t v_isShared_6072_; uint8_t v_isSharedCheck_6076_; 
v_a_6067_ = lean_ctor_get(v_r_6049_, 0);
lean_inc(v_a_6067_);
lean_dec_ref_known(v_r_6049_, 1);
v___x_6068_ = lean_box(0);
v___x_6069_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6010_, v_isExporting_6017_, v___x_6033_, v___y_6008_, v___x_6045_, v___x_6068_);
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
lean_ctor_set_tag(v___x_6071_, 1);
lean_ctor_set(v___x_6071_, 0, v_a_6067_);
v___x_6074_ = v___x_6071_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6067_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6086_, lean_object* v_isExporting_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_){
_start:
{
uint8_t v_isExporting_boxed_6093_; lean_object* v_res_6094_; 
v_isExporting_boxed_6093_ = lean_unbox(v_isExporting_6087_);
v_res_6094_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6086_, v_isExporting_boxed_6093_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
lean_dec(v___y_6089_);
lean_dec_ref(v___y_6088_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6095_, uint8_t v_when_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_){
_start:
{
if (v_when_6096_ == 0)
{
lean_object* v___x_6102_; 
lean_inc(v___y_6100_);
lean_inc_ref(v___y_6099_);
lean_inc(v___y_6098_);
lean_inc_ref(v___y_6097_);
v___x_6102_ = lean_apply_5(v_x_6095_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, lean_box(0));
return v___x_6102_;
}
else
{
uint8_t v___x_6103_; lean_object* v___x_6104_; 
v___x_6103_ = 0;
v___x_6104_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6095_, v___x_6103_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
return v___x_6104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6105_, lean_object* v_when_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_){
_start:
{
uint8_t v_when_boxed_6112_; lean_object* v_res_6113_; 
v_when_boxed_6112_ = lean_unbox(v_when_6106_);
v_res_6113_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6105_, v_when_boxed_6112_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
return v_res_6113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6114_, lean_object* v_argsPacker_6115_, lean_object* v_decrTactics_6116_, lean_object* v_value_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_){
_start:
{
lean_object* v___f_6123_; uint8_t v___x_6124_; lean_object* v___x_6125_; 
v___f_6123_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6123_, 0, v_value_6117_);
lean_closure_set(v___f_6123_, 1, v_decrTactics_6116_);
lean_closure_set(v___f_6123_, 2, v_argsPacker_6115_);
lean_closure_set(v___f_6123_, 3, v_funNames_6114_);
v___x_6124_ = 1;
v___x_6125_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6123_, v___x_6124_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_);
return v___x_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6126_, lean_object* v_argsPacker_6127_, lean_object* v_decrTactics_6128_, lean_object* v_value_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6126_, v_argsPacker_6127_, v_decrTactics_6128_, v_value_6129_, v_a_6130_, v_a_6131_, v_a_6132_, v_a_6133_);
lean_dec(v_a_6133_);
lean_dec_ref(v_a_6132_);
lean_dec(v_a_6131_);
lean_dec_ref(v_a_6130_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6136_, lean_object* v_msg_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
lean_object* v___x_6145_; 
v___x_6145_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_);
return v___x_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6146_, lean_object* v_msg_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
lean_object* v_res_6155_; 
v_res_6155_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6146_, v_msg_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
lean_dec(v___y_6151_);
lean_dec_ref(v___y_6150_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_){
_start:
{
lean_object* v___x_6165_; 
v___x_6165_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6163_);
return v___x_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
lean_dec_ref(v___y_6168_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6176_, lean_object* v_x_6177_, lean_object* v_mkInfoTree_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v___x_6188_; 
v___x_6188_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6177_, v_mkInfoTree_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_);
return v___x_6188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6189_, lean_object* v_x_6190_, lean_object* v_mkInfoTree_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_){
_start:
{
lean_object* v_res_6201_; 
v_res_6201_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6189_, v_x_6190_, v_mkInfoTree_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
lean_dec(v___y_6199_);
lean_dec_ref(v___y_6198_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
return v_res_6201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6202_, size_t v_i_6203_, size_t v_stop_6204_, lean_object* v_b_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v___x_6213_; 
v___x_6213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6202_, v_i_6203_, v_stop_6204_, v_b_6205_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6214_, lean_object* v_i_6215_, lean_object* v_stop_6216_, lean_object* v_b_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
size_t v_i_boxed_6225_; size_t v_stop_boxed_6226_; lean_object* v_res_6227_; 
v_i_boxed_6225_ = lean_unbox_usize(v_i_6215_);
lean_dec(v_i_6215_);
v_stop_boxed_6226_ = lean_unbox_usize(v_stop_6216_);
lean_dec(v_stop_6216_);
v_res_6227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6214_, v_i_boxed_6225_, v_stop_boxed_6226_, v_b_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec(v___y_6221_);
lean_dec_ref(v___y_6220_);
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec_ref(v_as_6214_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6228_, lean_object* v_x_6229_, uint8_t v_isExporting_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6229_, v_isExporting_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
return v___x_6236_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6237_, lean_object* v_x_6238_, lean_object* v_isExporting_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_){
_start:
{
uint8_t v_isExporting_boxed_6245_; lean_object* v_res_6246_; 
v_isExporting_boxed_6245_ = lean_unbox(v_isExporting_6239_);
v_res_6246_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6237_, v_x_6238_, v_isExporting_boxed_6245_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
return v_res_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6247_, lean_object* v_x_6248_, uint8_t v_when_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_){
_start:
{
lean_object* v___x_6255_; 
v___x_6255_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6248_, v_when_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6256_, lean_object* v_x_6257_, lean_object* v_when_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_){
_start:
{
uint8_t v_when_boxed_6264_; lean_object* v_res_6265_; 
v_when_boxed_6264_ = lean_unbox(v_when_6258_);
v_res_6265_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6256_, v_x_6257_, v_when_boxed_6264_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
lean_dec(v___y_6262_);
lean_dec_ref(v___y_6261_);
lean_dec(v___y_6260_);
lean_dec_ref(v___y_6259_);
return v_res_6265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6266_, lean_object* v_macroStack_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
lean_object* v___x_6275_; 
v___x_6275_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6266_, v_macroStack_6267_, v___y_6272_);
return v___x_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6276_, lean_object* v_macroStack_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_){
_start:
{
lean_object* v_res_6285_; 
v_res_6285_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6276_, v_macroStack_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6280_);
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6278_);
return v_res_6285_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6292_ = lean_box(0);
v___x_6293_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6294_ = l_Lean_mkConst(v___x_6293_, v___x_6292_);
return v___x_6294_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6299_ = lean_box(0);
v___x_6300_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6301_ = l_Lean_mkConst(v___x_6300_, v___x_6299_);
return v___x_6301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6302_, lean_object* v_a_6303_, lean_object* v_a_6304_, lean_object* v_a_6305_, lean_object* v_a_6306_){
_start:
{
lean_object* v___x_6311_; 
v___x_6311_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6302_, v_a_6304_);
if (lean_obj_tag(v___x_6311_) == 0)
{
lean_object* v_a_6312_; lean_object* v___x_6313_; uint8_t v___x_6314_; 
v_a_6312_ = lean_ctor_get(v___x_6311_, 0);
lean_inc(v_a_6312_);
lean_dec_ref_known(v___x_6311_, 1);
v___x_6313_ = l_Lean_Expr_cleanupAnnotations(v_a_6312_);
v___x_6314_ = l_Lean_Expr_isApp(v___x_6313_);
if (v___x_6314_ == 0)
{
lean_dec_ref(v___x_6313_);
goto v___jp_6308_;
}
else
{
lean_object* v_arg_6315_; lean_object* v___x_6316_; uint8_t v___x_6317_; 
v_arg_6315_ = lean_ctor_get(v___x_6313_, 1);
lean_inc_ref(v_arg_6315_);
v___x_6316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6313_);
v___x_6317_ = l_Lean_Expr_isApp(v___x_6316_);
if (v___x_6317_ == 0)
{
lean_dec_ref(v___x_6316_);
lean_dec_ref(v_arg_6315_);
goto v___jp_6308_;
}
else
{
lean_object* v_arg_6318_; lean_object* v___x_6319_; uint8_t v___x_6320_; 
v_arg_6318_ = lean_ctor_get(v___x_6316_, 1);
lean_inc_ref(v_arg_6318_);
v___x_6319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6316_);
v___x_6320_ = l_Lean_Expr_isApp(v___x_6319_);
if (v___x_6320_ == 0)
{
lean_dec_ref(v___x_6319_);
lean_dec_ref(v_arg_6318_);
lean_dec_ref(v_arg_6315_);
goto v___jp_6308_;
}
else
{
lean_object* v_arg_6321_; lean_object* v___x_6322_; uint8_t v___x_6323_; 
v_arg_6321_ = lean_ctor_get(v___x_6319_, 1);
lean_inc_ref(v_arg_6321_);
v___x_6322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6319_);
v___x_6323_ = l_Lean_Expr_isApp(v___x_6322_);
if (v___x_6323_ == 0)
{
lean_dec_ref(v___x_6322_);
lean_dec_ref(v_arg_6321_);
lean_dec_ref(v_arg_6318_);
lean_dec_ref(v_arg_6315_);
goto v___jp_6308_;
}
else
{
lean_object* v___x_6324_; lean_object* v___x_6325_; uint8_t v___x_6326_; 
v___x_6324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6322_);
v___x_6325_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6326_ = l_Lean_Expr_isConstOf(v___x_6324_, v___x_6325_);
lean_dec_ref(v___x_6324_);
if (v___x_6326_ == 0)
{
lean_dec_ref(v_arg_6321_);
lean_dec_ref(v_arg_6318_);
lean_dec_ref(v_arg_6315_);
goto v___jp_6308_;
}
else
{
lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6327_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6328_ = l_Lean_Meta_isExprDefEq(v_arg_6321_, v___x_6327_, v_a_6303_, v_a_6304_, v_a_6305_, v_a_6306_);
if (lean_obj_tag(v___x_6328_) == 0)
{
lean_object* v_a_6329_; lean_object* v___x_6331_; uint8_t v_isShared_6332_; uint8_t v_isSharedCheck_6362_; 
v_a_6329_ = lean_ctor_get(v___x_6328_, 0);
v_isSharedCheck_6362_ = !lean_is_exclusive(v___x_6328_);
if (v_isSharedCheck_6362_ == 0)
{
v___x_6331_ = v___x_6328_;
v_isShared_6332_ = v_isSharedCheck_6362_;
goto v_resetjp_6330_;
}
else
{
lean_inc(v_a_6329_);
lean_dec(v___x_6328_);
v___x_6331_ = lean_box(0);
v_isShared_6332_ = v_isSharedCheck_6362_;
goto v_resetjp_6330_;
}
v_resetjp_6330_:
{
uint8_t v___x_6333_; 
v___x_6333_ = lean_unbox(v_a_6329_);
lean_dec(v_a_6329_);
if (v___x_6333_ == 0)
{
lean_object* v___x_6334_; lean_object* v___x_6336_; 
lean_dec_ref(v_arg_6318_);
lean_dec_ref(v_arg_6315_);
v___x_6334_ = lean_box(0);
if (v_isShared_6332_ == 0)
{
lean_ctor_set(v___x_6331_, 0, v___x_6334_);
v___x_6336_ = v___x_6331_;
goto v_reusejp_6335_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v___x_6334_);
v___x_6336_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6335_;
}
v_reusejp_6335_:
{
return v___x_6336_;
}
}
else
{
lean_object* v___x_6338_; lean_object* v___x_6339_; 
lean_del_object(v___x_6331_);
v___x_6338_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6339_ = l_Lean_Meta_isExprDefEq(v_arg_6315_, v___x_6338_, v_a_6303_, v_a_6304_, v_a_6305_, v_a_6306_);
if (lean_obj_tag(v___x_6339_) == 0)
{
lean_object* v_a_6340_; lean_object* v___x_6342_; uint8_t v_isShared_6343_; uint8_t v_isSharedCheck_6353_; 
v_a_6340_ = lean_ctor_get(v___x_6339_, 0);
v_isSharedCheck_6353_ = !lean_is_exclusive(v___x_6339_);
if (v_isSharedCheck_6353_ == 0)
{
v___x_6342_ = v___x_6339_;
v_isShared_6343_ = v_isSharedCheck_6353_;
goto v_resetjp_6341_;
}
else
{
lean_inc(v_a_6340_);
lean_dec(v___x_6339_);
v___x_6342_ = lean_box(0);
v_isShared_6343_ = v_isSharedCheck_6353_;
goto v_resetjp_6341_;
}
v_resetjp_6341_:
{
uint8_t v___x_6344_; 
v___x_6344_ = lean_unbox(v_a_6340_);
lean_dec(v_a_6340_);
if (v___x_6344_ == 0)
{
lean_object* v___x_6345_; lean_object* v___x_6347_; 
lean_dec_ref(v_arg_6318_);
v___x_6345_ = lean_box(0);
if (v_isShared_6343_ == 0)
{
lean_ctor_set(v___x_6342_, 0, v___x_6345_);
v___x_6347_ = v___x_6342_;
goto v_reusejp_6346_;
}
else
{
lean_object* v_reuseFailAlloc_6348_; 
v_reuseFailAlloc_6348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6348_, 0, v___x_6345_);
v___x_6347_ = v_reuseFailAlloc_6348_;
goto v_reusejp_6346_;
}
v_reusejp_6346_:
{
return v___x_6347_;
}
}
else
{
lean_object* v___x_6349_; lean_object* v___x_6351_; 
v___x_6349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6349_, 0, v_arg_6318_);
if (v_isShared_6343_ == 0)
{
lean_ctor_set(v___x_6342_, 0, v___x_6349_);
v___x_6351_ = v___x_6342_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v___x_6349_);
v___x_6351_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
return v___x_6351_;
}
}
}
}
else
{
lean_object* v_a_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6361_; 
lean_dec_ref(v_arg_6318_);
v_a_6354_ = lean_ctor_get(v___x_6339_, 0);
v_isSharedCheck_6361_ = !lean_is_exclusive(v___x_6339_);
if (v_isSharedCheck_6361_ == 0)
{
v___x_6356_ = v___x_6339_;
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_a_6354_);
lean_dec(v___x_6339_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v___x_6359_; 
if (v_isShared_6357_ == 0)
{
v___x_6359_ = v___x_6356_;
goto v_reusejp_6358_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_a_6354_);
v___x_6359_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6358_;
}
v_reusejp_6358_:
{
return v___x_6359_;
}
}
}
}
}
}
else
{
lean_object* v_a_6363_; lean_object* v___x_6365_; uint8_t v_isShared_6366_; uint8_t v_isSharedCheck_6370_; 
lean_dec_ref(v_arg_6318_);
lean_dec_ref(v_arg_6315_);
v_a_6363_ = lean_ctor_get(v___x_6328_, 0);
v_isSharedCheck_6370_ = !lean_is_exclusive(v___x_6328_);
if (v_isSharedCheck_6370_ == 0)
{
v___x_6365_ = v___x_6328_;
v_isShared_6366_ = v_isSharedCheck_6370_;
goto v_resetjp_6364_;
}
else
{
lean_inc(v_a_6363_);
lean_dec(v___x_6328_);
v___x_6365_ = lean_box(0);
v_isShared_6366_ = v_isSharedCheck_6370_;
goto v_resetjp_6364_;
}
v_resetjp_6364_:
{
lean_object* v___x_6368_; 
if (v_isShared_6366_ == 0)
{
v___x_6368_ = v___x_6365_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6369_; 
v_reuseFailAlloc_6369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_a_6363_);
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
}
}
}
}
}
else
{
lean_object* v_a_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6378_; 
v_a_6371_ = lean_ctor_get(v___x_6311_, 0);
v_isSharedCheck_6378_ = !lean_is_exclusive(v___x_6311_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6373_ = v___x_6311_;
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_a_6371_);
lean_dec(v___x_6311_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v___x_6376_; 
if (v_isShared_6374_ == 0)
{
v___x_6376_ = v___x_6373_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_a_6371_);
v___x_6376_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
return v___x_6376_;
}
}
}
v___jp_6308_:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6309_ = lean_box(0);
v___x_6310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6310_, 0, v___x_6309_);
return v___x_6310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6379_, lean_object* v_a_6380_, lean_object* v_a_6381_, lean_object* v_a_6382_, lean_object* v_a_6383_, lean_object* v_a_6384_){
_start:
{
lean_object* v_res_6385_; 
v_res_6385_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6379_, v_a_6380_, v_a_6381_, v_a_6382_, v_a_6383_);
lean_dec(v_a_6383_);
lean_dec_ref(v_a_6382_);
lean_dec(v_a_6381_);
lean_dec_ref(v_a_6380_);
return v_res_6385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6386_, lean_object* v_maxFVars_x3f_6387_, lean_object* v_k_6388_, uint8_t v_cleanupAnnotations_6389_, uint8_t v_whnfType_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_){
_start:
{
lean_object* v___f_6398_; lean_object* v___x_6399_; 
lean_inc(v___y_6392_);
lean_inc_ref(v___y_6391_);
v___f_6398_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6398_, 0, v_k_6388_);
lean_closure_set(v___f_6398_, 1, v___y_6391_);
lean_closure_set(v___f_6398_, 2, v___y_6392_);
v___x_6399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6386_, v_maxFVars_x3f_6387_, v___f_6398_, v_cleanupAnnotations_6389_, v_whnfType_6390_, v___y_6393_, v___y_6394_, v___y_6395_, v___y_6396_);
if (lean_obj_tag(v___x_6399_) == 0)
{
return v___x_6399_;
}
else
{
lean_object* v_a_6400_; lean_object* v___x_6402_; uint8_t v_isShared_6403_; uint8_t v_isSharedCheck_6407_; 
v_a_6400_ = lean_ctor_get(v___x_6399_, 0);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6402_ = v___x_6399_;
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
else
{
lean_inc(v_a_6400_);
lean_dec(v___x_6399_);
v___x_6402_ = lean_box(0);
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
v_resetjp_6401_:
{
lean_object* v___x_6405_; 
if (v_isShared_6403_ == 0)
{
v___x_6405_ = v___x_6402_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_a_6400_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6408_, lean_object* v_maxFVars_x3f_6409_, lean_object* v_k_6410_, lean_object* v_cleanupAnnotations_6411_, lean_object* v_whnfType_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6420_; uint8_t v_whnfType_boxed_6421_; lean_object* v_res_6422_; 
v_cleanupAnnotations_boxed_6420_ = lean_unbox(v_cleanupAnnotations_6411_);
v_whnfType_boxed_6421_ = lean_unbox(v_whnfType_6412_);
v_res_6422_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6408_, v_maxFVars_x3f_6409_, v_k_6410_, v_cleanupAnnotations_boxed_6420_, v_whnfType_boxed_6421_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec_ref(v___y_6413_);
return v_res_6422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6423_, lean_object* v_type_6424_, lean_object* v_maxFVars_x3f_6425_, lean_object* v_k_6426_, uint8_t v_cleanupAnnotations_6427_, uint8_t v_whnfType_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_){
_start:
{
lean_object* v___x_6436_; 
v___x_6436_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6424_, v_maxFVars_x3f_6425_, v_k_6426_, v_cleanupAnnotations_6427_, v_whnfType_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_);
return v___x_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6437_, lean_object* v_type_6438_, lean_object* v_maxFVars_x3f_6439_, lean_object* v_k_6440_, lean_object* v_cleanupAnnotations_6441_, lean_object* v_whnfType_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6450_; uint8_t v_whnfType_boxed_6451_; lean_object* v_res_6452_; 
v_cleanupAnnotations_boxed_6450_ = lean_unbox(v_cleanupAnnotations_6441_);
v_whnfType_boxed_6451_ = lean_unbox(v_whnfType_6442_);
v_res_6452_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6437_, v_type_6438_, v_maxFVars_x3f_6439_, v_k_6440_, v_cleanupAnnotations_boxed_6450_, v_whnfType_boxed_6451_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec(v___y_6448_);
lean_dec_ref(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec_ref(v___y_6445_);
lean_dec(v___y_6444_);
lean_dec_ref(v___y_6443_);
return v_res_6452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6453_, lean_object* v_x_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_){
_start:
{
lean_object* v_keyedConfig_6462_; uint8_t v_trackZetaDelta_6463_; lean_object* v_zetaDeltaSet_6464_; lean_object* v_localInstances_6465_; lean_object* v_defEqCtx_x3f_6466_; lean_object* v_synthPendingDepth_6467_; lean_object* v_customCanUnfoldPredicate_x3f_6468_; uint8_t v_univApprox_6469_; uint8_t v_inTypeClassResolution_6470_; uint8_t v_cacheInferType_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; 
v_keyedConfig_6462_ = lean_ctor_get(v___y_6457_, 0);
v_trackZetaDelta_6463_ = lean_ctor_get_uint8(v___y_6457_, sizeof(void*)*7);
v_zetaDeltaSet_6464_ = lean_ctor_get(v___y_6457_, 1);
v_localInstances_6465_ = lean_ctor_get(v___y_6457_, 3);
v_defEqCtx_x3f_6466_ = lean_ctor_get(v___y_6457_, 4);
v_synthPendingDepth_6467_ = lean_ctor_get(v___y_6457_, 5);
v_customCanUnfoldPredicate_x3f_6468_ = lean_ctor_get(v___y_6457_, 6);
v_univApprox_6469_ = lean_ctor_get_uint8(v___y_6457_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6470_ = lean_ctor_get_uint8(v___y_6457_, sizeof(void*)*7 + 2);
v_cacheInferType_6471_ = lean_ctor_get_uint8(v___y_6457_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6468_);
lean_inc(v_synthPendingDepth_6467_);
lean_inc(v_defEqCtx_x3f_6466_);
lean_inc_ref(v_localInstances_6465_);
lean_inc(v_zetaDeltaSet_6464_);
lean_inc_ref(v_keyedConfig_6462_);
v___x_6472_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6472_, 0, v_keyedConfig_6462_);
lean_ctor_set(v___x_6472_, 1, v_zetaDeltaSet_6464_);
lean_ctor_set(v___x_6472_, 2, v_lctx_6453_);
lean_ctor_set(v___x_6472_, 3, v_localInstances_6465_);
lean_ctor_set(v___x_6472_, 4, v_defEqCtx_x3f_6466_);
lean_ctor_set(v___x_6472_, 5, v_synthPendingDepth_6467_);
lean_ctor_set(v___x_6472_, 6, v_customCanUnfoldPredicate_x3f_6468_);
lean_ctor_set_uint8(v___x_6472_, sizeof(void*)*7, v_trackZetaDelta_6463_);
lean_ctor_set_uint8(v___x_6472_, sizeof(void*)*7 + 1, v_univApprox_6469_);
lean_ctor_set_uint8(v___x_6472_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6470_);
lean_ctor_set_uint8(v___x_6472_, sizeof(void*)*7 + 3, v_cacheInferType_6471_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
v___x_6473_ = lean_apply_7(v_x_6454_, v___y_6455_, v___y_6456_, v___x_6472_, v___y_6458_, v___y_6459_, v___y_6460_, lean_box(0));
if (lean_obj_tag(v___x_6473_) == 0)
{
lean_object* v_a_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6481_; 
v_a_6474_ = lean_ctor_get(v___x_6473_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6473_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6476_ = v___x_6473_;
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_a_6474_);
lean_dec(v___x_6473_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6479_; 
if (v_isShared_6477_ == 0)
{
v___x_6479_ = v___x_6476_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
v___x_6479_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
return v___x_6479_;
}
}
}
else
{
return v___x_6473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6482_, lean_object* v_x_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_){
_start:
{
lean_object* v_res_6491_; 
v_res_6491_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6482_, v_x_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
lean_dec(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec(v___y_6485_);
lean_dec_ref(v___y_6484_);
return v_res_6491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6492_, lean_object* v_lctx_6493_, lean_object* v_x_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_){
_start:
{
lean_object* v___x_6502_; 
v___x_6502_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6493_, v_x_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_);
return v___x_6502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6503_, lean_object* v_lctx_6504_, lean_object* v_x_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_){
_start:
{
lean_object* v_res_6513_; 
v_res_6513_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6503_, v_lctx_6504_, v_x_6505_, v___y_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_);
lean_dec(v___y_6511_);
lean_dec_ref(v___y_6510_);
lean_dec(v___y_6509_);
lean_dec_ref(v___y_6508_);
lean_dec(v___y_6507_);
lean_dec_ref(v___y_6506_);
return v_res_6513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v_prefixArgs_6514_, lean_object* v_declName_6515_, lean_object* v_x_6516_, lean_object* v_F_6517_, lean_object* v_val_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_){
_start:
{
lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; 
v___x_6526_ = lean_array_get_size(v_prefixArgs_6514_);
v___x_6527_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6527_, 0, v_declName_6515_);
lean_closure_set(v___x_6527_, 1, v___x_6526_);
v___x_6528_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6516_, v_F_6517_, v_val_6518_, v___x_6527_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v_prefixArgs_6529_, lean_object* v_declName_6530_, lean_object* v_x_6531_, lean_object* v_F_6532_, lean_object* v_val_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l_Lean_Elab_WF_mkFix___lam__0(v_prefixArgs_6529_, v_declName_6530_, v_x_6531_, v_F_6532_, v_val_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
lean_dec(v___y_6537_);
lean_dec_ref(v___y_6536_);
lean_dec(v___y_6535_);
lean_dec_ref(v___y_6534_);
lean_dec_ref(v_prefixArgs_6529_);
return v_res_6541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v___x_6558_, lean_object* v___x_6559_, lean_object* v_wfRel_6560_, lean_object* v_x_6561_, lean_object* v_type_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_, lean_object* v___y_6567_, lean_object* v___y_6568_){
_start:
{
lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; 
v___x_6570_ = lean_unsigned_to_nat(0u);
v___x_6571_ = lean_array_get_borrowed(v___x_6558_, v_x_6561_, v___x_6570_);
v___x_6572_ = l_Lean_Expr_fvarId_x21(v___x_6571_);
v___x_6573_ = l_Lean_FVarId_getUserName___redArg(v___x_6572_, v___y_6565_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6573_) == 0)
{
lean_object* v_a_6574_; lean_object* v___x_6575_; 
v_a_6574_ = lean_ctor_get(v___x_6573_, 0);
lean_inc(v_a_6574_);
lean_dec_ref_known(v___x_6573_, 1);
lean_inc(v___y_6568_);
lean_inc_ref(v___y_6567_);
lean_inc(v___y_6566_);
lean_inc_ref(v___y_6565_);
lean_inc(v___x_6571_);
v___x_6575_ = lean_infer_type(v___x_6571_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; lean_object* v___x_6577_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
lean_inc_n(v_a_6576_, 2);
lean_dec_ref_known(v___x_6575_, 1);
v___x_6577_ = l_Lean_Meta_getLevel(v_a_6576_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; lean_object* v___x_6579_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
lean_inc(v_a_6578_);
lean_dec_ref_known(v___x_6577_, 1);
lean_inc_ref(v_type_6562_);
v___x_6579_ = l_Lean_Meta_getLevel(v_type_6562_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v_a_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; uint8_t v___x_6583_; uint8_t v___x_6584_; uint8_t v___x_6585_; lean_object* v___x_6586_; 
v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
lean_inc(v_a_6580_);
lean_dec_ref_known(v___x_6579_, 1);
v___x_6581_ = lean_mk_empty_array_with_capacity(v___x_6559_);
lean_inc(v___x_6571_);
lean_inc_ref(v___x_6581_);
v___x_6582_ = lean_array_push(v___x_6581_, v___x_6571_);
v___x_6583_ = 0;
v___x_6584_ = 1;
v___x_6585_ = 1;
v___x_6586_ = l_Lean_Meta_mkLambdaFVars(v___x_6582_, v_type_6562_, v___x_6583_, v___x_6584_, v___x_6583_, v___x_6584_, v___x_6585_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
lean_dec_ref(v___x_6582_);
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_a_6587_; lean_object* v___x_6588_; 
v_a_6587_ = lean_ctor_get(v___x_6586_, 0);
lean_inc(v_a_6587_);
lean_dec_ref_known(v___x_6586_, 1);
lean_inc_ref(v_wfRel_6560_);
v___x_6588_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6560_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v___x_6591_; uint8_t v_isShared_6592_; uint8_t v_isSharedCheck_6633_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6633_ == 0)
{
v___x_6591_ = v___x_6588_;
v_isShared_6592_ = v_isSharedCheck_6633_;
goto v_resetjp_6590_;
}
else
{
lean_inc(v_a_6589_);
lean_dec(v___x_6588_);
v___x_6591_ = lean_box(0);
v_isShared_6592_ = v_isSharedCheck_6633_;
goto v_resetjp_6590_;
}
v_resetjp_6590_:
{
if (lean_obj_tag(v_a_6589_) == 1)
{
lean_object* v_val_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6602_; 
lean_dec_ref(v___x_6581_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_val_6593_ = lean_ctor_get(v_a_6589_, 0);
lean_inc(v_val_6593_);
lean_dec_ref_known(v_a_6589_, 1);
v___x_6594_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__2));
v___x_6595_ = lean_box(0);
v___x_6596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6596_, 0, v_a_6580_);
lean_ctor_set(v___x_6596_, 1, v___x_6595_);
v___x_6597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6597_, 0, v_a_6578_);
lean_ctor_set(v___x_6597_, 1, v___x_6596_);
v___x_6598_ = l_Lean_mkConst(v___x_6594_, v___x_6597_);
v___x_6599_ = l_Lean_mkApp3(v___x_6598_, v_a_6576_, v_a_6587_, v_val_6593_);
v___x_6600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6600_, 0, v___x_6599_);
lean_ctor_set(v___x_6600_, 1, v_a_6574_);
if (v_isShared_6592_ == 0)
{
lean_ctor_set(v___x_6591_, 0, v___x_6600_);
v___x_6602_ = v___x_6591_;
goto v_reusejp_6601_;
}
else
{
lean_object* v_reuseFailAlloc_6603_; 
v_reuseFailAlloc_6603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6603_, 0, v___x_6600_);
v___x_6602_ = v_reuseFailAlloc_6603_;
goto v_reusejp_6601_;
}
v_reusejp_6601_:
{
return v___x_6602_;
}
}
else
{
lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; 
lean_del_object(v___x_6591_);
lean_dec(v_a_6589_);
v___x_6604_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__4));
lean_inc_ref(v_wfRel_6560_);
v___x_6605_ = l_Lean_mkProj(v___x_6604_, v___x_6570_, v_wfRel_6560_);
v___x_6606_ = l_Lean_mkProj(v___x_6604_, v___x_6559_, v_wfRel_6560_);
v___x_6607_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__6));
v___x_6608_ = lean_array_push(v___x_6581_, v___x_6606_);
v___x_6609_ = l_Lean_Meta_mkAppM(v___x_6607_, v___x_6608_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
if (lean_obj_tag(v___x_6609_) == 0)
{
lean_object* v_a_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6624_; 
v_a_6610_ = lean_ctor_get(v___x_6609_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6609_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6612_ = v___x_6609_;
v_isShared_6613_ = v_isSharedCheck_6624_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_a_6610_);
lean_dec(v___x_6609_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6624_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6622_; 
v___x_6614_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__7));
v___x_6615_ = lean_box(0);
v___x_6616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6616_, 0, v_a_6580_);
lean_ctor_set(v___x_6616_, 1, v___x_6615_);
v___x_6617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6617_, 0, v_a_6578_);
lean_ctor_set(v___x_6617_, 1, v___x_6616_);
v___x_6618_ = l_Lean_mkConst(v___x_6614_, v___x_6617_);
v___x_6619_ = l_Lean_mkApp4(v___x_6618_, v_a_6576_, v_a_6587_, v___x_6605_, v_a_6610_);
v___x_6620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6620_, 0, v___x_6619_);
lean_ctor_set(v___x_6620_, 1, v_a_6574_);
if (v_isShared_6613_ == 0)
{
lean_ctor_set(v___x_6612_, 0, v___x_6620_);
v___x_6622_ = v___x_6612_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v___x_6620_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
return v___x_6622_;
}
}
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_dec_ref(v___x_6605_);
lean_dec(v_a_6587_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec(v_a_6576_);
lean_dec(v_a_6574_);
v_a_6625_ = lean_ctor_get(v___x_6609_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6609_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6609_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6609_);
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
}
}
else
{
lean_object* v_a_6634_; lean_object* v___x_6636_; uint8_t v_isShared_6637_; uint8_t v_isSharedCheck_6641_; 
lean_dec(v_a_6587_);
lean_dec_ref(v___x_6581_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec(v_a_6576_);
lean_dec(v_a_6574_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6634_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6636_ = v___x_6588_;
v_isShared_6637_ = v_isSharedCheck_6641_;
goto v_resetjp_6635_;
}
else
{
lean_inc(v_a_6634_);
lean_dec(v___x_6588_);
v___x_6636_ = lean_box(0);
v_isShared_6637_ = v_isSharedCheck_6641_;
goto v_resetjp_6635_;
}
v_resetjp_6635_:
{
lean_object* v___x_6639_; 
if (v_isShared_6637_ == 0)
{
v___x_6639_ = v___x_6636_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6640_; 
v_reuseFailAlloc_6640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
v___x_6639_ = v_reuseFailAlloc_6640_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
return v___x_6639_;
}
}
}
}
else
{
lean_object* v_a_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6649_; 
lean_dec_ref(v___x_6581_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec(v_a_6576_);
lean_dec(v_a_6574_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6642_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6649_ == 0)
{
v___x_6644_ = v___x_6586_;
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_a_6642_);
lean_dec(v___x_6586_);
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
v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_6650_; lean_object* v___x_6652_; uint8_t v_isShared_6653_; uint8_t v_isSharedCheck_6657_; 
lean_dec(v_a_6578_);
lean_dec(v_a_6576_);
lean_dec(v_a_6574_);
lean_dec_ref(v_type_6562_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6650_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6657_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6657_ == 0)
{
v___x_6652_ = v___x_6579_;
v_isShared_6653_ = v_isSharedCheck_6657_;
goto v_resetjp_6651_;
}
else
{
lean_inc(v_a_6650_);
lean_dec(v___x_6579_);
v___x_6652_ = lean_box(0);
v_isShared_6653_ = v_isSharedCheck_6657_;
goto v_resetjp_6651_;
}
v_resetjp_6651_:
{
lean_object* v___x_6655_; 
if (v_isShared_6653_ == 0)
{
v___x_6655_ = v___x_6652_;
goto v_reusejp_6654_;
}
else
{
lean_object* v_reuseFailAlloc_6656_; 
v_reuseFailAlloc_6656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6656_, 0, v_a_6650_);
v___x_6655_ = v_reuseFailAlloc_6656_;
goto v_reusejp_6654_;
}
v_reusejp_6654_:
{
return v___x_6655_;
}
}
}
}
else
{
lean_object* v_a_6658_; lean_object* v___x_6660_; uint8_t v_isShared_6661_; uint8_t v_isSharedCheck_6665_; 
lean_dec(v_a_6576_);
lean_dec(v_a_6574_);
lean_dec_ref(v_type_6562_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6658_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6665_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6665_ == 0)
{
v___x_6660_ = v___x_6577_;
v_isShared_6661_ = v_isSharedCheck_6665_;
goto v_resetjp_6659_;
}
else
{
lean_inc(v_a_6658_);
lean_dec(v___x_6577_);
v___x_6660_ = lean_box(0);
v_isShared_6661_ = v_isSharedCheck_6665_;
goto v_resetjp_6659_;
}
v_resetjp_6659_:
{
lean_object* v___x_6663_; 
if (v_isShared_6661_ == 0)
{
v___x_6663_ = v___x_6660_;
goto v_reusejp_6662_;
}
else
{
lean_object* v_reuseFailAlloc_6664_; 
v_reuseFailAlloc_6664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6658_);
v___x_6663_ = v_reuseFailAlloc_6664_;
goto v_reusejp_6662_;
}
v_reusejp_6662_:
{
return v___x_6663_;
}
}
}
}
else
{
lean_object* v_a_6666_; lean_object* v___x_6668_; uint8_t v_isShared_6669_; uint8_t v_isSharedCheck_6673_; 
lean_dec(v_a_6574_);
lean_dec_ref(v_type_6562_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6666_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6673_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6673_ == 0)
{
v___x_6668_ = v___x_6575_;
v_isShared_6669_ = v_isSharedCheck_6673_;
goto v_resetjp_6667_;
}
else
{
lean_inc(v_a_6666_);
lean_dec(v___x_6575_);
v___x_6668_ = lean_box(0);
v_isShared_6669_ = v_isSharedCheck_6673_;
goto v_resetjp_6667_;
}
v_resetjp_6667_:
{
lean_object* v___x_6671_; 
if (v_isShared_6669_ == 0)
{
v___x_6671_ = v___x_6668_;
goto v_reusejp_6670_;
}
else
{
lean_object* v_reuseFailAlloc_6672_; 
v_reuseFailAlloc_6672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6672_, 0, v_a_6666_);
v___x_6671_ = v_reuseFailAlloc_6672_;
goto v_reusejp_6670_;
}
v_reusejp_6670_:
{
return v___x_6671_;
}
}
}
}
else
{
lean_object* v_a_6674_; lean_object* v___x_6676_; uint8_t v_isShared_6677_; uint8_t v_isSharedCheck_6681_; 
lean_dec_ref(v_type_6562_);
lean_dec_ref(v_wfRel_6560_);
lean_dec(v___x_6559_);
v_a_6674_ = lean_ctor_get(v___x_6573_, 0);
v_isSharedCheck_6681_ = !lean_is_exclusive(v___x_6573_);
if (v_isSharedCheck_6681_ == 0)
{
v___x_6676_ = v___x_6573_;
v_isShared_6677_ = v_isSharedCheck_6681_;
goto v_resetjp_6675_;
}
else
{
lean_inc(v_a_6674_);
lean_dec(v___x_6573_);
v___x_6676_ = lean_box(0);
v_isShared_6677_ = v_isSharedCheck_6681_;
goto v_resetjp_6675_;
}
v_resetjp_6675_:
{
lean_object* v___x_6679_; 
if (v_isShared_6677_ == 0)
{
v___x_6679_ = v___x_6676_;
goto v_reusejp_6678_;
}
else
{
lean_object* v_reuseFailAlloc_6680_; 
v_reuseFailAlloc_6680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6680_, 0, v_a_6674_);
v___x_6679_ = v_reuseFailAlloc_6680_;
goto v_reusejp_6678_;
}
v_reusejp_6678_:
{
return v___x_6679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v___x_6682_, lean_object* v___x_6683_, lean_object* v_wfRel_6684_, lean_object* v_x_6685_, lean_object* v_type_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_){
_start:
{
lean_object* v_res_6694_; 
v_res_6694_ = l_Lean_Elab_WF_mkFix___lam__1(v___x_6682_, v___x_6683_, v_wfRel_6684_, v_x_6685_, v_type_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_, v___y_6692_);
lean_dec(v___y_6692_);
lean_dec_ref(v___y_6691_);
lean_dec(v___y_6690_);
lean_dec_ref(v___y_6689_);
lean_dec(v___y_6688_);
lean_dec_ref(v___y_6687_);
lean_dec_ref(v_x_6685_);
lean_dec_ref(v___x_6682_);
return v_res_6694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6695_, lean_object* v___x_6696_, lean_object* v___x_6697_, lean_object* v___f_6698_, lean_object* v_funNames_6699_, lean_object* v_argsPacker_6700_, lean_object* v_decrTactics_6701_, uint8_t v___x_6702_, lean_object* v_fst_6703_, lean_object* v_prefixArgs_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_){
_start:
{
lean_object* v___x_6712_; 
lean_inc_ref(v___x_6696_);
lean_inc_ref(v___x_6695_);
v___x_6712_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6695_, v___x_6696_, v___x_6697_, v___f_6698_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
if (lean_obj_tag(v___x_6712_) == 0)
{
lean_object* v_a_6713_; lean_object* v___x_6714_; 
v_a_6713_ = lean_ctor_get(v___x_6712_, 0);
lean_inc(v_a_6713_);
lean_dec_ref_known(v___x_6712_, 1);
v___x_6714_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6699_, v_argsPacker_6700_, v_decrTactics_6701_, v_a_6713_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
if (lean_obj_tag(v___x_6714_) == 0)
{
lean_object* v_a_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; uint8_t v___x_6720_; uint8_t v___x_6721_; lean_object* v___x_6722_; 
v_a_6715_ = lean_ctor_get(v___x_6714_, 0);
lean_inc(v_a_6715_);
lean_dec_ref_known(v___x_6714_, 1);
v___x_6716_ = lean_unsigned_to_nat(2u);
v___x_6717_ = lean_mk_empty_array_with_capacity(v___x_6716_);
v___x_6718_ = lean_array_push(v___x_6717_, v___x_6695_);
v___x_6719_ = lean_array_push(v___x_6718_, v___x_6696_);
v___x_6720_ = 1;
v___x_6721_ = 1;
v___x_6722_ = l_Lean_Meta_mkLambdaFVars(v___x_6719_, v_a_6715_, v___x_6702_, v___x_6720_, v___x_6702_, v___x_6720_, v___x_6721_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
lean_dec_ref(v___x_6719_);
if (lean_obj_tag(v___x_6722_) == 0)
{
lean_object* v_a_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; 
v_a_6723_ = lean_ctor_get(v___x_6722_, 0);
lean_inc(v_a_6723_);
lean_dec_ref_known(v___x_6722_, 1);
v___x_6724_ = l_Lean_Expr_app___override(v_fst_6703_, v_a_6723_);
v___x_6725_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6704_, v___x_6724_, v___x_6702_, v___x_6720_, v___x_6702_, v___x_6720_, v___x_6721_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
return v___x_6725_;
}
else
{
lean_dec_ref(v_fst_6703_);
return v___x_6722_;
}
}
else
{
lean_dec_ref(v_fst_6703_);
lean_dec_ref(v___x_6696_);
lean_dec_ref(v___x_6695_);
return v___x_6714_;
}
}
else
{
lean_dec_ref(v_fst_6703_);
lean_dec_ref(v_decrTactics_6701_);
lean_dec_ref(v_argsPacker_6700_);
lean_dec_ref(v_funNames_6699_);
lean_dec_ref(v___x_6696_);
lean_dec_ref(v___x_6695_);
return v___x_6712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6726_ = _args[0];
lean_object* v___x_6727_ = _args[1];
lean_object* v___x_6728_ = _args[2];
lean_object* v___f_6729_ = _args[3];
lean_object* v_funNames_6730_ = _args[4];
lean_object* v_argsPacker_6731_ = _args[5];
lean_object* v_decrTactics_6732_ = _args[6];
lean_object* v___x_6733_ = _args[7];
lean_object* v_fst_6734_ = _args[8];
lean_object* v_prefixArgs_6735_ = _args[9];
lean_object* v___y_6736_ = _args[10];
lean_object* v___y_6737_ = _args[11];
lean_object* v___y_6738_ = _args[12];
lean_object* v___y_6739_ = _args[13];
lean_object* v___y_6740_ = _args[14];
lean_object* v___y_6741_ = _args[15];
lean_object* v___y_6742_ = _args[16];
_start:
{
uint8_t v___x_5939__boxed_6743_; lean_object* v_res_6744_; 
v___x_5939__boxed_6743_ = lean_unbox(v___x_6733_);
v_res_6744_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6726_, v___x_6727_, v___x_6728_, v___f_6729_, v_funNames_6730_, v_argsPacker_6731_, v_decrTactics_6732_, v___x_5939__boxed_6743_, v_fst_6734_, v_prefixArgs_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_, v___y_6740_, v___y_6741_);
lean_dec(v___y_6741_);
lean_dec_ref(v___y_6740_);
lean_dec(v___y_6739_);
lean_dec_ref(v___y_6738_);
lean_dec(v___y_6737_);
lean_dec_ref(v___y_6736_);
lean_dec_ref(v_prefixArgs_6735_);
return v_res_6744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6745_, lean_object* v_snd_6746_, lean_object* v___x_6747_, lean_object* v_prefixArgs_6748_, lean_object* v_value_6749_, lean_object* v___f_6750_, lean_object* v_funNames_6751_, lean_object* v_argsPacker_6752_, lean_object* v_decrTactics_6753_, uint8_t v___x_6754_, lean_object* v_fst_6755_, lean_object* v_xs_6756_, lean_object* v_x_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_){
_start:
{
lean_object* v_lctx_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___f_6774_; lean_object* v___x_6775_; 
v_lctx_6765_ = lean_ctor_get(v___y_6760_, 2);
v___x_6766_ = lean_unsigned_to_nat(0u);
v___x_6767_ = lean_array_get_borrowed(v___x_6745_, v_xs_6756_, v___x_6766_);
v___x_6768_ = l_Lean_Expr_fvarId_x21(v___x_6767_);
lean_inc_ref(v_lctx_6765_);
v___x_6769_ = l_Lean_LocalContext_setUserName(v_lctx_6765_, v___x_6768_, v_snd_6746_);
v___x_6770_ = lean_array_get_borrowed(v___x_6745_, v_xs_6756_, v___x_6747_);
lean_inc_n(v___x_6767_, 2);
lean_inc_ref(v_prefixArgs_6748_);
v___x_6771_ = lean_array_push(v_prefixArgs_6748_, v___x_6767_);
v___x_6772_ = l_Lean_Expr_beta(v_value_6749_, v___x_6771_);
v___x_6773_ = lean_box(v___x_6754_);
lean_inc(v___x_6770_);
v___f_6774_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6774_, 0, v___x_6767_);
lean_closure_set(v___f_6774_, 1, v___x_6770_);
lean_closure_set(v___f_6774_, 2, v___x_6772_);
lean_closure_set(v___f_6774_, 3, v___f_6750_);
lean_closure_set(v___f_6774_, 4, v_funNames_6751_);
lean_closure_set(v___f_6774_, 5, v_argsPacker_6752_);
lean_closure_set(v___f_6774_, 6, v_decrTactics_6753_);
lean_closure_set(v___f_6774_, 7, v___x_6773_);
lean_closure_set(v___f_6774_, 8, v_fst_6755_);
lean_closure_set(v___f_6774_, 9, v_prefixArgs_6748_);
v___x_6775_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6769_, v___f_6774_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_);
return v___x_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6776_ = _args[0];
lean_object* v_snd_6777_ = _args[1];
lean_object* v___x_6778_ = _args[2];
lean_object* v_prefixArgs_6779_ = _args[3];
lean_object* v_value_6780_ = _args[4];
lean_object* v___f_6781_ = _args[5];
lean_object* v_funNames_6782_ = _args[6];
lean_object* v_argsPacker_6783_ = _args[7];
lean_object* v_decrTactics_6784_ = _args[8];
lean_object* v___x_6785_ = _args[9];
lean_object* v_fst_6786_ = _args[10];
lean_object* v_xs_6787_ = _args[11];
lean_object* v_x_6788_ = _args[12];
lean_object* v___y_6789_ = _args[13];
lean_object* v___y_6790_ = _args[14];
lean_object* v___y_6791_ = _args[15];
lean_object* v___y_6792_ = _args[16];
lean_object* v___y_6793_ = _args[17];
lean_object* v___y_6794_ = _args[18];
lean_object* v___y_6795_ = _args[19];
_start:
{
uint8_t v___x_6009__boxed_6796_; lean_object* v_res_6797_; 
v___x_6009__boxed_6796_ = lean_unbox(v___x_6785_);
v_res_6797_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6776_, v_snd_6777_, v___x_6778_, v_prefixArgs_6779_, v_value_6780_, v___f_6781_, v_funNames_6782_, v_argsPacker_6783_, v_decrTactics_6784_, v___x_6009__boxed_6796_, v_fst_6786_, v_xs_6787_, v_x_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_);
lean_dec(v___y_6794_);
lean_dec_ref(v___y_6793_);
lean_dec(v___y_6792_);
lean_dec_ref(v___y_6791_);
lean_dec(v___y_6790_);
lean_dec_ref(v___y_6789_);
lean_dec_ref(v_x_6788_);
lean_dec_ref(v_xs_6787_);
lean_dec(v___x_6778_);
lean_dec_ref(v___x_6776_);
return v_res_6797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6802_, lean_object* v_prefixArgs_6803_, lean_object* v_argsPacker_6804_, lean_object* v_wfRel_6805_, lean_object* v_funNames_6806_, lean_object* v_decrTactics_6807_, lean_object* v_a_6808_, lean_object* v_a_6809_, lean_object* v_a_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_){
_start:
{
lean_object* v_declName_6815_; lean_object* v_type_6816_; lean_object* v_value_6817_; lean_object* v___f_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; 
v_declName_6815_ = lean_ctor_get(v_preDef_6802_, 3);
lean_inc(v_declName_6815_);
v_type_6816_ = lean_ctor_get(v_preDef_6802_, 6);
lean_inc_ref(v_type_6816_);
v_value_6817_ = lean_ctor_get(v_preDef_6802_, 7);
lean_inc_ref(v_value_6817_);
lean_dec_ref(v_preDef_6802_);
lean_inc_ref(v_prefixArgs_6803_);
v___f_6818_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 2);
lean_closure_set(v___f_6818_, 0, v_prefixArgs_6803_);
lean_closure_set(v___f_6818_, 1, v_declName_6815_);
v___x_6819_ = l_Lean_instInhabitedExpr;
v___x_6820_ = l_Lean_Meta_instantiateForall(v_type_6816_, v_prefixArgs_6803_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_);
if (lean_obj_tag(v___x_6820_) == 0)
{
lean_object* v_a_6821_; lean_object* v___x_6822_; lean_object* v___f_6823_; lean_object* v___x_6824_; uint8_t v___x_6825_; lean_object* v___x_6826_; 
v_a_6821_ = lean_ctor_get(v___x_6820_, 0);
lean_inc(v_a_6821_);
lean_dec_ref_known(v___x_6820_, 1);
v___x_6822_ = lean_unsigned_to_nat(1u);
v___f_6823_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6823_, 0, v___x_6819_);
lean_closure_set(v___f_6823_, 1, v___x_6822_);
lean_closure_set(v___f_6823_, 2, v_wfRel_6805_);
v___x_6824_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6825_ = 0;
v___x_6826_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6821_, v___x_6824_, v___f_6823_, v___x_6825_, v___x_6825_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_);
if (lean_obj_tag(v___x_6826_) == 0)
{
lean_object* v_a_6827_; lean_object* v_fst_6828_; lean_object* v_snd_6829_; lean_object* v___x_6830_; lean_object* v___f_6831_; lean_object* v___x_6832_; 
v_a_6827_ = lean_ctor_get(v___x_6826_, 0);
lean_inc(v_a_6827_);
lean_dec_ref_known(v___x_6826_, 1);
v_fst_6828_ = lean_ctor_get(v_a_6827_, 0);
lean_inc_n(v_fst_6828_, 2);
v_snd_6829_ = lean_ctor_get(v_a_6827_, 1);
lean_inc(v_snd_6829_);
lean_dec(v_a_6827_);
v___x_6830_ = lean_box(v___x_6825_);
v___f_6831_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6831_, 0, v___x_6819_);
lean_closure_set(v___f_6831_, 1, v_snd_6829_);
lean_closure_set(v___f_6831_, 2, v___x_6822_);
lean_closure_set(v___f_6831_, 3, v_prefixArgs_6803_);
lean_closure_set(v___f_6831_, 4, v_value_6817_);
lean_closure_set(v___f_6831_, 5, v___f_6818_);
lean_closure_set(v___f_6831_, 6, v_funNames_6806_);
lean_closure_set(v___f_6831_, 7, v_argsPacker_6804_);
lean_closure_set(v___f_6831_, 8, v_decrTactics_6807_);
lean_closure_set(v___f_6831_, 9, v___x_6830_);
lean_closure_set(v___f_6831_, 10, v_fst_6828_);
lean_inc(v_a_6813_);
lean_inc_ref(v_a_6812_);
lean_inc(v_a_6811_);
lean_inc_ref(v_a_6810_);
v___x_6832_ = lean_infer_type(v_fst_6828_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_);
if (lean_obj_tag(v___x_6832_) == 0)
{
lean_object* v_a_6833_; lean_object* v___x_6834_; 
v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
lean_inc(v_a_6833_);
lean_dec_ref_known(v___x_6832_, 1);
lean_inc(v_a_6813_);
lean_inc_ref(v_a_6812_);
lean_inc(v_a_6811_);
lean_inc_ref(v_a_6810_);
v___x_6834_ = lean_whnf(v_a_6833_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_);
if (lean_obj_tag(v___x_6834_) == 0)
{
lean_object* v_a_6835_; lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; 
v_a_6835_ = lean_ctor_get(v___x_6834_, 0);
lean_inc(v_a_6835_);
lean_dec_ref_known(v___x_6834_, 1);
v___x_6836_ = l_Lean_Expr_bindingDomain_x21(v_a_6835_);
lean_dec(v_a_6835_);
v___x_6837_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6838_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6836_, v___x_6837_, v___f_6831_, v___x_6825_, v___x_6825_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_);
return v___x_6838_;
}
else
{
lean_dec_ref(v___f_6831_);
return v___x_6834_;
}
}
else
{
lean_dec_ref(v___f_6831_);
return v___x_6832_;
}
}
else
{
lean_object* v_a_6839_; lean_object* v___x_6841_; uint8_t v_isShared_6842_; uint8_t v_isSharedCheck_6846_; 
lean_dec_ref(v___f_6818_);
lean_dec_ref(v_value_6817_);
lean_dec_ref(v_decrTactics_6807_);
lean_dec_ref(v_funNames_6806_);
lean_dec_ref(v_argsPacker_6804_);
lean_dec_ref(v_prefixArgs_6803_);
v_a_6839_ = lean_ctor_get(v___x_6826_, 0);
v_isSharedCheck_6846_ = !lean_is_exclusive(v___x_6826_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6841_ = v___x_6826_;
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
else
{
lean_inc(v_a_6839_);
lean_dec(v___x_6826_);
v___x_6841_ = lean_box(0);
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
v_resetjp_6840_:
{
lean_object* v___x_6844_; 
if (v_isShared_6842_ == 0)
{
v___x_6844_ = v___x_6841_;
goto v_reusejp_6843_;
}
else
{
lean_object* v_reuseFailAlloc_6845_; 
v_reuseFailAlloc_6845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6845_, 0, v_a_6839_);
v___x_6844_ = v_reuseFailAlloc_6845_;
goto v_reusejp_6843_;
}
v_reusejp_6843_:
{
return v___x_6844_;
}
}
}
}
else
{
lean_dec_ref(v___f_6818_);
lean_dec_ref(v_value_6817_);
lean_dec_ref(v_decrTactics_6807_);
lean_dec_ref(v_funNames_6806_);
lean_dec_ref(v_wfRel_6805_);
lean_dec_ref(v_argsPacker_6804_);
lean_dec_ref(v_prefixArgs_6803_);
return v___x_6820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6847_, lean_object* v_prefixArgs_6848_, lean_object* v_argsPacker_6849_, lean_object* v_wfRel_6850_, lean_object* v_funNames_6851_, lean_object* v_decrTactics_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_, lean_object* v_a_6859_){
_start:
{
lean_object* v_res_6860_; 
v_res_6860_ = l_Lean_Elab_WF_mkFix(v_preDef_6847_, v_prefixArgs_6848_, v_argsPacker_6849_, v_wfRel_6850_, v_funNames_6851_, v_decrTactics_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_, v_a_6857_, v_a_6858_);
lean_dec(v_a_6858_);
lean_dec_ref(v_a_6857_);
lean_dec(v_a_6856_);
lean_dec_ref(v_a_6855_);
lean_dec(v_a_6854_);
lean_dec_ref(v_a_6853_);
return v_res_6860_;
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
