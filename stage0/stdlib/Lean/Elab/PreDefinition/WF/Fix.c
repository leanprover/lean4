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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27;
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__20));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__22));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__24));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__26));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_716_, lean_object* v_declHint_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_env_722_; uint8_t v___x_723_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_st_ref_get(v___y_718_);
v_env_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_env_722_);
lean_dec(v___x_721_);
v___x_723_ = l_Lean_Name_isAnonymous(v_declHint_717_);
if (v___x_723_ == 0)
{
uint8_t v_isExporting_724_; 
v_isExporting_724_ = lean_ctor_get_uint8(v_env_722_, sizeof(void*)*13);
if (v_isExporting_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v_env_722_);
lean_dec(v_declHint_717_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_msg_716_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
lean_inc_ref(v_env_722_);
v___x_726_ = l_Lean_Environment_setExporting(v_env_722_, v___x_723_);
lean_inc(v_declHint_717_);
lean_inc_ref(v___x_726_);
v___x_727_ = l_Lean_Environment_contains(v___x_726_, v_declHint_717_, v_isExporting_724_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec_ref(v___x_726_);
lean_dec_ref(v_env_722_);
lean_dec(v_declHint_717_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_msg_716_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_c_734_; lean_object* v___x_735_; 
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_731_ = l_Lean_Options_empty;
v___x_732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_732_, 0, v___x_726_);
lean_ctor_set(v___x_732_, 1, v___x_729_);
lean_ctor_set(v___x_732_, 2, v___x_730_);
lean_ctor_set(v___x_732_, 3, v___x_731_);
lean_inc(v_declHint_717_);
v___x_733_ = l_Lean_MessageData_ofConstName(v_declHint_717_, v___x_723_);
v_c_734_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_734_, 0, v___x_732_);
lean_ctor_set(v_c_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_722_, v_declHint_717_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_env_722_);
lean_dec(v_declHint_717_);
v___x_736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v_c_734_);
v___x_738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_MessageData_note(v___x_739_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v_msg_716_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_799_; 
v_val_743_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_799_ == 0)
{
v___x_745_ = v___x_735_;
v_isShared_746_ = v_isSharedCheck_799_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v___x_735_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_799_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v_modules_748_; lean_object* v_moduleNames_749_; lean_object* v_mod_750_; uint8_t v___y_752_; uint8_t v___x_782_; 
v___x_747_ = l_Lean_Environment_header(v_env_722_);
lean_dec_ref(v_env_722_);
v_modules_748_ = lean_ctor_get(v___x_747_, 3);
lean_inc_ref(v_modules_748_);
v_moduleNames_749_ = lean_ctor_get(v___x_747_, 4);
lean_inc_ref(v_moduleNames_749_);
lean_dec_ref(v___x_747_);
v_mod_750_ = lean_array_get(v___x_720_, v_moduleNames_749_, v_val_743_);
lean_dec_ref(v_moduleNames_749_);
v___x_782_ = l_Lean_isPrivateName(v_declHint_717_);
lean_dec(v_declHint_717_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_modules_748_);
v___x_784_ = lean_nat_dec_lt(v_val_743_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v_modules_748_);
lean_dec(v_val_743_);
v___y_752_ = v___x_782_;
goto v___jp_751_;
}
else
{
lean_object* v___x_785_; lean_object* v_toImport_786_; uint8_t v_isExported_787_; 
v___x_785_ = lean_array_fget(v_modules_748_, v_val_743_);
lean_dec(v_val_743_);
lean_dec_ref(v_modules_748_);
v_toImport_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_ref(v_toImport_786_);
lean_dec(v___x_785_);
v_isExported_787_ = lean_ctor_get_uint8(v_toImport_786_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_786_);
v___y_752_ = v_isExported_787_;
goto v___jp_751_;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_modules_748_);
lean_del_object(v___x_745_);
lean_dec(v_val_743_);
v___x_788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_c_734_);
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__25);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_MessageData_ofName(v_mod_750_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__27);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_MessageData_note(v___x_795_);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v_msg_716_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_c_734_);
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_MessageData_ofName(v_mod_750_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_MessageData_note(v___x_760_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v_msg_716_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 0);
lean_ctor_set(v___x_745_, 0, v___x_762_);
v___x_764_ = v___x_745_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_c_734_);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofName(v_mod_750_);
lean_inc_ref(v___x_770_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__21);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_770_);
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__23);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_MessageData_note(v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v_msg_716_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 0);
lean_ctor_set(v___x_745_, 0, v___x_778_);
v___x_780_ = v___x_745_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
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
lean_object* v___x_800_; 
lean_dec_ref(v_env_722_);
lean_dec(v_declHint_717_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_msg_716_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_801_, lean_object* v_declHint_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_801_, v_declHint_802_, v___y_803_);
lean_dec(v___y_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_806_, lean_object* v_declHint_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_827_; 
v___x_817_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_806_, v_declHint_807_, v___y_815_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_827_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = l_Lean_unknownIdentifierMessageTag;
v___x_823_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_828_, lean_object* v_declHint_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_828_, v_declHint_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_toCold_851_; lean_object* v_currRecDepth_852_; lean_object* v_ref_853_; uint16_t v_optionFlags_854_; uint8_t v_suppressElabErrors_855_; uint8_t v_isRecordingDeps_856_; lean_object* v_ref_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_toCold_851_ = lean_ctor_get(v___y_848_, 0);
v_currRecDepth_852_ = lean_ctor_get(v___y_848_, 1);
v_ref_853_ = lean_ctor_get(v___y_848_, 2);
v_optionFlags_854_ = lean_ctor_get_uint16(v___y_848_, sizeof(void*)*3);
v_suppressElabErrors_855_ = lean_ctor_get_uint8(v___y_848_, sizeof(void*)*3 + 2);
v_isRecordingDeps_856_ = lean_ctor_get_uint8(v___y_848_, sizeof(void*)*3 + 3);
v_ref_857_ = l_Lean_replaceRef(v_ref_840_, v_ref_853_);
lean_inc(v_currRecDepth_852_);
lean_inc_ref(v_toCold_851_);
v___x_858_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_858_, 0, v_toCold_851_);
lean_ctor_set(v___x_858_, 1, v_currRecDepth_852_);
lean_ctor_set(v___x_858_, 2, v_ref_857_);
lean_ctor_set_uint16(v___x_858_, sizeof(void*)*3, v_optionFlags_854_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*3 + 2, v_suppressElabErrors_855_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*3 + 3, v_isRecordingDeps_856_);
v___x_859_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_841_, v___y_846_, v___y_847_, v___x_858_, v___y_849_);
lean_dec_ref_known(v___x_858_, 3);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_860_, lean_object* v_msg_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_860_, v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v_ref_860_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_872_, lean_object* v_msg_873_, lean_object* v_declHint_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_873_, v_declHint_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_872_, v_a_885_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_887_, lean_object* v_msg_888_, lean_object* v_declHint_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_887_, v_msg_888_, v_declHint_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec(v___y_890_);
lean_dec(v_ref_887_);
return v_res_899_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_906_, lean_object* v_constName_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_918_ = 0;
lean_inc(v_constName_907_);
v___x_919_ = l_Lean_MessageData_ofConstName(v_constName_907_, v___x_918_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_917_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_906_, v___x_922_, v_constName_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_924_, lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_924_, v_constName_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v_ref_924_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_ref_946_; lean_object* v___x_947_; 
v_ref_946_ = lean_ctor_get(v___y_943_, 2);
v___x_947_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_946_, v_constName_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_env_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v___x_969_ = lean_st_ref_get(v___y_967_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = 0;
lean_inc(v_constName_959_);
v___x_972_ = l_Lean_Environment_find_x3f(v_env_970_, v_constName_959_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_973_;
}
else
{
lean_object* v_val_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_constName_959_);
v_val_974_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_972_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_val_974_);
lean_dec(v___x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 0);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec(v___y_983_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_env_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = lean_st_ref_get(v___y_994_);
v_env_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc_ref(v_env_997_);
lean_dec(v___x_996_);
v___x_998_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_997_, v_declName_993_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1000_, v___y_1001_);
lean_dec(v___y_1001_);
return v_res_1003_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_instMonadEIO___redArg();
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_toApplicative_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1116_; 
v___x_1021_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_1022_ = l_StateRefT_x27_instMonad___redArg(v___x_1021_);
v_toApplicative_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___x_1022_, 1);
lean_dec(v_unused_1117_);
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1116_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_toApplicative_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1116_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_toFunctor_1027_; lean_object* v_toSeq_1028_; lean_object* v_toSeqLeft_1029_; lean_object* v_toSeqRight_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1114_; 
v_toFunctor_1027_ = lean_ctor_get(v_toApplicative_1023_, 0);
v_toSeq_1028_ = lean_ctor_get(v_toApplicative_1023_, 2);
v_toSeqLeft_1029_ = lean_ctor_get(v_toApplicative_1023_, 3);
v_toSeqRight_1030_ = lean_ctor_get(v_toApplicative_1023_, 4);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_toApplicative_1023_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v_toApplicative_1023_, 1);
lean_dec(v_unused_1115_);
v___x_1032_ = v_toApplicative_1023_;
v_isShared_1033_ = v_isSharedCheck_1114_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_toSeqRight_1030_);
lean_inc(v_toSeqLeft_1029_);
lean_inc(v_toSeq_1028_);
lean_inc(v_toFunctor_1027_);
lean_dec(v_toApplicative_1023_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1114_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1043_; 
v___f_1034_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1035_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1027_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toFunctor_1027_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toFunctor_1027_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___f_1036_);
lean_ctor_set(v___x_1038_, 1, v___f_1037_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeqRight_1030_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeqLeft_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeq_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v___f_1039_);
lean_ctor_set(v___x_1032_, 3, v___f_1040_);
lean_ctor_set(v___x_1032_, 2, v___f_1041_);
lean_ctor_set(v___x_1032_, 1, v___f_1034_);
lean_ctor_set(v___x_1032_, 0, v___x_1038_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___f_1034_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v___f_1039_);
v___x_1043_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___f_1035_);
lean_ctor_set(v___x_1025_, 0, v___x_1043_);
v___x_1045_ = v___x_1025_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___f_1035_);
v___x_1045_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v_toApplicative_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1110_; 
v___x_1046_ = l_StateRefT_x27_instMonad___redArg(v___x_1045_);
v_toApplicative_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v___x_1046_, 1);
lean_dec(v_unused_1111_);
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1110_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_toApplicative_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1110_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_toFunctor_1051_; lean_object* v_toSeq_1052_; lean_object* v_toSeqLeft_1053_; lean_object* v_toSeqRight_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1108_; 
v_toFunctor_1051_ = lean_ctor_get(v_toApplicative_1047_, 0);
v_toSeq_1052_ = lean_ctor_get(v_toApplicative_1047_, 2);
v_toSeqLeft_1053_ = lean_ctor_get(v_toApplicative_1047_, 3);
v_toSeqRight_1054_ = lean_ctor_get(v_toApplicative_1047_, 4);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_toApplicative_1047_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v_toApplicative_1047_, 1);
lean_dec(v_unused_1109_);
v___x_1056_ = v_toApplicative_1047_;
v_isShared_1057_ = v_isSharedCheck_1108_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_toSeqRight_1054_);
lean_inc(v_toSeqLeft_1053_);
lean_inc(v_toSeq_1052_);
lean_inc(v_toFunctor_1051_);
lean_dec(v_toApplicative_1047_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1108_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___x_1067_; 
v___f_1058_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1059_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1051_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toFunctor_1051_);
v___f_1061_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1061_, 0, v_toFunctor_1051_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___f_1060_);
lean_ctor_set(v___x_1062_, 1, v___f_1061_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toSeqRight_1054_);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1064_, 0, v_toSeqLeft_1053_);
v___f_1065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1065_, 0, v_toSeq_1052_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___f_1063_);
lean_ctor_set(v___x_1056_, 3, v___f_1064_);
lean_ctor_set(v___x_1056_, 2, v___f_1065_);
lean_ctor_set(v___x_1056_, 1, v___f_1058_);
lean_ctor_set(v___x_1056_, 0, v___x_1062_);
v___x_1067_ = v___x_1056_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___f_1058_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v___f_1065_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___f_1063_);
v___x_1067_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___f_1059_);
lean_ctor_set(v___x_1049_, 0, v___x_1067_);
v___x_1069_ = v___x_1049_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___f_1059_);
v___x_1069_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v_toApplicative_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1104_; 
v___x_1070_ = l_StateRefT_x27_instMonad___redArg(v___x_1069_);
v_toApplicative_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v___x_1070_, 1);
lean_dec(v_unused_1105_);
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1104_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_toApplicative_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1104_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_toFunctor_1075_; lean_object* v_toSeq_1076_; lean_object* v_toSeqLeft_1077_; lean_object* v_toSeqRight_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1102_; 
v_toFunctor_1075_ = lean_ctor_get(v_toApplicative_1071_, 0);
v_toSeq_1076_ = lean_ctor_get(v_toApplicative_1071_, 2);
v_toSeqLeft_1077_ = lean_ctor_get(v_toApplicative_1071_, 3);
v_toSeqRight_1078_ = lean_ctor_get(v_toApplicative_1071_, 4);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_toApplicative_1071_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v_toApplicative_1071_, 1);
lean_dec(v_unused_1103_);
v___x_1080_ = v_toApplicative_1071_;
v_isShared_1081_ = v_isSharedCheck_1102_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_toSeqRight_1078_);
lean_inc(v_toSeqLeft_1077_);
lean_inc(v_toSeq_1076_);
lean_inc(v_toFunctor_1075_);
lean_dec(v_toApplicative_1071_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1102_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1091_; 
v___f_1082_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1083_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1075_);
v___f_1084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1084_, 0, v_toFunctor_1075_);
v___f_1085_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1085_, 0, v_toFunctor_1075_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___f_1084_);
lean_ctor_set(v___x_1086_, 1, v___f_1085_);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1087_, 0, v_toSeqRight_1078_);
v___f_1088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1088_, 0, v_toSeqLeft_1077_);
v___f_1089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1089_, 0, v_toSeq_1076_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 4, v___f_1087_);
lean_ctor_set(v___x_1080_, 3, v___f_1088_);
lean_ctor_set(v___x_1080_, 2, v___f_1089_);
lean_ctor_set(v___x_1080_, 1, v___f_1082_);
lean_ctor_set(v___x_1080_, 0, v___x_1086_);
v___x_1091_ = v___x_1080_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___f_1082_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___f_1089_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v___f_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v___f_1087_);
v___x_1091_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___f_1083_);
lean_ctor_set(v___x_1073_, 0, v___x_1091_);
v___x_1093_ = v___x_1073_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___f_1083_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_49416__overap_1098_; lean_object* v___x_1099_; 
v___x_1094_ = l_StateRefT_x27_instMonad___redArg(v___x_1093_);
v___x_1095_ = l_StateRefT_x27_instMonad___redArg(v___x_1094_);
v___x_1096_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1097_ = l_instInhabitedOfMonad___redArg(v___x_1095_, v___x_1096_);
v___x_49416__overap_1098_ = lean_panic_fn_borrowed(v___x_1097_, v_msg_1011_);
lean_dec(v___x_1097_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc(v___y_1012_);
v___x_1099_ = lean_apply_9(v___x_49416__overap_1098_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, lean_box(0));
return v___x_1099_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
return v_res_1128_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1133_ = lean_unsigned_to_nat(53u);
v___x_1134_ = lean_unsigned_to_nat(62u);
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1137_ = l_mkPanicMessageWithDecl(v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_bs_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_bs_1140_);
return v___x_1151_;
}
else
{
lean_object* v_v_1152_; lean_object* v___x_1153_; lean_object* v_bs_x27_1154_; lean_object* v_a_1156_; lean_object* v___x_1161_; 
v_v_1152_ = lean_array_uget(v_bs_1140_, v_i_1139_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v_bs_x27_1154_ = lean_array_uset(v_bs_1140_, v_i_1139_, v___x_1153_);
v___x_1161_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1152_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
if (lean_obj_tag(v_a_1162_) == 6)
{
lean_object* v_val_1163_; lean_object* v_numFields_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v_val_1163_ = lean_ctor_get(v_a_1162_, 0);
lean_inc_ref(v_val_1163_);
lean_dec_ref_known(v_a_1162_, 1);
v_numFields_1164_ = lean_ctor_get(v_val_1163_, 4);
lean_inc(v_numFields_1164_);
lean_dec_ref(v_val_1163_);
v___x_1165_ = 0;
v___x_1166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1166_, 0, v_numFields_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1153_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*2, v___x_1165_);
v_a_1156_ = v___x_1166_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_a_1162_);
v___x_1167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1168_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1167_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_a_1156_ = v_a_1169_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_bs_x27_1154_);
v_a_1170_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_bs_x27_1154_);
v_a_1178_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1161_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1161_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
v___jp_1155_:
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1139_, v___x_1157_);
v___x_1159_ = lean_array_uset(v_bs_x27_1154_, v_i_1139_, v_a_1156_);
v_i_1139_ = v___x_1158_;
v_bs_1140_ = v___x_1159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_bs_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
size_t v_sz_boxed_1198_; size_t v_i_boxed_1199_; lean_object* v_res_1200_; 
v_sz_boxed_1198_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1198_, v_i_boxed_1199_, v_bs_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1200_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1201_; lean_object* v_dummy_1202_; 
v___x_1201_ = lean_box(0);
v_dummy_1202_ = l_Lean_Expr_sort___override(v___x_1201_);
return v_dummy_1202_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_unsigned_to_nat(16u);
v___x_1205_ = lean_mk_array(v___x_1204_, v___x_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1211_, uint8_t v_alsoCasesOn_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Lean_Expr_isApp(v_e_1211_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_e_1211_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Expr_getAppFn(v_e_1211_);
if (lean_obj_tag(v___x_1228_) == 4)
{
lean_object* v_declName_1229_; lean_object* v_us_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1385_; 
v_declName_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_n(v_declName_1229_, 2);
v_us_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_us_1230_);
lean_dec_ref_known(v___x_1228_, 2);
v___x_1231_ = l_Lean_instInhabitedExpr;
v___x_1232_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1229_, v___y_1220_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1385_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1385_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 1)
{
lean_object* v_val_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1278_; 
v_val_1237_ = lean_ctor_get(v_a_1233_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1239_ = v_a_1233_;
v_isShared_1240_ = v_isSharedCheck_1278_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_val_1237_);
lean_dec(v_a_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1278_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_dummy_1241_; lean_object* v_nargs_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_args_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_dummy_1241_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1242_ = l_Lean_Expr_getAppNumArgs(v_e_1211_);
lean_inc(v_nargs_1242_);
v___x_1243_ = lean_mk_array(v_nargs_1242_, v_dummy_1241_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_sub(v_nargs_1242_, v___x_1244_);
lean_dec(v_nargs_1242_);
v_args_1246_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1211_, v___x_1243_, v___x_1245_);
v___x_1247_ = lean_array_get_size(v_args_1246_);
v___x_1248_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1237_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
lean_dec(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v_numParams_1250_; lean_object* v_numDiscrs_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v_numParams_1250_ = lean_ctor_get(v_val_1237_, 0);
v_numDiscrs_1251_ = lean_ctor_get(v_val_1237_, 1);
v___x_1252_ = lean_array_mk(v_us_1230_);
v___x_1253_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1250_);
v___x_1254_ = l_Array_extract___redArg(v_args_1246_, v___x_1253_, v_numParams_1250_);
v___x_1255_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1237_);
v___x_1256_ = lean_array_get(v___x_1231_, v_args_1246_, v___x_1255_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_nat_add(v_numParams_1250_, v___x_1244_);
v___x_1258_ = lean_nat_add(v___x_1257_, v_numDiscrs_1251_);
lean_inc(v___x_1258_);
lean_inc_ref_n(v_args_1246_, 2);
v___x_1259_ = l_Array_toSubarray___redArg(v_args_1246_, v___x_1257_, v___x_1258_);
v___x_1260_ = l_Subarray_copy___redArg(v___x_1259_);
v___x_1261_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1237_);
v___x_1262_ = lean_nat_add(v___x_1258_, v___x_1261_);
lean_dec(v___x_1261_);
lean_inc(v___x_1262_);
v___x_1263_ = l_Array_toSubarray___redArg(v_args_1246_, v___x_1258_, v___x_1262_);
v___x_1264_ = l_Subarray_copy___redArg(v___x_1263_);
v___x_1265_ = l_Array_toSubarray___redArg(v_args_1246_, v___x_1262_, v___x_1247_);
v___x_1266_ = l_Subarray_copy___redArg(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1267_, 0, v_val_1237_);
lean_ctor_set(v___x_1267_, 1, v_declName_1229_);
lean_ctor_set(v___x_1267_, 2, v___x_1252_);
lean_ctor_set(v___x_1267_, 3, v___x_1254_);
lean_ctor_set(v___x_1267_, 4, v___x_1256_);
lean_ctor_set(v___x_1267_, 5, v___x_1260_);
lean_ctor_set(v___x_1267_, 6, v___x_1264_);
lean_ctor_set(v___x_1267_, 7, v___x_1266_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1267_);
v___x_1269_ = v___x_1239_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1269_);
v___x_1271_ = v___x_1235_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_dec_ref(v_args_1246_);
lean_del_object(v___x_1239_);
lean_dec(v_val_1237_);
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
v___x_1274_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1274_);
v___x_1276_ = v___x_1235_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1279_; 
lean_del_object(v___x_1235_);
lean_dec(v_a_1233_);
v___x_1279_ = lean_st_ref_get(v___y_1220_);
if (v_alsoCasesOn_1212_ == 0)
{
lean_dec(v___x_1279_);
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
lean_dec_ref(v_e_1211_);
goto v___jp_1222_;
}
else
{
lean_object* v_env_1280_; uint8_t v___x_1281_; 
v_env_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref(v_env_1280_);
lean_dec(v___x_1279_);
lean_inc(v_declName_1229_);
v___x_1281_ = l_Lean_isCasesOnRecursor(v_env_1280_, v_declName_1229_);
if (v___x_1281_ == 0)
{
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
lean_dec_ref(v_e_1211_);
goto v___jp_1222_;
}
else
{
lean_object* v_indName_1282_; lean_object* v___x_1283_; 
v_indName_1282_ = l_Lean_Name_getPrefix(v_declName_1229_);
v___x_1283_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1282_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1376_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1376_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1376_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
if (lean_obj_tag(v_a_1284_) == 5)
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1371_; 
v_val_1288_ = lean_ctor_get(v_a_1284_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1290_ = v_a_1284_;
v_isShared_1291_ = v_isSharedCheck_1371_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v_a_1284_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1371_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_toConstantVal_1292_; lean_object* v_numParams_1293_; lean_object* v_numIndices_1294_; lean_object* v_ctors_1295_; lean_object* v_nargs_1296_; lean_object* v_dummy_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_args_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_toConstantVal_1292_ = lean_ctor_get(v_val_1288_, 0);
lean_inc_ref(v_toConstantVal_1292_);
v_numParams_1293_ = lean_ctor_get(v_val_1288_, 1);
lean_inc(v_numParams_1293_);
v_numIndices_1294_ = lean_ctor_get(v_val_1288_, 2);
lean_inc(v_numIndices_1294_);
v_ctors_1295_ = lean_ctor_get(v_val_1288_, 4);
lean_inc(v_ctors_1295_);
v_nargs_1296_ = l_Lean_Expr_getAppNumArgs(v_e_1211_);
v_dummy_1297_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1296_);
v___x_1298_ = lean_mk_array(v_nargs_1296_, v_dummy_1297_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_sub(v_nargs_1296_, v___x_1299_);
lean_dec(v_nargs_1296_);
v_args_1301_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1211_, v___x_1298_, v___x_1300_);
v___x_1302_ = lean_nat_add(v_numParams_1293_, v___x_1299_);
v___x_1303_ = lean_nat_add(v___x_1302_, v_numIndices_1294_);
v___x_1304_ = lean_nat_add(v___x_1303_, v___x_1299_);
lean_dec(v___x_1303_);
v___x_1305_ = l_Lean_InductiveVal_numCtors(v_val_1288_);
lean_dec_ref(v_val_1288_);
v___x_1306_ = lean_nat_add(v___x_1304_, v___x_1305_);
lean_dec(v___x_1305_);
v___x_1307_ = lean_array_get_size(v_args_1301_);
v___x_1308_ = lean_nat_dec_le(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v___x_1306_);
lean_dec(v___x_1304_);
lean_dec(v___x_1302_);
lean_dec_ref(v_args_1301_);
lean_dec(v_ctors_1295_);
lean_dec(v_numIndices_1294_);
lean_dec(v_numParams_1293_);
lean_dec_ref(v_toConstantVal_1292_);
lean_del_object(v___x_1290_);
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
v___x_1309_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1309_);
v___x_1311_ = v___x_1286_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v___x_1313_; lean_object* v_params_1314_; lean_object* v_motive_1315_; lean_object* v_discrs_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_discrInfos_1319_; lean_object* v_alts_1320_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v_lower_1362_; lean_object* v_upper_1363_; uint8_t v___x_1370_; 
lean_del_object(v___x_1286_);
v___x_1313_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1293_);
lean_inc_ref_n(v_args_1301_, 3);
v_params_1314_ = l_Array_toSubarray___redArg(v_args_1301_, v___x_1313_, v_numParams_1293_);
v_motive_1315_ = lean_array_get(v___x_1231_, v_args_1301_, v_numParams_1293_);
lean_dec(v_numParams_1293_);
lean_inc(v___x_1304_);
v_discrs_1316_ = l_Array_toSubarray___redArg(v_args_1301_, v___x_1302_, v___x_1304_);
v___x_1317_ = lean_nat_add(v_numIndices_1294_, v___x_1299_);
lean_dec(v_numIndices_1294_);
v___x_1318_ = lean_box(0);
v_discrInfos_1319_ = lean_mk_array(v___x_1317_, v___x_1318_);
lean_inc(v___x_1306_);
v_alts_1320_ = l_Array_toSubarray___redArg(v_args_1301_, v___x_1304_, v___x_1306_);
v___x_1370_ = lean_nat_dec_le(v___x_1306_, v___x_1313_);
if (v___x_1370_ == 0)
{
v_lower_1362_ = v___x_1306_;
v_upper_1363_ = v___x_1307_;
goto v___jp_1361_;
}
else
{
lean_dec(v___x_1306_);
v_lower_1362_ = v___x_1313_;
v_upper_1363_ = v___x_1307_;
goto v___jp_1361_;
}
v___jp_1321_:
{
lean_object* v___x_1324_; size_t v_sz_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_array_mk(v_ctors_1295_);
v_sz_1325_ = lean_array_size(v___x_1324_);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1325_, v___x_1326_, v___x_1324_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1352_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v_start_1332_; lean_object* v_stop_1333_; lean_object* v_start_1334_; lean_object* v_stop_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_start_1332_ = lean_ctor_get(v_params_1314_, 1);
v_stop_1333_ = lean_ctor_get(v_params_1314_, 2);
v_start_1334_ = lean_ctor_get(v_discrs_1316_, 1);
v_stop_1335_ = lean_ctor_get(v_discrs_1316_, 2);
v___x_1336_ = lean_nat_sub(v_stop_1333_, v_start_1332_);
v___x_1337_ = lean_nat_sub(v_stop_1335_, v_start_1334_);
v___x_1338_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1339_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1336_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set(v___x_1339_, 2, v_a_1328_);
lean_ctor_set(v___x_1339_, 3, v___y_1323_);
lean_ctor_set(v___x_1339_, 4, v_discrInfos_1319_);
lean_ctor_set(v___x_1339_, 5, v___x_1338_);
v___x_1340_ = lean_array_mk(v_us_1230_);
v___x_1341_ = l_Subarray_copy___redArg(v_params_1314_);
v___x_1342_ = l_Subarray_copy___redArg(v_discrs_1316_);
v___x_1343_ = l_Subarray_copy___redArg(v_alts_1320_);
v___x_1344_ = l_Subarray_copy___redArg(v___y_1322_);
v___x_1345_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1339_);
lean_ctor_set(v___x_1345_, 1, v_declName_1229_);
lean_ctor_set(v___x_1345_, 2, v___x_1340_);
lean_ctor_set(v___x_1345_, 3, v___x_1341_);
lean_ctor_set(v___x_1345_, 4, v_motive_1315_);
lean_ctor_set(v___x_1345_, 5, v___x_1342_);
lean_ctor_set(v___x_1345_, 6, v___x_1343_);
lean_ctor_set(v___x_1345_, 7, v___x_1344_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 1);
lean_ctor_set(v___x_1290_, 0, v___x_1345_);
v___x_1347_ = v___x_1290_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1347_);
v___x_1349_ = v___x_1330_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v_alts_1320_);
lean_dec_ref(v_discrInfos_1319_);
lean_dec_ref(v_discrs_1316_);
lean_dec(v_motive_1315_);
lean_dec_ref(v_params_1314_);
lean_del_object(v___x_1290_);
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
v_a_1353_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1327_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1327_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
v___jp_1361_:
{
lean_object* v_levelParams_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_levelParams_1364_ = lean_ctor_get(v_toConstantVal_1292_, 1);
lean_inc(v_levelParams_1364_);
lean_dec_ref(v_toConstantVal_1292_);
v___x_1365_ = l_Array_toSubarray___redArg(v_args_1301_, v_lower_1362_, v_upper_1363_);
v___x_1366_ = l_List_lengthTR___redArg(v_levelParams_1364_);
lean_dec(v_levelParams_1364_);
v___x_1367_ = l_List_lengthTR___redArg(v_us_1230_);
v___x_1368_ = lean_nat_dec_eq(v___x_1366_, v___x_1367_);
lean_dec(v___x_1367_);
lean_dec(v___x_1366_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1322_ = v___x_1365_;
v___y_1323_ = v___x_1369_;
goto v___jp_1321_;
}
else
{
v___y_1322_ = v___x_1365_;
v___y_1323_ = v___x_1318_;
goto v___jp_1321_;
}
}
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec(v_a_1284_);
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
lean_dec_ref(v_e_1211_);
v___x_1372_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1372_);
v___x_1374_ = v___x_1286_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_us_1230_);
lean_dec(v_declName_1229_);
lean_dec_ref(v_e_1211_);
v_a_1377_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1283_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1283_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
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
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_e_1211_);
goto v___jp_1222_;
}
}
v___jp_1222_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1386_, lean_object* v_alsoCasesOn_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1397_; lean_object* v_res_1398_; 
v_alsoCasesOn_boxed_1397_ = lean_unbox(v_alsoCasesOn_1387_);
v_res_1398_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1386_, v_alsoCasesOn_boxed_1397_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v_b_1404_, lean_object* v_c_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc(v___y_1400_);
v___x_1411_ = lean_apply_11(v_k_1399_, v_b_1404_, v_c_1405_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, lean_box(0));
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v_b_1417_, lean_object* v_c_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v_b_1417_, v_c_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec(v___y_1413_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1425_, lean_object* v_maxFVars_1426_, lean_object* v_k_1427_, uint8_t v_cleanupAnnotations_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___f_1438_; uint8_t v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v___y_1430_);
lean_inc(v___y_1429_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1438_, 0, v_k_1427_);
lean_closure_set(v___f_1438_, 1, v___y_1429_);
lean_closure_set(v___f_1438_, 2, v___y_1430_);
lean_closure_set(v___f_1438_, 3, v___y_1431_);
lean_closure_set(v___f_1438_, 4, v___y_1432_);
v___x_1439_ = 1;
v___x_1440_ = 0;
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_maxFVars_1426_);
v___x_1442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1425_, v___x_1439_, v___x_1440_, v___x_1439_, v___x_1440_, v___x_1441_, v___f_1438_, v_cleanupAnnotations_1428_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec_ref_known(v___x_1441_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1451_, lean_object* v_maxFVars_1452_, lean_object* v_k_1453_, lean_object* v_cleanupAnnotations_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1464_; lean_object* v_res_1465_; 
v_cleanupAnnotations_boxed_1464_ = lean_unbox(v_cleanupAnnotations_1454_);
v_res_1465_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1451_, v_maxFVars_1452_, v_k_1453_, v_cleanupAnnotations_boxed_1464_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec(v___y_1455_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc(v___y_1467_);
v___x_1477_ = lean_apply_10(v_k_1466_, v_b_1471_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, lean_box(0));
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v_b_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1479_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1490_, lean_object* v_type_1491_, lean_object* v_val_1492_, lean_object* v_k_1493_, uint8_t v_nondep_1494_, uint8_t v_kind_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___f_1505_; lean_object* v___x_1506_; 
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc(v___y_1496_);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1505_, 0, v_k_1493_);
lean_closure_set(v___f_1505_, 1, v___y_1496_);
lean_closure_set(v___f_1505_, 2, v___y_1497_);
lean_closure_set(v___f_1505_, 3, v___y_1498_);
lean_closure_set(v___f_1505_, 4, v___y_1499_);
v___x_1506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1490_, v_type_1491_, v_val_1492_, v___f_1505_, v_nondep_1494_, v_kind_1495_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
return v___x_1506_;
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1515_, lean_object* v_type_1516_, lean_object* v_val_1517_, lean_object* v_k_1518_, lean_object* v_nondep_1519_, lean_object* v_kind_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v_nondep_boxed_1530_; uint8_t v_kind_boxed_1531_; lean_object* v_res_1532_; 
v_nondep_boxed_1530_ = lean_unbox(v_nondep_1519_);
v_kind_boxed_1531_ = lean_unbox(v_kind_1520_);
v_res_1532_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1515_, v_type_1516_, v_val_1517_, v_k_1518_, v_nondep_boxed_1530_, v_kind_boxed_1531_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec(v___y_1521_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1533_, uint8_t v_usedLetOnly_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v_x_1535_);
v___x_1545_ = lean_apply_10(v_k_1533_, v_x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
v___x_1549_ = lean_array_push(v___x_1548_, v_x_1535_);
v___x_1550_ = 0;
v___x_1551_ = 1;
v___x_1552_ = l_Lean_Meta_mkLetFVars(v___x_1549_, v_a_1546_, v_usedLetOnly_1534_, v___x_1550_, v___x_1551_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v___x_1549_);
return v___x_1552_;
}
else
{
lean_dec_ref(v_x_1535_);
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1553_, lean_object* v_usedLetOnly_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_usedLetOnly_boxed_1565_; lean_object* v_res_1566_; 
v_usedLetOnly_boxed_1565_ = lean_unbox(v_usedLetOnly_1554_);
v_res_1566_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1553_, v_usedLetOnly_boxed_1565_, v_x_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1567_, lean_object* v_type_1568_, lean_object* v_val_1569_, lean_object* v_k_1570_, uint8_t v_nondep_1571_, uint8_t v_kind_1572_, uint8_t v_usedLetOnly_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_box(v_usedLetOnly_1573_);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1584_, 0, v_k_1570_);
lean_closure_set(v___f_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1567_, v_type_1568_, v_val_1569_, v___f_1584_, v_nondep_1571_, v_kind_1572_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1586_, lean_object* v_type_1587_, lean_object* v_val_1588_, lean_object* v_k_1589_, lean_object* v_nondep_1590_, lean_object* v_kind_1591_, lean_object* v_usedLetOnly_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_nondep_boxed_1602_; uint8_t v_kind_boxed_1603_; uint8_t v_usedLetOnly_boxed_1604_; lean_object* v_res_1605_; 
v_nondep_boxed_1602_ = lean_unbox(v_nondep_1590_);
v_kind_boxed_1603_ = lean_unbox(v_kind_1591_);
v_usedLetOnly_boxed_1604_ = lean_unbox(v_usedLetOnly_1592_);
v_res_1605_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1586_, v_type_1587_, v_val_1588_, v_k_1589_, v_nondep_boxed_1602_, v_kind_boxed_1603_, v_usedLetOnly_boxed_1604_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec(v___y_1593_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1606_, uint8_t v_bi_1607_, lean_object* v_type_1608_, lean_object* v_k_1609_, uint8_t v_kind_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___f_1620_; lean_object* v___x_1621_; 
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc(v___y_1611_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1620_, 0, v_k_1609_);
lean_closure_set(v___f_1620_, 1, v___y_1611_);
lean_closure_set(v___f_1620_, 2, v___y_1612_);
lean_closure_set(v___f_1620_, 3, v___y_1613_);
lean_closure_set(v___f_1620_, 4, v___y_1614_);
v___x_1621_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1606_, v_bi_1607_, v_type_1608_, v___f_1620_, v_kind_1610_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1621_) == 0)
{
return v___x_1621_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1630_, lean_object* v_bi_1631_, lean_object* v_type_1632_, lean_object* v_k_1633_, lean_object* v_kind_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v_bi_boxed_1644_; uint8_t v_kind_boxed_1645_; lean_object* v_res_1646_; 
v_bi_boxed_1644_ = lean_unbox(v_bi_1631_);
v_kind_boxed_1645_ = lean_unbox(v_kind_1634_);
v_res_1646_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1630_, v_bi_boxed_1644_, v_type_1632_, v_k_1633_, v_kind_boxed_1645_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec(v___y_1635_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
lean_inc(v___y_1648_);
v___x_1657_ = lean_apply_9(v_k_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, lean_box(0));
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec(v___y_1659_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1669_, uint8_t v_allowLevelAssignments_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___f_1680_; lean_object* v___x_1681_; 
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc(v___y_1672_);
lean_inc(v___y_1671_);
v___f_1680_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1680_, 0, v_k_1669_);
lean_closure_set(v___f_1680_, 1, v___y_1671_);
lean_closure_set(v___f_1680_, 2, v___y_1672_);
lean_closure_set(v___f_1680_, 3, v___y_1673_);
lean_closure_set(v___f_1680_, 4, v___y_1674_);
v___x_1681_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1670_, v___f_1680_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1681_) == 0)
{
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1690_, lean_object* v_allowLevelAssignments_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1701_; lean_object* v_res_1702_; 
v_allowLevelAssignments_boxed_1701_ = lean_unbox(v_allowLevelAssignments_1691_);
v_res_1702_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1690_, v_allowLevelAssignments_boxed_1701_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v___y_1692_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1703_, lean_object* v_x_1704_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_box(0);
return v___x_1705_;
}
else
{
lean_object* v_key_1706_; lean_object* v_value_1707_; lean_object* v_tail_1708_; uint8_t v___x_1709_; 
v_key_1706_ = lean_ctor_get(v_x_1704_, 0);
v_value_1707_ = lean_ctor_get(v_x_1704_, 1);
v_tail_1708_ = lean_ctor_get(v_x_1704_, 2);
v___x_1709_ = lean_expr_eqv(v_key_1706_, v_a_1703_);
if (v___x_1709_ == 0)
{
v_x_1704_ = v_tail_1708_;
goto _start;
}
else
{
lean_object* v___x_1711_; 
lean_inc(v_value_1707_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_value_1707_);
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1712_, lean_object* v_x_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1712_, v_x_1713_);
lean_dec(v_x_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_buckets_1717_; lean_object* v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; uint64_t v_fold_1722_; uint64_t v___x_1723_; uint64_t v___x_1724_; uint64_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_buckets_1717_ = lean_ctor_get(v_m_1715_, 1);
v___x_1718_ = lean_array_get_size(v_buckets_1717_);
v___x_1719_ = l_Lean_Expr_hash(v_a_1716_);
v___x_1720_ = 32ULL;
v___x_1721_ = lean_uint64_shift_right(v___x_1719_, v___x_1720_);
v_fold_1722_ = lean_uint64_xor(v___x_1719_, v___x_1721_);
v___x_1723_ = 16ULL;
v___x_1724_ = lean_uint64_shift_right(v_fold_1722_, v___x_1723_);
v___x_1725_ = lean_uint64_xor(v_fold_1722_, v___x_1724_);
v___x_1726_ = lean_uint64_to_usize(v___x_1725_);
v___x_1727_ = lean_usize_of_nat(v___x_1718_);
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_sub(v___x_1727_, v___x_1728_);
v___x_1730_ = lean_usize_land(v___x_1726_, v___x_1729_);
v___x_1731_ = lean_array_uget_borrowed(v_buckets_1717_, v___x_1730_);
v___x_1732_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1716_, v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1733_, v_a_1734_);
lean_dec_ref(v_a_1734_);
lean_dec_ref(v_m_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1736_, lean_object* v_opt_1737_){
_start:
{
lean_object* v_name_1738_; lean_object* v_defValue_1739_; lean_object* v_map_1740_; lean_object* v___x_1741_; 
v_name_1738_ = lean_ctor_get(v_opt_1737_, 0);
v_defValue_1739_ = lean_ctor_get(v_opt_1737_, 1);
v_map_1740_ = lean_ctor_get(v_opts_1736_, 0);
v___x_1741_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1740_, v_name_1738_);
if (lean_obj_tag(v___x_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_unbox(v_defValue_1739_);
return v___x_1742_;
}
else
{
lean_object* v_val_1743_; 
v_val_1743_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v___x_1741_, 1);
if (lean_obj_tag(v_val_1743_) == 1)
{
uint8_t v_v_1744_; 
v_v_1744_ = lean_ctor_get_uint8(v_val_1743_, 0);
lean_dec_ref_known(v_val_1743_, 0);
return v_v_1744_;
}
else
{
uint8_t v___x_1745_; 
lean_dec(v_val_1743_);
v___x_1745_ = lean_unbox(v_defValue_1739_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1746_, lean_object* v_opt_1747_){
_start:
{
uint8_t v_res_1748_; lean_object* v_r_1749_; 
v_res_1748_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1746_, v_opt_1747_);
lean_dec_ref(v_opt_1747_);
lean_dec_ref(v_opts_1746_);
v_r_1749_ = lean_box(v_res_1748_);
return v_r_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v_array_1752_; lean_object* v_start_1753_; lean_object* v_stop_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1767_; 
v_array_1752_ = lean_ctor_get(v_a_1750_, 0);
v_start_1753_ = lean_ctor_get(v_a_1750_, 1);
v_stop_1754_ = lean_ctor_get(v_a_1750_, 2);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1756_ = v_a_1750_;
v_isShared_1757_ = v_isSharedCheck_1767_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_stop_1754_);
lean_inc(v_start_1753_);
lean_inc(v_array_1752_);
lean_dec(v_a_1750_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1767_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_lt(v_start_1753_, v_stop_1754_);
if (v___x_1758_ == 0)
{
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
return v_b_1751_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_add(v_start_1753_, v___x_1759_);
lean_inc_ref(v_array_1752_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1760_);
v___x_1762_ = v___x_1756_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_array_1752_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_stop_1754_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_array_fget(v_array_1752_, v_start_1753_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
v___x_1764_ = lean_array_push(v_b_1751_, v___x_1763_);
v_a_1750_ = v___x_1762_;
v_b_1751_ = v___x_1764_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1768_, lean_object* v_recFnName_1769_, lean_object* v_fixedPrefixSize_1770_, lean_object* v_F_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_expr_instantiate1(v_body_1768_, v_x_1772_);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1769_, v_fixedPrefixSize_1770_, v_F_1771_, v___x_1782_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
v___x_1787_ = lean_array_push(v___x_1786_, v_x_1772_);
v___x_1788_ = 0;
v___x_1789_ = 1;
v___x_1790_ = 1;
v___x_1791_ = l_Lean_Meta_mkLambdaFVars(v___x_1787_, v_a_1784_, v___x_1788_, v___x_1789_, v___x_1788_, v___x_1789_, v___x_1790_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec_ref(v___x_1787_);
return v___x_1791_;
}
else
{
lean_dec_ref(v_x_1772_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1792_, lean_object* v_recFnName_1793_, lean_object* v_fixedPrefixSize_1794_, lean_object* v_F_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1792_, v_recFnName_1793_, v_fixedPrefixSize_1794_, v_F_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v_body_1792_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1807_, lean_object* v_recFnName_1808_, lean_object* v_fixedPrefixSize_1809_, lean_object* v_F_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_expr_instantiate1(v_body_1807_, v_x_1811_);
v___x_1822_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1808_, v_fixedPrefixSize_1809_, v_F_1810_, v___x_1821_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; uint8_t v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = lean_unsigned_to_nat(1u);
v___x_1825_ = lean_mk_empty_array_with_capacity(v___x_1824_);
v___x_1826_ = lean_array_push(v___x_1825_, v_x_1811_);
v___x_1827_ = 0;
v___x_1828_ = 1;
v___x_1829_ = 1;
v___x_1830_ = l_Lean_Meta_mkForallFVars(v___x_1826_, v_a_1823_, v___x_1827_, v___x_1828_, v___x_1828_, v___x_1829_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec_ref(v___x_1826_);
return v___x_1830_;
}
else
{
lean_dec_ref(v_x_1811_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1831_, lean_object* v_recFnName_1832_, lean_object* v_fixedPrefixSize_1833_, lean_object* v_F_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1831_, v_recFnName_1832_, v_fixedPrefixSize_1833_, v_F_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v_body_1831_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1846_, lean_object* v_recFnName_1847_, lean_object* v_fixedPrefixSize_1848_, lean_object* v_F_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1846_, v_recFnName_1847_, v_fixedPrefixSize_1848_, v_F_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v_x_1850_);
lean_dec_ref(v_body_1846_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1863_, lean_object* v_fixedPrefixSize_1864_, lean_object* v_F_1865_, size_t v_sz_1866_, size_t v_i_1867_, lean_object* v_bs_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_lt(v_i_1867_, v_sz_1866_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec_ref(v_F_1865_);
lean_dec(v_fixedPrefixSize_1864_);
lean_dec(v_recFnName_1863_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_bs_1868_);
return v___x_1879_;
}
else
{
lean_object* v_v_1880_; lean_object* v___x_1881_; lean_object* v_bs_x27_1882_; lean_object* v___x_1883_; 
v_v_1880_ = lean_array_uget(v_bs_1868_, v_i_1867_);
v___x_1881_ = lean_unsigned_to_nat(0u);
v_bs_x27_1882_ = lean_array_uset(v_bs_1868_, v_i_1867_, v___x_1881_);
lean_inc_ref(v_F_1865_);
lean_inc(v_fixedPrefixSize_1864_);
lean_inc(v_recFnName_1863_);
v___x_1883_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1863_, v_fixedPrefixSize_1864_, v_F_1865_, v_v_1880_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = ((size_t)1ULL);
v___x_1886_ = lean_usize_add(v_i_1867_, v___x_1885_);
v___x_1887_ = lean_array_uset(v_bs_x27_1882_, v_i_1867_, v_a_1884_);
v_i_1867_ = v___x_1886_;
v_bs_1868_ = v___x_1887_;
goto _start;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_bs_x27_1882_);
lean_dec_ref(v_F_1865_);
lean_dec(v_fixedPrefixSize_1864_);
lean_dec(v_recFnName_1863_);
v_a_1889_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1883_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1883_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_cls_1904_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1905_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1906_ = l_Lean_Name_append(v___x_1905_, v_cls_1904_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1910_, lean_object* v_fixedPrefixSize_1911_, lean_object* v_F_1912_, lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1935_ = l_Lean_Expr_getAppNumArgs(v_e_1913_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_add(v_fixedPrefixSize_1911_, v___x_1936_);
v___x_1938_ = lean_nat_dec_lt(v___x_1935_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v_dummy_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v_args_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1939_ = l_Lean_instInhabitedExpr;
v_dummy_1940_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1935_);
v___x_1941_ = lean_mk_array(v___x_1935_, v_dummy_1940_);
v___x_1942_ = lean_nat_sub(v___x_1935_, v___x_1936_);
lean_dec(v___x_1935_);
v_args_1943_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1913_, v___x_1941_, v___x_1942_);
v___x_1944_ = lean_array_get_borrowed(v___x_1939_, v_args_1943_, v_fixedPrefixSize_1911_);
lean_inc(v___x_1944_);
lean_inc_ref(v_F_1912_);
lean_inc(v_fixedPrefixSize_1911_);
lean_inc(v_recFnName_1910_);
v___x_1945_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1910_, v_fixedPrefixSize_1911_, v_F_1912_, v___x_1944_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
lean_inc_ref(v_F_1912_);
v___x_1947_ = l_Lean_Expr_app___override(v_F_1912_, v_a_1946_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
lean_inc(v_a_1919_);
lean_inc_ref(v_a_1918_);
lean_inc_ref(v___x_1947_);
v___x_1948_ = lean_infer_type(v___x_1947_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
lean_inc(v_a_1919_);
lean_inc_ref(v_a_1918_);
v___x_1950_ = lean_whnf(v_a_1949_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_Lean_Expr_bindingDomain_x21(v_a_1951_);
lean_dec(v_a_1951_);
v___x_1953_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1952_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; lean_object* v_lower_1957_; lean_object* v_upper_1958_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_Lean_Expr_app___override(v___x_1947_, v_a_1954_);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_array_get_size(v_args_1943_);
v___x_1984_ = lean_nat_dec_le(v___x_1937_, v___x_1982_);
if (v___x_1984_ == 0)
{
v_lower_1957_ = v___x_1937_;
v_upper_1958_ = v___x_1983_;
goto v___jp_1956_;
}
else
{
lean_dec(v___x_1937_);
v_lower_1957_ = v___x_1982_;
v_upper_1958_ = v___x_1983_;
goto v___jp_1956_;
}
v___jp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = l_Array_toSubarray___redArg(v_args_1943_, v_lower_1957_, v_upper_1958_);
v___x_1960_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1961_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1959_, v___x_1960_);
v_sz_1962_ = lean_array_size(v___x_1961_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1910_, v_fixedPrefixSize_1911_, v_F_1912_, v_sz_1962_, v___x_1963_, v___x_1961_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_mkAppN(v___x_1955_, v_a_1965_);
lean_dec(v_a_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1955_);
v_a_1974_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1964_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1964_);
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
else
{
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_args_1943_);
lean_dec(v___x_1937_);
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
return v___x_1953_;
}
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_args_1943_);
lean_dec(v___x_1937_);
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
return v___x_1950_;
}
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_args_1943_);
lean_dec(v___x_1937_);
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
return v___x_1948_;
}
}
else
{
lean_dec_ref(v_args_1943_);
lean_dec(v___x_1937_);
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
return v___x_1945_;
}
}
else
{
lean_object* v_toCold_1985_; lean_object* v_options_1986_; uint8_t v_hasTrace_1987_; 
lean_dec(v___x_1937_);
lean_dec(v___x_1935_);
v_toCold_1985_ = lean_ctor_get(v_a_1920_, 0);
v_options_1986_ = lean_ctor_get(v_toCold_1985_, 2);
v_hasTrace_1987_ = lean_ctor_get_uint8(v_options_1986_, sizeof(void*)*1);
if (v_hasTrace_1987_ == 0)
{
v___y_1924_ = v_a_1914_;
v___y_1925_ = v_a_1915_;
v___y_1926_ = v_a_1916_;
v___y_1927_ = v_a_1917_;
v___y_1928_ = v_a_1918_;
v___y_1929_ = v_a_1919_;
v___y_1930_ = v_a_1920_;
v___y_1931_ = v_a_1921_;
goto v___jp_1923_;
}
else
{
lean_object* v_inheritedTraceOptions_1988_; lean_object* v_cls_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_toCold_1985_, 11);
v_cls_1989_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1990_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1986_, v___x_1990_);
if (v___x_1991_ == 0)
{
v___y_1924_ = v_a_1914_;
v___y_1925_ = v_a_1915_;
v___y_1926_ = v_a_1916_;
v___y_1927_ = v_a_1917_;
v___y_1928_ = v_a_1918_;
v___y_1929_ = v_a_1919_;
v___y_1930_ = v_a_1920_;
v___y_1931_ = v_a_1921_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1992_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1913_);
v___x_1993_ = l_Lean_indentExpr(v_e_1913_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1989_, v___x_1994_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref_known(v___x_1995_, 1);
v___y_1924_ = v_a_1914_;
v___y_1925_ = v_a_1915_;
v___y_1926_ = v_a_1916_;
v___y_1927_ = v_a_1917_;
v___y_1928_ = v_a_1918_;
v___y_1929_ = v_a_1919_;
v___y_1930_ = v_a_1920_;
v___y_1931_ = v_a_1921_;
goto v___jp_1923_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_e_1913_);
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
v___jp_1923_:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_etaExpand(v_e_1913_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1910_, v_fixedPrefixSize_1911_, v_F_1912_, v_a_1933_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
return v___x_1934_;
}
else
{
lean_dec_ref(v_F_1912_);
lean_dec(v_fixedPrefixSize_1911_);
lean_dec(v_recFnName_1910_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_2004_, lean_object* v_fixedPrefixSize_2005_, lean_object* v_F_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 5)
{
lean_object* v_fn_2019_; lean_object* v_arg_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_fn_2019_ = lean_ctor_get(v_x_2007_, 0);
lean_inc_ref(v_fn_2019_);
v_arg_2020_ = lean_ctor_get(v_x_2007_, 1);
lean_inc_ref(v_arg_2020_);
lean_dec_ref_known(v_x_2007_, 2);
v___x_2021_ = lean_array_set(v_x_2008_, v_x_2009_, v_arg_2020_);
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = lean_nat_sub(v_x_2009_, v___x_2022_);
lean_dec(v_x_2009_);
v_x_2007_ = v_fn_2019_;
v_x_2008_ = v___x_2021_;
v_x_2009_ = v___x_2023_;
goto _start;
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_x_2009_);
lean_inc_ref(v_F_2006_);
lean_inc(v_fixedPrefixSize_2005_);
lean_inc(v_recFnName_2004_);
v___x_2025_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2004_, v_fixedPrefixSize_2005_, v_F_2006_, v_x_2007_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; size_t v_sz_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v_sz_2027_ = lean_array_size(v_x_2008_);
v___x_2028_ = ((size_t)0ULL);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2004_, v_fixedPrefixSize_2005_, v_F_2006_, v_sz_2027_, v___x_2028_, v_x_2008_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2038_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = l_Lean_mkAppN(v_a_2026_, v_a_2030_);
lean_dec(v_a_2030_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2034_);
v___x_2036_ = v___x_2032_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2026_);
v_a_2039_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2029_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2029_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_dec_ref(v_x_2008_);
lean_dec_ref(v_F_2006_);
lean_dec(v_fixedPrefixSize_2005_);
lean_dec(v_recFnName_2004_);
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2047_, lean_object* v_fixedPrefixSize_2048_, lean_object* v_F_2049_, lean_object* v_e_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Expr_isAppOf(v_e_2050_, v_recFnName_2047_);
if (v___x_2060_ == 0)
{
lean_object* v_dummy_2061_; lean_object* v_nargs_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_dummy_2061_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2062_ = l_Lean_Expr_getAppNumArgs(v_e_2050_);
lean_inc(v_nargs_2062_);
v___x_2063_ = lean_mk_array(v_nargs_2062_, v_dummy_2061_);
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_nat_sub(v_nargs_2062_, v___x_2064_);
lean_dec(v_nargs_2062_);
v___x_2066_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2047_, v_fixedPrefixSize_2048_, v_F_2049_, v_e_2050_, v___x_2063_, v___x_2065_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2047_, v_fixedPrefixSize_2048_, v_F_2049_, v_e_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
return v___x_2067_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2070_ = l_Lean_stringToMessageData(v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2074_, lean_object* v_b_2075_, lean_object* v_recFnName_2076_, lean_object* v_fixedPrefixSize_2077_, uint8_t v___x_2078_, lean_object* v___x_2079_, lean_object* v_a_2080_, lean_object* v_e_2081_, lean_object* v_xs_2082_, lean_object* v_altBody_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_array_get_size(v_xs_2082_);
v___x_2101_ = lean_nat_dec_eq(v___x_2100_, v___x_2079_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_altBody_2083_);
lean_dec(v_fixedPrefixSize_2077_);
lean_dec(v_recFnName_2076_);
v___x_2102_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2103_ = l_Lean_indentExpr(v_a_2080_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = l_Lean_indentExpr(v_e_2081_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2108_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_dec_ref(v_e_2081_);
lean_dec_ref(v_a_2080_);
goto v___jp_2093_;
}
v___jp_2093_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_array_get_borrowed(v___x_2074_, v_xs_2082_, v_b_2075_);
lean_inc(v___x_2094_);
v___x_2095_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2076_, v_fixedPrefixSize_2077_, v___x_2094_, v_altBody_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; uint8_t v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = 0;
v___x_2098_ = 1;
v___x_2099_ = l_Lean_Meta_mkLambdaFVars(v_xs_2082_, v_a_2096_, v___x_2097_, v___x_2078_, v___x_2097_, v___x_2078_, v___x_2098_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
return v___x_2099_;
}
else
{
return v___x_2095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2118_ = _args[0];
lean_object* v_b_2119_ = _args[1];
lean_object* v_recFnName_2120_ = _args[2];
lean_object* v_fixedPrefixSize_2121_ = _args[3];
lean_object* v___x_2122_ = _args[4];
lean_object* v___x_2123_ = _args[5];
lean_object* v_a_2124_ = _args[6];
lean_object* v_e_2125_ = _args[7];
lean_object* v_xs_2126_ = _args[8];
lean_object* v_altBody_2127_ = _args[9];
lean_object* v___y_2128_ = _args[10];
lean_object* v___y_2129_ = _args[11];
lean_object* v___y_2130_ = _args[12];
lean_object* v___y_2131_ = _args[13];
lean_object* v___y_2132_ = _args[14];
lean_object* v___y_2133_ = _args[15];
lean_object* v___y_2134_ = _args[16];
lean_object* v___y_2135_ = _args[17];
lean_object* v___y_2136_ = _args[18];
_start:
{
uint8_t v___x_57737__boxed_2137_; lean_object* v_res_2138_; 
v___x_57737__boxed_2137_ = lean_unbox(v___x_2122_);
v_res_2138_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2118_, v_b_2119_, v_recFnName_2120_, v_fixedPrefixSize_2121_, v___x_57737__boxed_2137_, v___x_2123_, v_a_2124_, v_e_2125_, v_xs_2126_, v_altBody_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v_xs_2126_);
lean_dec(v___x_2123_);
lean_dec(v_b_2119_);
lean_dec_ref(v___x_2118_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2139_, lean_object* v_fixedPrefixSize_2140_, lean_object* v_e_2141_, lean_object* v_as_2142_, lean_object* v_bs_2143_, lean_object* v_i_2144_, lean_object* v_cs_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_array_get_size(v_as_2142_);
v___x_2156_ = lean_nat_dec_lt(v_i_2144_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_i_2144_);
lean_dec_ref(v_e_2141_);
lean_dec(v_fixedPrefixSize_2140_);
lean_dec(v_recFnName_2139_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_cs_2145_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = lean_array_get_size(v_bs_2143_);
v___x_2159_ = lean_nat_dec_lt(v_i_2144_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec(v_i_2144_);
lean_dec_ref(v_e_2141_);
lean_dec(v_fixedPrefixSize_2140_);
lean_dec(v_recFnName_2139_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_cs_2145_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v_a_2162_; lean_object* v_b_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2161_ = l_Lean_instInhabitedExpr;
v_a_2162_ = lean_array_fget_borrowed(v_as_2142_, v_i_2144_);
v_b_2163_ = lean_array_fget_borrowed(v_bs_2143_, v_i_2144_);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_add(v_b_2163_, v___x_2164_);
v___x_2166_ = lean_box(v___x_2159_);
lean_inc_ref(v_e_2141_);
lean_inc_n(v_a_2162_, 2);
lean_inc(v___x_2165_);
lean_inc(v_fixedPrefixSize_2140_);
lean_inc(v_recFnName_2139_);
lean_inc(v_b_2163_);
v___f_2167_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2167_, 0, v___x_2161_);
lean_closure_set(v___f_2167_, 1, v_b_2163_);
lean_closure_set(v___f_2167_, 2, v_recFnName_2139_);
lean_closure_set(v___f_2167_, 3, v_fixedPrefixSize_2140_);
lean_closure_set(v___f_2167_, 4, v___x_2166_);
lean_closure_set(v___f_2167_, 5, v___x_2165_);
lean_closure_set(v___f_2167_, 6, v_a_2162_);
lean_closure_set(v___f_2167_, 7, v_e_2141_);
v___x_2168_ = 0;
v___x_2169_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2162_, v___x_2165_, v___f_2167_, v___x_2168_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_nat_add(v_i_2144_, v___x_2164_);
lean_dec(v_i_2144_);
v___x_2172_ = lean_array_push(v_cs_2145_, v_a_2170_);
v_i_2144_ = v___x_2171_;
v_cs_2145_ = v___x_2172_;
goto _start;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_cs_2145_);
lean_dec(v_i_2144_);
lean_dec_ref(v_e_2141_);
lean_dec(v_fixedPrefixSize_2140_);
lean_dec(v_recFnName_2139_);
v_a_2174_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2169_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2169_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2182_, lean_object* v_fixedPrefixSize_2183_, lean_object* v_F_2184_, lean_object* v_e_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
switch(lean_obj_tag(v_e_2185_))
{
case 6:
{
lean_object* v_binderName_2195_; lean_object* v_binderType_2196_; lean_object* v_body_2197_; uint8_t v_binderInfo_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
v_binderName_2195_ = lean_ctor_get(v_e_2185_, 0);
lean_inc(v_binderName_2195_);
v_binderType_2196_ = lean_ctor_get(v_e_2185_, 1);
lean_inc_ref(v_binderType_2196_);
v_body_2197_ = lean_ctor_get(v_e_2185_, 2);
lean_inc_ref(v_body_2197_);
v_binderInfo_2198_ = lean_ctor_get_uint8(v_e_2185_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2185_, 3);
lean_inc_ref(v_F_2184_);
lean_inc(v_fixedPrefixSize_2183_);
lean_inc(v_recFnName_2182_);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2199_, 0, v_body_2197_);
lean_closure_set(v___f_2199_, 1, v_recFnName_2182_);
lean_closure_set(v___f_2199_, 2, v_fixedPrefixSize_2183_);
lean_closure_set(v___f_2199_, 3, v_F_2184_);
v___x_2200_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_binderType_2196_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = 0;
v___x_2203_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2195_, v_binderInfo_2198_, v_a_2201_, v___f_2199_, v___x_2202_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2203_;
}
else
{
lean_dec_ref(v___f_2199_);
lean_dec(v_binderName_2195_);
return v___x_2200_;
}
}
case 7:
{
lean_object* v_binderName_2204_; lean_object* v_binderType_2205_; lean_object* v_body_2206_; uint8_t v_binderInfo_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; 
v_binderName_2204_ = lean_ctor_get(v_e_2185_, 0);
lean_inc(v_binderName_2204_);
v_binderType_2205_ = lean_ctor_get(v_e_2185_, 1);
lean_inc_ref(v_binderType_2205_);
v_body_2206_ = lean_ctor_get(v_e_2185_, 2);
lean_inc_ref(v_body_2206_);
v_binderInfo_2207_ = lean_ctor_get_uint8(v_e_2185_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2185_, 3);
lean_inc_ref(v_F_2184_);
lean_inc(v_fixedPrefixSize_2183_);
lean_inc(v_recFnName_2182_);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2208_, 0, v_body_2206_);
lean_closure_set(v___f_2208_, 1, v_recFnName_2182_);
lean_closure_set(v___f_2208_, 2, v_fixedPrefixSize_2183_);
lean_closure_set(v___f_2208_, 3, v_F_2184_);
v___x_2209_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_binderType_2205_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = 0;
v___x_2212_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2204_, v_binderInfo_2207_, v_a_2210_, v___f_2208_, v___x_2211_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2212_;
}
else
{
lean_dec_ref(v___f_2208_);
lean_dec(v_binderName_2204_);
return v___x_2209_;
}
}
case 8:
{
lean_object* v_declName_2213_; lean_object* v_type_2214_; lean_object* v_value_2215_; lean_object* v_body_2216_; uint8_t v_nondep_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
v_declName_2213_ = lean_ctor_get(v_e_2185_, 0);
lean_inc(v_declName_2213_);
v_type_2214_ = lean_ctor_get(v_e_2185_, 1);
lean_inc_ref(v_type_2214_);
v_value_2215_ = lean_ctor_get(v_e_2185_, 2);
lean_inc_ref(v_value_2215_);
v_body_2216_ = lean_ctor_get(v_e_2185_, 3);
lean_inc_ref(v_body_2216_);
v_nondep_2217_ = lean_ctor_get_uint8(v_e_2185_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2185_, 4);
lean_inc_ref_n(v_F_2184_, 2);
lean_inc_n(v_fixedPrefixSize_2183_, 2);
lean_inc_n(v_recFnName_2182_, 2);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2218_, 0, v_body_2216_);
lean_closure_set(v___f_2218_, 1, v_recFnName_2182_);
lean_closure_set(v___f_2218_, 2, v_fixedPrefixSize_2183_);
lean_closure_set(v___f_2218_, 3, v_F_2184_);
v___x_2219_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_type_2214_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_value_2215_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = 0;
v___x_2224_ = 0;
v___x_2225_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2213_, v_a_2220_, v_a_2222_, v___f_2218_, v_nondep_2217_, v___x_2223_, v___x_2224_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2225_;
}
else
{
lean_dec(v_a_2220_);
lean_dec_ref(v___f_2218_);
lean_dec(v_declName_2213_);
return v___x_2221_;
}
}
else
{
lean_dec_ref(v___f_2218_);
lean_dec_ref(v_value_2215_);
lean_dec(v_declName_2213_);
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
lean_dec(v_recFnName_2182_);
return v___x_2219_;
}
}
case 10:
{
lean_object* v_data_2226_; lean_object* v_expr_2227_; lean_object* v___x_2228_; 
v_data_2226_ = lean_ctor_get(v_e_2185_, 0);
lean_inc(v_data_2226_);
v_expr_2227_ = lean_ctor_get(v_e_2185_, 1);
lean_inc_ref(v_expr_2227_);
v___x_2228_ = l_Lean_getRecAppSyntax_x3f(v_e_2185_);
lean_dec_ref_known(v_e_2185_, 2);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v_toCold_2230_; lean_object* v_currRecDepth_2231_; lean_object* v_ref_2232_; uint16_t v_optionFlags_2233_; uint8_t v_suppressElabErrors_2234_; uint8_t v_isRecordingDeps_2235_; lean_object* v_ref_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_data_2226_);
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v_toCold_2230_ = lean_ctor_get(v_a_2192_, 0);
v_currRecDepth_2231_ = lean_ctor_get(v_a_2192_, 1);
v_ref_2232_ = lean_ctor_get(v_a_2192_, 2);
v_optionFlags_2233_ = lean_ctor_get_uint16(v_a_2192_, sizeof(void*)*3);
v_suppressElabErrors_2234_ = lean_ctor_get_uint8(v_a_2192_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2235_ = lean_ctor_get_uint8(v_a_2192_, sizeof(void*)*3 + 3);
v_ref_2236_ = l_Lean_replaceRef(v_val_2229_, v_ref_2232_);
lean_dec(v_val_2229_);
lean_inc(v_currRecDepth_2231_);
lean_inc_ref(v_toCold_2230_);
v___x_2237_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2237_, 0, v_toCold_2230_);
lean_ctor_set(v___x_2237_, 1, v_currRecDepth_2231_);
lean_ctor_set(v___x_2237_, 2, v_ref_2236_);
lean_ctor_set_uint16(v___x_2237_, sizeof(void*)*3, v_optionFlags_2233_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*3 + 2, v_suppressElabErrors_2234_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*3 + 3, v_isRecordingDeps_2235_);
v___x_2238_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_expr_2227_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v___x_2237_, v_a_2193_);
lean_dec_ref_known(v___x_2237_, 3);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; 
lean_dec(v___x_2228_);
v___x_2239_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_expr_2227_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
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
v___x_2244_ = l_Lean_mkMData(v_data_2226_, v_a_2240_);
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
lean_dec(v_data_2226_);
return v___x_2239_;
}
}
}
case 11:
{
lean_object* v_typeName_2249_; lean_object* v_idx_2250_; lean_object* v_struct_2251_; lean_object* v___x_2252_; 
v_typeName_2249_ = lean_ctor_get(v_e_2185_, 0);
lean_inc(v_typeName_2249_);
v_idx_2250_ = lean_ctor_get(v_e_2185_, 1);
lean_inc(v_idx_2250_);
v_struct_2251_ = lean_ctor_get(v_e_2185_, 2);
lean_inc_ref(v_struct_2251_);
lean_dec_ref_known(v_e_2185_, 3);
v___x_2252_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_struct_2251_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2261_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = l_Lean_mkProj(v_typeName_2249_, v_idx_2250_, v_a_2253_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2257_);
v___x_2259_ = v___x_2255_;
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
lean_dec(v_idx_2250_);
lean_dec(v_typeName_2249_);
return v___x_2252_;
}
}
case 4:
{
uint8_t v___x_2262_; 
v___x_2262_ = l_Lean_Expr_isConstOf(v_e_2185_, v_recFnName_2182_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
lean_dec(v_recFnName_2182_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_e_2185_);
return v___x_2263_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_e_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2264_;
}
}
case 5:
{
uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = 1;
lean_inc_ref(v_e_2185_);
v___x_2266_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2185_, v___x_2265_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
if (lean_obj_tag(v_a_2267_) == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_e_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2268_;
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2270_; 
v_val_2269_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v_a_2267_, 1);
lean_inc_ref(v_F_2184_);
v___x_2270_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2269_, v_F_2184_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
if (lean_obj_tag(v_a_2271_) == 1)
{
lean_object* v_val_2272_; lean_object* v_toMatcherInfo_2273_; lean_object* v_matcherName_2274_; lean_object* v_matcherLevels_2275_; lean_object* v_params_2276_; lean_object* v_motive_2277_; lean_object* v_discrs_2278_; lean_object* v_alts_2279_; lean_object* v_remaining_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_val_2272_ = lean_ctor_get(v_a_2271_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v_a_2271_, 1);
v_toMatcherInfo_2273_ = lean_ctor_get(v_val_2272_, 0);
lean_inc_ref(v_toMatcherInfo_2273_);
v_matcherName_2274_ = lean_ctor_get(v_val_2272_, 1);
lean_inc(v_matcherName_2274_);
v_matcherLevels_2275_ = lean_ctor_get(v_val_2272_, 2);
lean_inc_ref(v_matcherLevels_2275_);
v_params_2276_ = lean_ctor_get(v_val_2272_, 3);
lean_inc_ref(v_params_2276_);
v_motive_2277_ = lean_ctor_get(v_val_2272_, 4);
lean_inc_ref(v_motive_2277_);
v_discrs_2278_ = lean_ctor_get(v_val_2272_, 5);
lean_inc_ref(v_discrs_2278_);
v_alts_2279_ = lean_ctor_get(v_val_2272_, 6);
lean_inc_ref(v_alts_2279_);
v_remaining_2280_ = lean_ctor_get(v_val_2272_, 7);
lean_inc_ref(v_remaining_2280_);
v___x_2281_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2272_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2183_);
lean_inc(v_recFnName_2182_);
v___x_2284_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_e_2185_, v_alts_2279_, v___x_2281_, v___x_2282_, v___x_2283_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v_alts_2279_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; size_t v_sz_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v_sz_2286_ = lean_array_size(v_discrs_2278_);
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_sz_2286_, v___x_2287_, v_discrs_2278_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2293_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2293_, 0, v_toMatcherInfo_2273_);
lean_ctor_set(v___x_2293_, 1, v_matcherName_2274_);
lean_ctor_set(v___x_2293_, 2, v_matcherLevels_2275_);
lean_ctor_set(v___x_2293_, 3, v_params_2276_);
lean_ctor_set(v___x_2293_, 4, v_motive_2277_);
lean_ctor_set(v___x_2293_, 5, v_a_2289_);
lean_ctor_set(v___x_2293_, 6, v_a_2285_);
lean_ctor_set(v___x_2293_, 7, v_remaining_2280_);
v___x_2294_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2293_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2285_);
lean_dec_ref(v_remaining_2280_);
lean_dec_ref(v_motive_2277_);
lean_dec_ref(v_params_2276_);
lean_dec_ref(v_matcherLevels_2275_);
lean_dec(v_matcherName_2274_);
lean_dec_ref(v_toMatcherInfo_2273_);
v_a_2299_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2288_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2288_);
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
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_remaining_2280_);
lean_dec_ref(v_discrs_2278_);
lean_dec_ref(v_motive_2277_);
lean_dec_ref(v_params_2276_);
lean_dec_ref(v_matcherLevels_2275_);
lean_dec(v_matcherName_2274_);
lean_dec_ref(v_toMatcherInfo_2273_);
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
lean_dec(v_recFnName_2182_);
v_a_2307_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2284_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2284_);
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
else
{
lean_object* v___x_2315_; 
lean_dec(v_a_2271_);
v___x_2315_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2182_, v_fixedPrefixSize_2183_, v_F_2184_, v_e_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2315_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref_known(v_e_2185_, 2);
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
lean_dec(v_recFnName_2182_);
v_a_2316_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2270_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2270_);
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
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref_known(v_e_2185_, 2);
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
lean_dec(v_recFnName_2182_);
v_a_2324_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2266_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2266_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
default: 
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec_ref(v_F_2184_);
lean_dec(v_fixedPrefixSize_2183_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_mk_empty_array_with_capacity(v___x_2332_);
v___x_2334_ = lean_array_push(v___x_2333_, v_recFnName_2182_);
lean_inc_ref(v_e_2185_);
v___x_2335_ = l_Lean_Elab_ensureNoRecFn(v___x_2334_, v_e_2185_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v___x_2335_, 0);
lean_dec(v_unused_2343_);
v___x_2337_ = v___x_2335_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v___x_2335_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v_e_2185_);
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_e_2185_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_e_2185_);
v_a_2344_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2335_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2335_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2352_, lean_object* v_fixedPrefixSize_2353_, lean_object* v_F_2354_, lean_object* v_e_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___x_2384_; 
lean_inc_ref(v_e_2355_);
lean_inc(v_recFnName_2352_);
v___x_2384_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2352_, v_e_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2472_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2472_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2472_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
uint8_t v___x_2389_; 
v___x_2389_ = lean_unbox(v_a_2385_);
lean_dec(v_a_2385_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref(v_F_2354_);
lean_dec(v_fixedPrefixSize_2353_);
lean_dec(v_recFnName_2352_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v_e_2355_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_e_2355_);
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
uint8_t v___x_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_del_object(v___x_2387_);
v___x_2393_ = 0;
v___x_2449_ = lean_st_ref_get(v_a_2357_);
v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2449_, v_e_2355_);
lean_dec(v___x_2449_);
if (lean_obj_tag(v___x_2450_) == 1)
{
lean_object* v_val_2451_; lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2454_; 
v_val_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_fst_2452_ = lean_ctor_get(v_val_2451_, 0);
lean_inc(v_fst_2452_);
v_snd_2453_ = lean_ctor_get(v_val_2451_, 1);
lean_inc(v_snd_2453_);
lean_dec(v_val_2451_);
v___x_2454_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2453_, v_a_2360_);
lean_dec(v_snd_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2463_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
if (v___x_2459_ == 0)
{
lean_del_object(v___x_2457_);
lean_dec(v_fst_2452_);
v___y_2395_ = v_a_2356_;
v___y_2396_ = v_a_2357_;
v___y_2397_ = v_a_2358_;
v___y_2398_ = v_a_2359_;
v___y_2399_ = v_a_2360_;
v___y_2400_ = v_a_2361_;
v___y_2401_ = v_a_2362_;
v___y_2402_ = v_a_2363_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2461_; 
lean_dec_ref(v_e_2355_);
lean_dec_ref(v_F_2354_);
lean_dec(v_fixedPrefixSize_2353_);
lean_dec(v_recFnName_2352_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_fst_2452_);
v___x_2461_ = v___x_2457_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_fst_2452_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_fst_2452_);
lean_dec_ref(v_e_2355_);
lean_dec_ref(v_F_2354_);
lean_dec(v_fixedPrefixSize_2353_);
lean_dec(v_recFnName_2352_);
v_a_2464_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2454_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2454_);
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
lean_dec(v___x_2450_);
v___y_2395_ = v_a_2356_;
v___y_2396_ = v_a_2357_;
v___y_2397_ = v_a_2358_;
v___y_2398_ = v_a_2359_;
v___y_2399_ = v_a_2360_;
v___y_2400_ = v_a_2361_;
v___y_2401_ = v_a_2362_;
v___y_2402_ = v_a_2363_;
goto v___jp_2394_;
}
v___jp_2394_:
{
lean_object* v___x_2403_; 
lean_inc_ref(v_e_2355_);
v___x_2403_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2352_, v_fixedPrefixSize_2353_, v_F_2354_, v_e_2355_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc_n(v_a_2404_, 2);
lean_dec_ref_known(v___x_2403_, 1);
lean_inc_ref(v_e_2355_);
v___f_2405_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2405_, 0, v_e_2355_);
lean_closure_set(v___f_2405_, 1, v_a_2404_);
v___x_2406_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2440_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2440_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2440_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2411_ = lean_st_ref_take(v___y_2396_);
lean_inc(v_a_2404_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_a_2404_);
lean_ctor_set(v___x_2412_, 1, v_a_2407_);
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2411_, v_e_2355_, v___x_2412_);
v___x_2414_ = lean_st_ref_put(v___y_2396_, v___x_2413_);
v___x_2415_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2401_);
v___x_2416_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2417_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_2415_, v___x_2416_);
lean_dec_ref(v___x_2415_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref(v___f_2405_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v_a_2404_);
v___x_2419_ = v___x_2409_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2404_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
else
{
lean_object* v___x_2421_; uint8_t v_transparency_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; 
lean_del_object(v___x_2409_);
v___x_2421_ = l_Lean_Meta_Context_config(v___y_2399_);
v_transparency_2422_ = lean_ctor_get_uint8(v___x_2421_, 9);
lean_dec_ref(v___x_2421_);
v___x_2423_ = 0;
v___x_2424_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v_keyedConfig_2425_; uint8_t v_trackZetaDelta_2426_; lean_object* v_zetaDeltaSet_2427_; lean_object* v_lctx_2428_; lean_object* v_localInstances_2429_; lean_object* v_defEqCtx_x3f_2430_; lean_object* v_synthPendingDepth_2431_; lean_object* v_customCanUnfoldPredicate_x3f_2432_; uint8_t v_univApprox_2433_; uint8_t v_inTypeClassResolution_2434_; uint8_t v_cacheInferType_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_keyedConfig_2425_ = lean_ctor_get(v___y_2399_, 0);
v_trackZetaDelta_2426_ = lean_ctor_get_uint8(v___y_2399_, sizeof(void*)*7);
v_zetaDeltaSet_2427_ = lean_ctor_get(v___y_2399_, 1);
v_lctx_2428_ = lean_ctor_get(v___y_2399_, 2);
v_localInstances_2429_ = lean_ctor_get(v___y_2399_, 3);
v_defEqCtx_x3f_2430_ = lean_ctor_get(v___y_2399_, 4);
v_synthPendingDepth_2431_ = lean_ctor_get(v___y_2399_, 5);
v_customCanUnfoldPredicate_x3f_2432_ = lean_ctor_get(v___y_2399_, 6);
v_univApprox_2433_ = lean_ctor_get_uint8(v___y_2399_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2434_ = lean_ctor_get_uint8(v___y_2399_, sizeof(void*)*7 + 2);
v_cacheInferType_2435_ = lean_ctor_get_uint8(v___y_2399_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2425_);
v___x_2436_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2423_, v_keyedConfig_2425_);
lean_inc(v_customCanUnfoldPredicate_x3f_2432_);
lean_inc(v_synthPendingDepth_2431_);
lean_inc(v_defEqCtx_x3f_2430_);
lean_inc_ref(v_localInstances_2429_);
lean_inc_ref(v_lctx_2428_);
lean_inc(v_zetaDeltaSet_2427_);
v___x_2437_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v_zetaDeltaSet_2427_);
lean_ctor_set(v___x_2437_, 2, v_lctx_2428_);
lean_ctor_set(v___x_2437_, 3, v_localInstances_2429_);
lean_ctor_set(v___x_2437_, 4, v_defEqCtx_x3f_2430_);
lean_ctor_set(v___x_2437_, 5, v_synthPendingDepth_2431_);
lean_ctor_set(v___x_2437_, 6, v_customCanUnfoldPredicate_x3f_2432_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*7, v_trackZetaDelta_2426_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*7 + 1, v_univApprox_2433_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2434_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*7 + 3, v_cacheInferType_2435_);
v___x_2438_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2405_, v___x_2393_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___x_2437_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref_known(v___x_2437_, 7);
v___y_2366_ = v_a_2404_;
v___y_2367_ = v___x_2438_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2405_, v___x_2393_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
v___y_2366_ = v_a_2404_;
v___y_2367_ = v___x_2439_;
goto v___jp_2365_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v___f_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_e_2355_);
v_a_2441_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2406_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2406_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_dec_ref(v_e_2355_);
return v___x_2403_;
}
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_e_2355_);
lean_dec_ref(v_F_2354_);
lean_dec(v_fixedPrefixSize_2353_);
lean_dec(v_recFnName_2352_);
v_a_2473_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2384_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2384_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
v___jp_2365_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_isSharedCheck_2374_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___y_2367_, 0);
lean_dec(v_unused_2375_);
v___x_2369_ = v___y_2367_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v___y_2367_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___y_2366_);
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___y_2366_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v___y_2366_);
v_a_2376_ = lean_ctor_get(v___y_2367_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___y_2367_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___y_2367_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2481_, lean_object* v_recFnName_2482_, lean_object* v_fixedPrefixSize_2483_, lean_object* v_F_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_expr_instantiate1(v_body_2481_, v_x_2485_);
v___x_2496_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2482_, v_fixedPrefixSize_2483_, v_F_2484_, v___x_2495_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2497_, lean_object* v_fixedPrefixSize_2498_, lean_object* v_F_2499_, lean_object* v_e_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2497_, v_fixedPrefixSize_2498_, v_F_2499_, v_e_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec(v_a_2501_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2511_, lean_object* v_fixedPrefixSize_2512_, lean_object* v_F_2513_, lean_object* v_sz_2514_, lean_object* v_i_2515_, lean_object* v_bs_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
size_t v_sz_boxed_2526_; size_t v_i_boxed_2527_; lean_object* v_res_2528_; 
v_sz_boxed_2526_ = lean_unbox_usize(v_sz_2514_);
lean_dec(v_sz_2514_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2511_, v_fixedPrefixSize_2512_, v_F_2513_, v_sz_boxed_2526_, v_i_boxed_2527_, v_bs_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec(v___y_2517_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2529_, lean_object* v_fixedPrefixSize_2530_, lean_object* v_F_2531_, lean_object* v_x_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2529_, v_fixedPrefixSize_2530_, v_F_2531_, v_x_2532_, v_x_2533_, v_x_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec(v___y_2535_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2545_, lean_object* v_fixedPrefixSize_2546_, lean_object* v_e_2547_, lean_object* v_as_2548_, lean_object* v_bs_2549_, lean_object* v_i_2550_, lean_object* v_cs_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2545_, v_fixedPrefixSize_2546_, v_e_2547_, v_as_2548_, v_bs_2549_, v_i_2550_, v_cs_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v_bs_2549_);
lean_dec_ref(v_as_2548_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2562_, lean_object* v_fixedPrefixSize_2563_, lean_object* v_F_2564_, lean_object* v_e_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2562_, v_fixedPrefixSize_2563_, v_F_2564_, v_e_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec(v_a_2566_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2576_, lean_object* v_fixedPrefixSize_2577_, lean_object* v_F_2578_, lean_object* v_e_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2576_, v_fixedPrefixSize_2577_, v_F_2578_, v_e_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec(v_a_2580_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2590_, lean_object* v_fixedPrefixSize_2591_, lean_object* v_F_2592_, lean_object* v_e_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2590_, v_fixedPrefixSize_2591_, v_F_2592_, v_e_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec(v_a_2594_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2604_, lean_object* v_k_2605_, uint8_t v_allowLevelAssignments_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2605_, v_allowLevelAssignments_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2617_, lean_object* v_k_2618_, lean_object* v_allowLevelAssignments_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2629_; lean_object* v_res_2630_; 
v_allowLevelAssignments_boxed_2629_ = lean_unbox(v_allowLevelAssignments_2619_);
v_res_2630_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2617_, v_k_2618_, v_allowLevelAssignments_boxed_2629_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2631_, lean_object* v_name_2632_, uint8_t v_bi_2633_, lean_object* v_type_2634_, lean_object* v_k_2635_, uint8_t v_kind_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2632_, v_bi_2633_, v_type_2634_, v_k_2635_, v_kind_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_name_2648_, lean_object* v_bi_2649_, lean_object* v_type_2650_, lean_object* v_k_2651_, lean_object* v_kind_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v_bi_boxed_2662_; uint8_t v_kind_boxed_2663_; lean_object* v_res_2664_; 
v_bi_boxed_2662_ = lean_unbox(v_bi_2649_);
v_kind_boxed_2663_ = lean_unbox(v_kind_2652_);
v_res_2664_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2647_, v_name_2648_, v_bi_boxed_2662_, v_type_2650_, v_k_2651_, v_kind_boxed_2663_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec(v___y_2653_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2665_, lean_object* v_e_2666_, lean_object* v_maxFVars_2667_, lean_object* v_k_2668_, uint8_t v_cleanupAnnotations_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2666_, v_maxFVars_2667_, v_k_2668_, v_cleanupAnnotations_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2680_, lean_object* v_e_2681_, lean_object* v_maxFVars_2682_, lean_object* v_k_2683_, lean_object* v_cleanupAnnotations_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2694_; lean_object* v_res_2695_; 
v_cleanupAnnotations_boxed_2694_ = lean_unbox(v_cleanupAnnotations_2684_);
v_res_2695_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2680_, v_e_2681_, v_maxFVars_2682_, v_k_2683_, v_cleanupAnnotations_boxed_2694_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2696_, lean_object* v_R_2697_, lean_object* v_a_2698_, lean_object* v_b_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2698_, v_b_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2701_, v_msg_2702_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2713_, lean_object* v_msg_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2713_, v_msg_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v___y_2715_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2725_, lean_object* v_m_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2726_, v_a_2727_, v_b_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2730_, lean_object* v_msg_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2731_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2742_, v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2754_, lean_object* v_m_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2755_, v_a_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2758_, lean_object* v_m_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2758_, v_m_2759_, v_a_2760_);
lean_dec_ref(v_a_2760_);
lean_dec_ref(v_m_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2762_, lean_object* v_name_2763_, lean_object* v_type_2764_, lean_object* v_val_2765_, lean_object* v_k_2766_, uint8_t v_nondep_2767_, uint8_t v_kind_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2763_, v_type_2764_, v_val_2765_, v_k_2766_, v_nondep_2767_, v_kind_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_name_2780_, lean_object* v_type_2781_, lean_object* v_val_2782_, lean_object* v_k_2783_, lean_object* v_nondep_2784_, lean_object* v_kind_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v_nondep_boxed_2795_; uint8_t v_kind_boxed_2796_; lean_object* v_res_2797_; 
v_nondep_boxed_2795_ = lean_unbox(v_nondep_2784_);
v_kind_boxed_2796_ = lean_unbox(v_kind_2785_);
v_res_2797_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2779_, v_name_2780_, v_type_2781_, v_val_2782_, v_k_2783_, v_nondep_boxed_2795_, v_kind_boxed_2796_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2798_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2810_);
return v_res_2819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2820_, lean_object* v_a_2821_, lean_object* v_x_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2821_, v_x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2824_, lean_object* v_a_2825_, lean_object* v_x_2826_){
_start:
{
uint8_t v_res_2827_; lean_object* v_r_2828_; 
v_res_2827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2824_, v_a_2825_, v_x_2826_);
lean_dec(v_x_2826_);
lean_dec_ref(v_a_2825_);
v_r_2828_ = lean_box(v_res_2827_);
return v_r_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2829_, lean_object* v_data_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2832_, lean_object* v_a_2833_, lean_object* v_b_2834_, lean_object* v_x_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2833_, v_b_2834_, v_x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2837_, lean_object* v_a_2838_, lean_object* v_x_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2838_, v_x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2841_, lean_object* v_a_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2841_, v_a_2842_, v_x_2843_);
lean_dec(v_x_2843_);
lean_dec_ref(v_a_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2845_, lean_object* v_i_2846_, lean_object* v_source_2847_, lean_object* v_target_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2846_, v_source_2847_, v_target_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2850_, lean_object* v_constName_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_constName_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2862_, v_constName_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2875_, v_x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2878_, lean_object* v_ref_2879_, lean_object* v_constName_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2879_, v_constName_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_ref_2892_, lean_object* v_constName_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2891_, v_ref_2892_, v_constName_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec(v_ref_2892_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2904_, lean_object* v_ref_2905_, lean_object* v_msg_2906_, lean_object* v_declHint_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2905_, v_msg_2906_, v_declHint_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_ref_2919_, lean_object* v_msg_2920_, lean_object* v_declHint_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2918_, v_ref_2919_, v_msg_2920_, v_declHint_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec(v_ref_2919_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2932_, lean_object* v_declHint_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2932_, v_declHint_2933_, v___y_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2944_, lean_object* v_declHint_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2944_, v_declHint_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2956_, lean_object* v_ref_2957_, lean_object* v_msg_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2957_, v_msg_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_ref_2970_, lean_object* v_msg_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2969_, v_ref_2970_, v_msg_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec(v_ref_2970_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_ref_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3036_; 
v_ref_2989_ = lean_ctor_get(v___y_2986_, 2);
v___x_2990_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3036_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3036_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v_traceState_2996_; lean_object* v_env_2997_; lean_object* v_nextMacroScope_2998_; lean_object* v_ngen_2999_; lean_object* v_auxDeclNGen_3000_; lean_object* v_cache_3001_; lean_object* v_recordedDeps_3002_; lean_object* v_messages_3003_; lean_object* v_infoState_3004_; lean_object* v_snapshotTasks_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3035_; 
v___x_2995_ = lean_st_ref_take(v___y_2987_);
v_traceState_2996_ = lean_ctor_get(v___x_2995_, 4);
v_env_2997_ = lean_ctor_get(v___x_2995_, 0);
v_nextMacroScope_2998_ = lean_ctor_get(v___x_2995_, 1);
v_ngen_2999_ = lean_ctor_get(v___x_2995_, 2);
v_auxDeclNGen_3000_ = lean_ctor_get(v___x_2995_, 3);
v_cache_3001_ = lean_ctor_get(v___x_2995_, 5);
v_recordedDeps_3002_ = lean_ctor_get(v___x_2995_, 6);
v_messages_3003_ = lean_ctor_get(v___x_2995_, 7);
v_infoState_3004_ = lean_ctor_get(v___x_2995_, 8);
v_snapshotTasks_3005_ = lean_ctor_get(v___x_2995_, 9);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3007_ = v___x_2995_;
v_isShared_3008_ = v_isSharedCheck_3035_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_snapshotTasks_3005_);
lean_inc(v_infoState_3004_);
lean_inc(v_messages_3003_);
lean_inc(v_recordedDeps_3002_);
lean_inc(v_cache_3001_);
lean_inc(v_traceState_2996_);
lean_inc(v_auxDeclNGen_3000_);
lean_inc(v_ngen_2999_);
lean_inc(v_nextMacroScope_2998_);
lean_inc(v_env_2997_);
lean_dec(v___x_2995_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3035_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
uint64_t v_tid_3009_; lean_object* v_traces_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3034_; 
v_tid_3009_ = lean_ctor_get_uint64(v_traceState_2996_, sizeof(void*)*1);
v_traces_3010_ = lean_ctor_get(v_traceState_2996_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_traceState_2996_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3012_ = v_traceState_2996_;
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_traces_3010_);
lean_dec(v_traceState_2996_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; double v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3017_ = 0;
v___x_3018_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3019_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3019_, 0, v_cls_2982_);
lean_ctor_set(v___x_3019_, 1, v___x_3015_);
lean_ctor_set(v___x_3019_, 2, v___x_3018_);
lean_ctor_set_float(v___x_3019_, sizeof(void*)*3, v___x_3016_);
lean_ctor_set_float(v___x_3019_, sizeof(void*)*3 + 8, v___x_3016_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*3 + 16, v___x_3017_);
v___x_3020_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3021_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v_a_2991_);
lean_ctor_set(v___x_3021_, 2, v___x_3020_);
lean_inc(v_ref_2989_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_ref_2989_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = l_Lean_PersistentArray_push___redArg(v_traces_3010_, v___x_3022_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3023_);
v___x_3025_ = v___x_3012_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3023_);
lean_ctor_set_uint64(v_reuseFailAlloc_3033_, sizeof(void*)*1, v_tid_3009_);
v___x_3025_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 4, v___x_3025_);
v___x_3027_ = v___x_3007_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_env_2997_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_nextMacroScope_2998_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_ngen_2999_);
lean_ctor_set(v_reuseFailAlloc_3032_, 3, v_auxDeclNGen_3000_);
lean_ctor_set(v_reuseFailAlloc_3032_, 4, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3032_, 5, v_cache_3001_);
lean_ctor_set(v_reuseFailAlloc_3032_, 6, v_recordedDeps_3002_);
lean_ctor_set(v_reuseFailAlloc_3032_, 7, v_messages_3003_);
lean_ctor_set(v_reuseFailAlloc_3032_, 8, v_infoState_3004_);
lean_ctor_set(v_reuseFailAlloc_3032_, 9, v_snapshotTasks_3005_);
v___x_3027_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_st_ref_put(v___y_2987_, v___x_3027_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3014_);
v___x_3030_ = v___x_2993_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3014_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3037_, lean_object* v_msg_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3037_, v_msg_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3044_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_unsigned_to_nat(16u);
v___x_3047_ = lean_mk_array(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3060_, lean_object* v_fixedPrefixSize_3061_, lean_object* v_F_3062_, lean_object* v_e_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v_toCold_3092_; lean_object* v_options_3093_; uint8_t v_hasTrace_3094_; 
v_toCold_3092_ = lean_ctor_get(v_a_3068_, 0);
v_options_3093_ = lean_ctor_get(v_toCold_3092_, 2);
v_hasTrace_3094_ = lean_ctor_get_uint8(v_options_3093_, sizeof(void*)*1);
if (v_hasTrace_3094_ == 0)
{
v___y_3072_ = v_a_3064_;
v___y_3073_ = v_a_3065_;
v___y_3074_ = v_a_3066_;
v___y_3075_ = v_a_3067_;
v___y_3076_ = v_a_3068_;
v___y_3077_ = v_a_3069_;
goto v___jp_3071_;
}
else
{
lean_object* v_inheritedTraceOptions_3095_; lean_object* v_cls_3096_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_options_3103_; lean_object* v_inheritedTraceOptions_3104_; lean_object* v___y_3105_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_inheritedTraceOptions_3095_ = lean_ctor_get(v_toCold_3092_, 11);
v_cls_3096_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3126_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3095_, v_options_3093_, v___x_3126_);
if (v___x_3127_ == 0)
{
v___y_3098_ = v_a_3064_;
v___y_3099_ = v_a_3065_;
v___y_3100_ = v_a_3066_;
v___y_3101_ = v_a_3067_;
v___y_3102_ = v_a_3068_;
v_options_3103_ = v_options_3093_;
v_inheritedTraceOptions_3104_ = v_inheritedTraceOptions_3095_;
v___y_3105_ = v_a_3069_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3128_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3063_);
v___x_3129_ = l_Lean_indentExpr(v_e_3063_);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3096_, v___x_3130_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_dec_ref_known(v___x_3131_, 1);
v___y_3098_ = v_a_3064_;
v___y_3099_ = v_a_3065_;
v___y_3100_ = v_a_3066_;
v___y_3101_ = v_a_3067_;
v___y_3102_ = v_a_3068_;
v_options_3103_ = v_options_3093_;
v_inheritedTraceOptions_3104_ = v_inheritedTraceOptions_3095_;
v___y_3105_ = v_a_3069_;
goto v___jp_3097_;
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v_e_3063_);
lean_dec_ref(v_F_3062_);
lean_dec(v_fixedPrefixSize_3061_);
lean_dec(v_recFnName_3060_);
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
v___jp_3097_:
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3107_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3104_, v_options_3103_, v___x_3106_);
if (v___x_3107_ == 0)
{
v___y_3072_ = v___y_3098_;
v___y_3073_ = v___y_3099_;
v___y_3074_ = v___y_3100_;
v___y_3075_ = v___y_3101_;
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3105_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3108_; 
lean_inc(v___y_3105_);
lean_inc_ref(v___y_3102_);
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
lean_inc_ref(v_F_3062_);
v___x_3108_ = lean_infer_type(v_F_3062_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3105_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3062_);
v___x_3111_ = l_Lean_MessageData_ofExpr(v_F_3062_);
v___x_3112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3112_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = l_Lean_indentExpr(v_a_3109_);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3096_, v___x_3116_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3105_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_dec_ref_known(v___x_3117_, 1);
v___y_3072_ = v___y_3098_;
v___y_3073_ = v___y_3099_;
v___y_3074_ = v___y_3100_;
v___y_3075_ = v___y_3101_;
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3105_;
goto v___jp_3071_;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_e_3063_);
lean_dec_ref(v_F_3062_);
lean_dec(v_fixedPrefixSize_3061_);
lean_dec(v_recFnName_3060_);
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
else
{
lean_dec_ref(v_e_3063_);
lean_dec_ref(v_F_3062_);
lean_dec(v_fixedPrefixSize_3061_);
lean_dec(v_recFnName_3060_);
return v___x_3108_;
}
}
}
}
v___jp_3071_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3079_ = lean_st_mk_ref(v___x_3078_);
v___x_3080_ = lean_st_mk_ref(v___x_3078_);
v___x_3081_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3060_, v_fixedPrefixSize_3061_, v_F_3062_, v_e_3063_, v___x_3080_, v___x_3079_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3091_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3091_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3091_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3086_ = lean_st_ref_get(v___x_3080_);
lean_dec(v___x_3080_);
lean_dec(v___x_3086_);
v___x_3087_ = lean_st_ref_get(v___x_3079_);
lean_dec(v___x_3079_);
lean_dec(v___x_3087_);
if (v_isShared_3085_ == 0)
{
v___x_3089_ = v___x_3084_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3082_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
else
{
lean_dec(v___x_3080_);
lean_dec(v___x_3079_);
return v___x_3081_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3140_, lean_object* v_fixedPrefixSize_3141_, lean_object* v_F_3142_, lean_object* v_e_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3140_, v_fixedPrefixSize_3141_, v_F_3142_, v_e_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3152_, lean_object* v_msg_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3152_, v_msg_3153_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3162_, lean_object* v_msg_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3162_, v_msg_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v_b_3175_, lean_object* v_c_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; 
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
v___x_3182_ = lean_apply_9(v_k_3172_, v_b_3175_, v_c_3176_, v___y_3173_, v___y_3174_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v_b_3186_, lean_object* v_c_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3183_, v___y_3184_, v___y_3185_, v_b_3186_, v_c_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3194_, lean_object* v_maxFVars_3195_, lean_object* v_k_3196_, uint8_t v_cleanupAnnotations_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___f_3205_; uint8_t v___x_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3205_, 0, v_k_3196_);
lean_closure_set(v___f_3205_, 1, v___y_3198_);
lean_closure_set(v___f_3205_, 2, v___y_3199_);
v___x_3206_ = 1;
v___x_3207_ = 0;
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_maxFVars_3195_);
v___x_3209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3194_, v___x_3206_, v___x_3207_, v___x_3206_, v___x_3207_, v___x_3208_, v___f_3205_, v_cleanupAnnotations_3197_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec_ref_known(v___x_3208_, 1);
if (lean_obj_tag(v___x_3209_) == 0)
{
return v___x_3209_;
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3218_, lean_object* v_maxFVars_3219_, lean_object* v_k_3220_, lean_object* v_cleanupAnnotations_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3229_; lean_object* v_res_3230_; 
v_cleanupAnnotations_boxed_3229_ = lean_unbox(v_cleanupAnnotations_3221_);
v_res_3230_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3218_, v_maxFVars_3219_, v_k_3220_, v_cleanupAnnotations_boxed_3229_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3231_, lean_object* v_e_3232_, lean_object* v_maxFVars_3233_, lean_object* v_k_3234_, uint8_t v_cleanupAnnotations_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3232_, v_maxFVars_3233_, v_k_3234_, v_cleanupAnnotations_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_e_3245_, lean_object* v_maxFVars_3246_, lean_object* v_k_3247_, lean_object* v_cleanupAnnotations_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3256_; lean_object* v_res_3257_; 
v_cleanupAnnotations_boxed_3256_ = lean_unbox(v_cleanupAnnotations_3248_);
v_res_3257_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3244_, v_e_3245_, v_maxFVars_3246_, v_k_3247_, v_cleanupAnnotations_boxed_3256_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3258_, lean_object* v_k_3259_, uint8_t v_cleanupAnnotations_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___f_3268_; uint8_t v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3268_, 0, v_k_3259_);
lean_closure_set(v___f_3268_, 1, v___y_3261_);
lean_closure_set(v___f_3268_, 2, v___y_3262_);
v___x_3269_ = 1;
v___x_3270_ = 0;
v___x_3271_ = lean_box(0);
v___x_3272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3258_, v___x_3269_, v___x_3270_, v___x_3269_, v___x_3270_, v___x_3271_, v___f_3268_, v_cleanupAnnotations_3260_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3272_) == 0)
{
return v___x_3272_;
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3281_, lean_object* v_k_3282_, lean_object* v_cleanupAnnotations_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3291_; lean_object* v_res_3292_; 
v_cleanupAnnotations_boxed_3291_ = lean_unbox(v_cleanupAnnotations_3283_);
v_res_3292_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3281_, v_k_3282_, v_cleanupAnnotations_boxed_3291_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3293_, lean_object* v_e_3294_, lean_object* v_k_3295_, uint8_t v_cleanupAnnotations_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3294_, v_k_3295_, v_cleanupAnnotations_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3305_, lean_object* v_e_3306_, lean_object* v_k_3307_, lean_object* v_cleanupAnnotations_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3316_; lean_object* v_res_3317_; 
v_cleanupAnnotations_boxed_3316_ = lean_unbox(v_cleanupAnnotations_3308_);
v_res_3317_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3305_, v_e_3306_, v_k_3307_, v_cleanupAnnotations_boxed_3316_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3318_, lean_object* v___x_3319_, lean_object* v___x_3320_, lean_object* v_x_3321_, uint8_t v___x_3322_, lean_object* v_xs_3323_, lean_object* v_type_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = l_Lean_LocalDecl_type(v_a_3318_);
v___x_3333_ = lean_array_get_borrowed(v___x_3319_, v_xs_3323_, v___x_3320_);
v___x_3334_ = l_Lean_Expr_replaceFVar(v___x_3332_, v_x_3321_, v___x_3333_);
lean_dec_ref(v___x_3332_);
v___x_3335_ = l_Lean_mkArrow(v___x_3334_, v_type_3324_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; uint8_t v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_n(v_a_3336_, 2);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = 0;
v___x_3338_ = 1;
v___x_3339_ = l_Lean_Meta_mkLambdaFVars(v_xs_3323_, v_a_3336_, v___x_3337_, v___x_3322_, v___x_3337_, v___x_3322_, v___x_3338_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = l_Lean_Meta_getLevel(v_a_3336_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_a_3340_);
lean_ctor_set(v___x_3346_, 1, v_a_3342_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3340_);
v_a_3351_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3341_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3341_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_a_3336_);
v_a_3359_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3339_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3339_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3335_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3335_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v_x_3378_, lean_object* v___x_3379_, lean_object* v_xs_3380_, lean_object* v_type_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v___x_6245__boxed_3389_; lean_object* v_res_3390_; 
v___x_6245__boxed_3389_ = lean_unbox(v___x_3379_);
v_res_3390_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3375_, v___x_3376_, v___x_3377_, v_x_3378_, v___x_6245__boxed_3389_, v_xs_3380_, v_type_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v_xs_3380_);
lean_dec(v___x_3377_);
lean_dec_ref(v___x_3376_);
lean_dec_ref(v_a_3375_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
lean_inc(v___y_3398_);
lean_inc_ref(v___y_3397_);
lean_inc(v___y_3396_);
lean_inc_ref(v___y_3395_);
lean_inc(v___y_3393_);
lean_inc_ref(v___y_3392_);
v___x_3400_ = lean_apply_8(v_k_3391_, v_b_3394_, v___y_3392_, v___y_3393_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, lean_box(0));
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3401_, v___y_3402_, v___y_3403_, v_b_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3411_, uint8_t v_bi_3412_, lean_object* v_type_3413_, lean_object* v_k_3414_, uint8_t v_kind_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___f_3423_; lean_object* v___x_3424_; 
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
v___f_3423_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3423_, 0, v_k_3414_);
lean_closure_set(v___f_3423_, 1, v___y_3416_);
lean_closure_set(v___f_3423_, 2, v___y_3417_);
v___x_3424_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3411_, v_bi_3412_, v_type_3413_, v___f_3423_, v_kind_3415_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3424_) == 0)
{
return v___x_3424_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3433_, lean_object* v_bi_3434_, lean_object* v_type_3435_, lean_object* v_k_3436_, lean_object* v_kind_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v_bi_boxed_3445_; uint8_t v_kind_boxed_3446_; lean_object* v_res_3447_; 
v_bi_boxed_3445_ = lean_unbox(v_bi_3434_);
v_kind_boxed_3446_ = lean_unbox(v_kind_3437_);
v_res_3447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3433_, v_bi_boxed_3445_, v_type_3435_, v_k_3436_, v_kind_boxed_3446_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3448_, lean_object* v_type_3449_, lean_object* v_k_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
uint8_t v___x_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = 0;
v___x_3459_ = 0;
v___x_3460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3448_, v___x_3458_, v_type_3449_, v_k_3450_, v___x_3459_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3461_, lean_object* v_type_3462_, lean_object* v_k_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3461_, v_type_3462_, v_k_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3485_, lean_object* v_F_3486_, lean_object* v_val_3487_, lean_object* v_k_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3496_; uint8_t v___y_3498_; uint8_t v___x_3612_; 
v___x_3496_ = l_Lean_instInhabitedExpr;
v___x_3612_ = l_Lean_Expr_isFVar(v_x_3485_);
if (v___x_3612_ == 0)
{
v___y_3498_ = v___x_3612_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3613_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3614_ = lean_unsigned_to_nat(6u);
v___x_3615_ = l_Lean_Expr_isAppOfArity(v_val_3487_, v___x_3613_, v___x_3614_);
v___y_3498_ = v___x_3615_;
goto v___jp_3497_;
}
v___jp_3497_:
{
if (v___y_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
v___x_3499_ = lean_apply_10(v_k_3488_, v_x_3485_, v_F_3486_, v_val_3487_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, lean_box(0));
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3500_ = lean_unsigned_to_nat(3u);
v___x_3501_ = l_Lean_Expr_getAppNumArgs(v_val_3487_);
v___x_3502_ = lean_nat_sub(v___x_3501_, v___x_3500_);
v___x_3503_ = lean_unsigned_to_nat(1u);
v___x_3504_ = lean_nat_sub(v___x_3502_, v___x_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = l_Lean_Expr_getRevArg_x21(v_val_3487_, v___x_3504_);
v___x_3506_ = lean_expr_eqv(v___x_3505_, v_x_3485_);
lean_dec_ref(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v___x_3501_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
v___x_3507_ = lean_apply_10(v_k_3488_, v_x_3485_, v_F_3486_, v_val_3487_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, lean_box(0));
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3508_ = lean_unsigned_to_nat(4u);
v___x_3509_ = lean_nat_sub(v___x_3501_, v___x_3508_);
v___x_3510_ = lean_nat_sub(v___x_3509_, v___x_3503_);
lean_dec(v___x_3509_);
v___x_3511_ = l_Lean_Expr_getRevArg_x21(v_val_3487_, v___x_3510_);
v___x_3512_ = l_Lean_Expr_isLambda(v___x_3511_);
lean_dec_ref(v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec(v___x_3501_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
v___x_3513_ = lean_apply_10(v_k_3488_, v_x_3485_, v_F_3486_, v_val_3487_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, lean_box(0));
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3514_ = lean_unsigned_to_nat(5u);
v___x_3515_ = lean_nat_sub(v___x_3501_, v___x_3514_);
v___x_3516_ = lean_nat_sub(v___x_3515_, v___x_3503_);
lean_dec(v___x_3515_);
v___x_3517_ = l_Lean_Expr_getRevArg_x21(v_val_3487_, v___x_3516_);
v___x_3518_ = l_Lean_Expr_isLambda(v___x_3517_);
lean_dec_ref(v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec(v___x_3501_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
v___x_3519_ = lean_apply_10(v_k_3488_, v_x_3485_, v_F_3486_, v_val_3487_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, lean_box(0));
return v___x_3519_;
}
else
{
lean_object* v_dummy_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v_args_3523_; lean_object* v___x_3524_; lean_object* v_00_u03b1_3525_; lean_object* v_00_u03b2_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_dummy_3520_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3501_);
v___x_3521_ = lean_mk_array(v___x_3501_, v_dummy_3520_);
v___x_3522_ = lean_nat_sub(v___x_3501_, v___x_3503_);
lean_dec(v___x_3501_);
v_args_3523_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3487_, v___x_3521_, v___x_3522_);
v___x_3524_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3525_ = lean_array_get(v___x_3496_, v_args_3523_, v___x_3524_);
v_00_u03b2_3526_ = lean_array_get(v___x_3496_, v_args_3523_, v___x_3503_);
v___x_3527_ = l_Lean_Expr_fvarId_x21(v_F_3486_);
v___x_3528_ = l_Lean_FVarId_getDecl___redArg(v___x_3527_, v_a_3491_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; lean_object* v___f_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc_n(v_a_3529_, 2);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = lean_box(v___x_3512_);
lean_inc_ref(v_x_3485_);
v___f_3531_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3531_, 0, v_a_3529_);
lean_closure_set(v___f_3531_, 1, v___x_3496_);
lean_closure_set(v___f_3531_, 2, v___x_3524_);
lean_closure_set(v___f_3531_, 3, v_x_3485_);
lean_closure_set(v___f_3531_, 4, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(2u);
v___x_3533_ = lean_array_get_borrowed(v___x_3496_, v_args_3523_, v___x_3532_);
v___x_3534_ = 0;
lean_inc(v___x_3533_);
v___x_3535_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3533_, v___f_3531_, v___x_3534_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v_fst_3537_; lean_object* v_snd_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3595_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v_fst_3537_ = lean_ctor_get(v_a_3536_, 0);
v_snd_3538_ = lean_ctor_get(v_a_3536_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3536_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3540_ = v_a_3536_;
v_isShared_3541_ = v_isSharedCheck_3595_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_snd_3538_);
lean_inc(v_fst_3537_);
lean_dec(v_a_3536_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3595_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3543_ = lean_array_get_borrowed(v___x_3496_, v_args_3523_, v___x_3508_);
lean_inc(v___x_3543_);
lean_inc_ref(v_x_3485_);
lean_inc(v_a_3529_);
lean_inc(v_00_u03b2_3526_);
lean_inc(v_00_u03b1_3525_);
lean_inc_ref(v_k_3488_);
v___x_3544_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3496_, v___x_3524_, v_k_3488_, v___x_3532_, v___x_3534_, v___x_3512_, v_00_u03b1_3525_, v_00_u03b2_3526_, v___x_3500_, v_a_3529_, v_x_3485_, v___x_3503_, v___x_3542_, v___x_3543_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3547_ = lean_array_get(v___x_3496_, v_args_3523_, v___x_3514_);
lean_dec_ref(v_args_3523_);
lean_inc_ref(v_x_3485_);
lean_inc(v_00_u03b2_3526_);
lean_inc(v_00_u03b1_3525_);
v___x_3548_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3496_, v___x_3524_, v_k_3488_, v___x_3532_, v___x_3534_, v___x_3512_, v_00_u03b1_3525_, v_00_u03b2_3526_, v___x_3500_, v_a_3529_, v_x_3485_, v___x_3503_, v___x_3546_, v___x_3547_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
lean_inc(v_00_u03b1_3525_);
v___x_3550_ = l_Lean_Meta_getLevel(v_00_u03b1_3525_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
lean_inc(v_00_u03b2_3526_);
v___x_3552_ = l_Lean_Meta_getLevel(v_00_u03b2_3526_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3578_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3578_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3578_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3558_ = lean_box(0);
if (v_isShared_3541_ == 0)
{
lean_ctor_set_tag(v___x_3540_, 1);
lean_ctor_set(v___x_3540_, 1, v___x_3558_);
lean_ctor_set(v___x_3540_, 0, v_a_3553_);
v___x_3560_ = v___x_3540_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3553_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3561_, 0, v_a_3551_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3562_, 0, v_snd_3538_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = l_Lean_mkConst(v___x_3557_, v___x_3562_);
v___x_3564_ = lean_unsigned_to_nat(7u);
v___x_3565_ = lean_mk_empty_array_with_capacity(v___x_3564_);
v___x_3566_ = lean_array_push(v___x_3565_, v_00_u03b1_3525_);
v___x_3567_ = lean_array_push(v___x_3566_, v_00_u03b2_3526_);
v___x_3568_ = lean_array_push(v___x_3567_, v_fst_3537_);
v___x_3569_ = lean_array_push(v___x_3568_, v_x_3485_);
v___x_3570_ = lean_array_push(v___x_3569_, v_a_3545_);
v___x_3571_ = lean_array_push(v___x_3570_, v_a_3549_);
v___x_3572_ = lean_array_push(v___x_3571_, v_F_3486_);
v___x_3573_ = l_Lean_mkAppN(v___x_3563_, v___x_3572_);
lean_dec_ref(v___x_3572_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3573_);
v___x_3575_ = v___x_3555_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_a_3551_);
lean_dec(v_a_3549_);
lean_dec(v_a_3545_);
lean_del_object(v___x_3540_);
lean_dec(v_snd_3538_);
lean_dec(v_fst_3537_);
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
v_a_3579_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3552_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3552_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v_a_3549_);
lean_dec(v_a_3545_);
lean_del_object(v___x_3540_);
lean_dec(v_snd_3538_);
lean_dec(v_fst_3537_);
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
v_a_3587_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3550_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3550_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_dec(v_a_3545_);
lean_del_object(v___x_3540_);
lean_dec(v_snd_3538_);
lean_dec(v_fst_3537_);
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
return v___x_3548_;
}
}
else
{
lean_del_object(v___x_3540_);
lean_dec(v_snd_3538_);
lean_dec(v_fst_3537_);
lean_dec(v_a_3529_);
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_args_3523_);
lean_dec_ref(v_k_3488_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
return v___x_3544_;
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3529_);
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_args_3523_);
lean_dec_ref(v_k_3488_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
v_a_3596_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3535_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3535_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v_00_u03b2_3526_);
lean_dec(v_00_u03b1_3525_);
lean_dec_ref(v_args_3523_);
lean_dec_ref(v_k_3488_);
lean_dec_ref(v_F_3486_);
lean_dec_ref(v_x_3485_);
v_a_3604_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3528_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3528_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3616_, lean_object* v_body_3617_, lean_object* v_k_3618_, lean_object* v___x_3619_, uint8_t v___x_3620_, uint8_t v___x_3621_, lean_object* v_FNew_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
lean_inc_ref(v_FNew_3622_);
lean_inc_ref(v___x_3616_);
v___x_3630_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3616_, v_FNew_3622_, v_body_3617_, v_k_3618_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; lean_object* v___x_3636_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v___x_3632_ = lean_mk_empty_array_with_capacity(v___x_3619_);
v___x_3633_ = lean_array_push(v___x_3632_, v___x_3616_);
v___x_3634_ = lean_array_push(v___x_3633_, v_FNew_3622_);
v___x_3635_ = 1;
v___x_3636_ = l_Lean_Meta_mkLambdaFVars(v___x_3634_, v_a_3631_, v___x_3620_, v___x_3621_, v___x_3620_, v___x_3621_, v___x_3635_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec_ref(v___x_3634_);
return v___x_3636_;
}
else
{
lean_dec_ref(v_FNew_3622_);
lean_dec_ref(v___x_3616_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3637_, lean_object* v_body_3638_, lean_object* v_k_3639_, lean_object* v___x_3640_, lean_object* v___x_3641_, lean_object* v___x_3642_, lean_object* v_FNew_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v___x_6491__boxed_3651_; uint8_t v___x_6492__boxed_3652_; lean_object* v_res_3653_; 
v___x_6491__boxed_3651_ = lean_unbox(v___x_3641_);
v___x_6492__boxed_3652_ = lean_unbox(v___x_3642_);
v_res_3653_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3637_, v_body_3638_, v_k_3639_, v___x_3640_, v___x_6491__boxed_3651_, v___x_6492__boxed_3652_, v_FNew_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___x_3640_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3654_, lean_object* v___x_3655_, lean_object* v_k_3656_, lean_object* v___x_3657_, uint8_t v___x_3658_, uint8_t v___x_3659_, lean_object* v_00_u03b1_3660_, lean_object* v_00_u03b2_3661_, lean_object* v___x_3662_, lean_object* v_ctorName_3663_, lean_object* v_a_3664_, lean_object* v_x_3665_, lean_object* v_xs_3666_, lean_object* v_body_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3675_ = lean_array_get_borrowed(v___x_3654_, v_xs_3666_, v___x_3655_);
v___x_3676_ = lean_box(v___x_3658_);
v___x_3677_ = lean_box(v___x_3659_);
lean_inc_n(v___x_3675_, 2);
v___f_3678_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3678_, 0, v___x_3675_);
lean_closure_set(v___f_3678_, 1, v_body_3667_);
lean_closure_set(v___f_3678_, 2, v_k_3656_);
lean_closure_set(v___f_3678_, 3, v___x_3657_);
lean_closure_set(v___f_3678_, 4, v___x_3676_);
lean_closure_set(v___f_3678_, 5, v___x_3677_);
v___x_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_00_u03b1_3660_);
v___x_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_00_u03b2_3661_);
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3675_);
v___x_3682_ = lean_mk_empty_array_with_capacity(v___x_3662_);
v___x_3683_ = lean_array_push(v___x_3682_, v___x_3679_);
v___x_3684_ = lean_array_push(v___x_3683_, v___x_3680_);
v___x_3685_ = lean_array_push(v___x_3684_, v___x_3681_);
v___x_3686_ = l_Lean_Meta_mkAppOptM(v_ctorName_3663_, v___x_3685_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3688_ = l_Lean_LocalDecl_type(v_a_3664_);
v___x_3689_ = l_Lean_Expr_replaceFVar(v___x_3688_, v_x_3665_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v___x_3688_);
v___x_3690_ = l_Lean_LocalDecl_userName(v_a_3664_);
v___x_3691_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3690_, v___x_3689_, v___f_3678_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
return v___x_3691_;
}
else
{
lean_dec_ref(v___f_3678_);
lean_dec_ref(v_x_3665_);
return v___x_3686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3692_ = _args[0];
lean_object* v___x_3693_ = _args[1];
lean_object* v_k_3694_ = _args[2];
lean_object* v___x_3695_ = _args[3];
lean_object* v___x_3696_ = _args[4];
lean_object* v___x_3697_ = _args[5];
lean_object* v_00_u03b1_3698_ = _args[6];
lean_object* v_00_u03b2_3699_ = _args[7];
lean_object* v___x_3700_ = _args[8];
lean_object* v_ctorName_3701_ = _args[9];
lean_object* v_a_3702_ = _args[10];
lean_object* v_x_3703_ = _args[11];
lean_object* v_xs_3704_ = _args[12];
lean_object* v_body_3705_ = _args[13];
lean_object* v___y_3706_ = _args[14];
lean_object* v___y_3707_ = _args[15];
lean_object* v___y_3708_ = _args[16];
lean_object* v___y_3709_ = _args[17];
lean_object* v___y_3710_ = _args[18];
lean_object* v___y_3711_ = _args[19];
lean_object* v___y_3712_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3713_; uint8_t v___x_6512__boxed_3714_; lean_object* v_res_3715_; 
v___x_6511__boxed_3713_ = lean_unbox(v___x_3696_);
v___x_6512__boxed_3714_ = lean_unbox(v___x_3697_);
v_res_3715_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3692_, v___x_3693_, v_k_3694_, v___x_3695_, v___x_6511__boxed_3713_, v___x_6512__boxed_3714_, v_00_u03b1_3698_, v_00_u03b2_3699_, v___x_3700_, v_ctorName_3701_, v_a_3702_, v_x_3703_, v_xs_3704_, v_body_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_xs_3704_);
lean_dec_ref(v_a_3702_);
lean_dec(v___x_3700_);
lean_dec(v___x_3693_);
lean_dec_ref(v___x_3692_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3716_, lean_object* v___x_3717_, lean_object* v_k_3718_, lean_object* v___x_3719_, uint8_t v___x_3720_, uint8_t v___x_3721_, lean_object* v_00_u03b1_3722_, lean_object* v_00_u03b2_3723_, lean_object* v___x_3724_, lean_object* v_a_3725_, lean_object* v_x_3726_, lean_object* v___x_3727_, lean_object* v_ctorName_3728_, lean_object* v_minor_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___f_3739_; lean_object* v___x_3740_; 
v___x_3737_ = lean_box(v___x_3720_);
v___x_3738_ = lean_box(v___x_3721_);
v___f_3739_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3739_, 0, v___x_3716_);
lean_closure_set(v___f_3739_, 1, v___x_3717_);
lean_closure_set(v___f_3739_, 2, v_k_3718_);
lean_closure_set(v___f_3739_, 3, v___x_3719_);
lean_closure_set(v___f_3739_, 4, v___x_3737_);
lean_closure_set(v___f_3739_, 5, v___x_3738_);
lean_closure_set(v___f_3739_, 6, v_00_u03b1_3722_);
lean_closure_set(v___f_3739_, 7, v_00_u03b2_3723_);
lean_closure_set(v___f_3739_, 8, v___x_3724_);
lean_closure_set(v___f_3739_, 9, v_ctorName_3728_);
lean_closure_set(v___f_3739_, 10, v_a_3725_);
lean_closure_set(v___f_3739_, 11, v_x_3726_);
v___x_3740_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3729_, v___x_3727_, v___f_3739_, v___x_3720_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3741_ = _args[0];
lean_object* v___x_3742_ = _args[1];
lean_object* v_k_3743_ = _args[2];
lean_object* v___x_3744_ = _args[3];
lean_object* v___x_3745_ = _args[4];
lean_object* v___x_3746_ = _args[5];
lean_object* v_00_u03b1_3747_ = _args[6];
lean_object* v_00_u03b2_3748_ = _args[7];
lean_object* v___x_3749_ = _args[8];
lean_object* v_a_3750_ = _args[9];
lean_object* v_x_3751_ = _args[10];
lean_object* v___x_3752_ = _args[11];
lean_object* v_ctorName_3753_ = _args[12];
lean_object* v_minor_3754_ = _args[13];
lean_object* v___y_3755_ = _args[14];
lean_object* v___y_3756_ = _args[15];
lean_object* v___y_3757_ = _args[16];
lean_object* v___y_3758_ = _args[17];
lean_object* v___y_3759_ = _args[18];
lean_object* v___y_3760_ = _args[19];
lean_object* v___y_3761_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3762_; uint8_t v___x_6476__boxed_3763_; lean_object* v_res_3764_; 
v___x_6475__boxed_3762_ = lean_unbox(v___x_3745_);
v___x_6476__boxed_3763_ = lean_unbox(v___x_3746_);
v_res_3764_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3741_, v___x_3742_, v_k_3743_, v___x_3744_, v___x_6475__boxed_3762_, v___x_6476__boxed_3763_, v_00_u03b1_3747_, v_00_u03b2_3748_, v___x_3749_, v_a_3750_, v_x_3751_, v___x_3752_, v_ctorName_3753_, v_minor_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3765_, lean_object* v_F_3766_, lean_object* v_val_3767_, lean_object* v_k_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3765_, v_F_3766_, v_val_3767_, v_k_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3777_, lean_object* v_name_3778_, uint8_t v_bi_3779_, lean_object* v_type_3780_, lean_object* v_k_3781_, uint8_t v_kind_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3778_, v_bi_3779_, v_type_3780_, v_k_3781_, v_kind_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3791_, lean_object* v_name_3792_, lean_object* v_bi_3793_, lean_object* v_type_3794_, lean_object* v_k_3795_, lean_object* v_kind_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
uint8_t v_bi_boxed_3804_; uint8_t v_kind_boxed_3805_; lean_object* v_res_3806_; 
v_bi_boxed_3804_ = lean_unbox(v_bi_3793_);
v_kind_boxed_3805_ = lean_unbox(v_kind_3796_);
v_res_3806_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3791_, v_name_3792_, v_bi_boxed_3804_, v_type_3794_, v_k_3795_, v_kind_boxed_3805_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3807_, lean_object* v_name_3808_, lean_object* v_type_3809_, lean_object* v_k_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3808_, v_type_3809_, v_k_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3819_, lean_object* v_name_3820_, lean_object* v_type_3821_, lean_object* v_k_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3819_, v_name_3820_, v_type_3821_, v_k_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3830_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3331__overap_3841_; lean_object* v___x_3842_; 
v___x_3840_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3841_ = lean_panic_fn_borrowed(v___x_3840_, v_msg_3832_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
v___x_3842_ = lean_apply_7(v___x_3331__overap_3841_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, lean_box(0));
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3851_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3855_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3856_ = lean_unsigned_to_nat(49u);
v___x_3857_ = lean_unsigned_to_nat(186u);
v___x_3858_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3860_ = l_mkPanicMessageWithDecl(v___x_3859_, v___x_3858_, v___x_3857_, v___x_3856_, v___x_3855_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3861_, lean_object* v_a_3862_, lean_object* v_k_3863_, lean_object* v___x_3864_, lean_object* v___x_3865_, lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v___x_3868_, lean_object* v_FNew_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
uint8_t v___x_3506__boxed_3877_; uint8_t v___x_3507__boxed_3878_; uint8_t v___x_3508__boxed_3879_; lean_object* v_res_3880_; 
v___x_3506__boxed_3877_ = lean_unbox(v___x_3866_);
v___x_3507__boxed_3878_ = lean_unbox(v___x_3867_);
v___x_3508__boxed_3879_ = lean_unbox(v___x_3868_);
v_res_3880_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3861_, v_a_3862_, v_k_3863_, v___x_3864_, v___x_3865_, v___x_3506__boxed_3877_, v___x_3507__boxed_3878_, v___x_3508__boxed_3879_, v_FNew_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___x_3864_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v___x_3889_, uint8_t v___x_3890_, uint8_t v___x_3891_, lean_object* v_k_3892_, lean_object* v___x_3893_, lean_object* v_00_u03b1_3894_, lean_object* v_00_u03b2_3895_, lean_object* v___x_3896_, lean_object* v_a_3897_, lean_object* v_x_3898_, lean_object* v_xs_3899_, lean_object* v_body_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; 
v___x_3908_ = lean_array_get(v___x_3886_, v_xs_3899_, v___x_3887_);
v___x_3909_ = lean_array_get(v___x_3886_, v_xs_3899_, v___x_3888_);
v___x_3910_ = lean_array_get_size(v_xs_3899_);
v___x_3911_ = l_Array_toSubarray___redArg(v_xs_3899_, v___x_3889_, v___x_3910_);
v___x_3912_ = l_Subarray_copy___redArg(v___x_3911_);
v___x_3913_ = 1;
v___x_3914_ = l_Lean_Meta_mkLambdaFVars(v___x_3912_, v_body_3900_, v___x_3890_, v___x_3891_, v___x_3890_, v___x_3891_, v___x_3913_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec_ref(v___x_3912_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3941_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3917_ = v___x_3914_;
v_isShared_3918_ = v_isSharedCheck_3941_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3941_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___f_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3919_ = lean_box(v___x_3890_);
v___x_3920_ = lean_box(v___x_3891_);
v___x_3921_ = lean_box(v___x_3913_);
lean_inc(v___x_3908_);
lean_inc(v___x_3909_);
v___f_3922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3922_, 0, v___x_3909_);
lean_closure_set(v___f_3922_, 1, v_a_3915_);
lean_closure_set(v___f_3922_, 2, v_k_3892_);
lean_closure_set(v___f_3922_, 3, v___x_3893_);
lean_closure_set(v___f_3922_, 4, v___x_3908_);
lean_closure_set(v___f_3922_, 5, v___x_3919_);
lean_closure_set(v___f_3922_, 6, v___x_3920_);
lean_closure_set(v___f_3922_, 7, v___x_3921_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3918_ == 0)
{
lean_ctor_set_tag(v___x_3917_, 1);
lean_ctor_set(v___x_3917_, 0, v_00_u03b1_3894_);
v___x_3925_ = v___x_3917_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_00_u03b1_3894_);
v___x_3925_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_00_u03b2_3895_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3908_);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3909_);
v___x_3929_ = lean_mk_empty_array_with_capacity(v___x_3896_);
v___x_3930_ = lean_array_push(v___x_3929_, v___x_3925_);
v___x_3931_ = lean_array_push(v___x_3930_, v___x_3926_);
v___x_3932_ = lean_array_push(v___x_3931_, v___x_3927_);
v___x_3933_ = lean_array_push(v___x_3932_, v___x_3928_);
v___x_3934_ = l_Lean_Meta_mkAppOptM(v___x_3923_, v___x_3933_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = l_Lean_LocalDecl_type(v_a_3897_);
v___x_3937_ = l_Lean_Expr_replaceFVar(v___x_3936_, v_x_3898_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v___x_3936_);
v___x_3938_ = l_Lean_LocalDecl_userName(v_a_3897_);
v___x_3939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3938_, v___x_3937_, v___f_3922_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
return v___x_3939_;
}
else
{
lean_dec_ref(v___f_3922_);
lean_dec_ref(v_x_3898_);
return v___x_3934_;
}
}
}
}
else
{
lean_dec(v___x_3909_);
lean_dec(v___x_3908_);
lean_dec_ref(v_x_3898_);
lean_dec_ref(v_00_u03b2_3895_);
lean_dec_ref(v_00_u03b1_3894_);
lean_dec(v___x_3893_);
lean_dec_ref(v_k_3892_);
return v___x_3914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3942_ = _args[0];
lean_object* v___x_3943_ = _args[1];
lean_object* v___x_3944_ = _args[2];
lean_object* v___x_3945_ = _args[3];
lean_object* v___x_3946_ = _args[4];
lean_object* v___x_3947_ = _args[5];
lean_object* v_k_3948_ = _args[6];
lean_object* v___x_3949_ = _args[7];
lean_object* v_00_u03b1_3950_ = _args[8];
lean_object* v_00_u03b2_3951_ = _args[9];
lean_object* v___x_3952_ = _args[10];
lean_object* v_a_3953_ = _args[11];
lean_object* v_x_3954_ = _args[12];
lean_object* v_xs_3955_ = _args[13];
lean_object* v_body_3956_ = _args[14];
lean_object* v___y_3957_ = _args[15];
lean_object* v___y_3958_ = _args[16];
lean_object* v___y_3959_ = _args[17];
lean_object* v___y_3960_ = _args[18];
lean_object* v___y_3961_ = _args[19];
lean_object* v___y_3962_ = _args[20];
lean_object* v___y_3963_ = _args[21];
_start:
{
uint8_t v___x_3533__boxed_3964_; uint8_t v___x_3534__boxed_3965_; lean_object* v_res_3966_; 
v___x_3533__boxed_3964_ = lean_unbox(v___x_3946_);
v___x_3534__boxed_3965_ = lean_unbox(v___x_3947_);
v_res_3966_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3942_, v___x_3943_, v___x_3944_, v___x_3945_, v___x_3533__boxed_3964_, v___x_3534__boxed_3965_, v_k_3948_, v___x_3949_, v_00_u03b1_3950_, v_00_u03b2_3951_, v___x_3952_, v_a_3953_, v_x_3954_, v_xs_3955_, v_body_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec_ref(v_a_3953_);
lean_dec(v___x_3952_);
lean_dec(v___x_3944_);
lean_dec(v___x_3943_);
lean_dec_ref(v___x_3942_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3970_, lean_object* v_F_3971_, lean_object* v_val_3972_, lean_object* v_k_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___x_3990_; uint8_t v___y_3992_; uint8_t v___x_4083_; 
v___x_3990_ = l_Lean_instInhabitedExpr;
v___x_4083_ = l_Lean_Expr_isFVar(v_x_3970_);
if (v___x_4083_ == 0)
{
v___y_3992_ = v___x_4083_;
goto v___jp_3991_;
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v___x_4084_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4085_ = lean_unsigned_to_nat(5u);
v___x_4086_ = l_Lean_Expr_isAppOfArity(v_val_3972_, v___x_4084_, v___x_4085_);
v___y_3992_ = v___x_4086_;
goto v___jp_3991_;
}
v___jp_3981_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3989_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3988_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
v___jp_3991_:
{
if (v___y_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec_ref(v_x_3970_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
lean_inc(v_a_3977_);
lean_inc_ref(v_a_3976_);
lean_inc(v_a_3975_);
lean_inc_ref(v_a_3974_);
v___x_3993_ = lean_apply_9(v_k_3973_, v_F_3971_, v_val_3972_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, lean_box(0));
return v___x_3993_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3994_ = lean_unsigned_to_nat(3u);
v___x_3995_ = l_Lean_Expr_getAppNumArgs(v_val_3972_);
v___x_3996_ = lean_nat_sub(v___x_3995_, v___x_3994_);
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_sub(v___x_3996_, v___x_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = l_Lean_Expr_getRevArg_x21(v_val_3972_, v___x_3998_);
v___x_4000_ = lean_expr_eqv(v___x_3999_, v_x_3970_);
lean_dec_ref(v___x_3999_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v___x_3995_);
lean_dec_ref(v_x_3970_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
lean_inc(v_a_3977_);
lean_inc_ref(v_a_3976_);
lean_inc(v_a_3975_);
lean_inc_ref(v_a_3974_);
v___x_4001_ = lean_apply_9(v_k_3973_, v_F_3971_, v_val_3972_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, lean_box(0));
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_4002_ = lean_unsigned_to_nat(4u);
v___x_4003_ = lean_nat_sub(v___x_3995_, v___x_4002_);
v___x_4004_ = lean_nat_sub(v___x_4003_, v___x_3997_);
lean_dec(v___x_4003_);
v___x_4005_ = l_Lean_Expr_getRevArg_x21(v_val_3972_, v___x_4004_);
v___x_4006_ = l_Lean_Expr_isLambda(v___x_4005_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_dec_ref(v___x_4005_);
lean_dec(v___x_3995_);
lean_dec_ref(v_x_3970_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
lean_inc(v_a_3977_);
lean_inc_ref(v_a_3976_);
lean_inc(v_a_3975_);
lean_inc_ref(v_a_3974_);
v___x_4007_ = lean_apply_9(v_k_3973_, v_F_3971_, v_val_3972_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, lean_box(0));
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4008_ = l_Lean_Expr_bindingBody_x21(v___x_4005_);
lean_dec_ref(v___x_4005_);
v___x_4009_ = l_Lean_Expr_isLambda(v___x_4008_);
lean_dec_ref(v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v___x_3995_);
lean_dec_ref(v_x_3970_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
lean_inc(v_a_3977_);
lean_inc_ref(v_a_3976_);
lean_inc(v_a_3975_);
lean_inc_ref(v_a_3974_);
v___x_4010_ = lean_apply_9(v_k_3973_, v_F_3971_, v_val_3972_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, lean_box(0));
return v___x_4010_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = l_Lean_Expr_getAppFn(v_val_3972_);
v___x_4012_ = l_Lean_Expr_constLevels_x21(v___x_4011_);
lean_dec_ref(v___x_4011_);
if (lean_obj_tag(v___x_4012_) == 1)
{
lean_object* v_tail_4013_; 
v_tail_4013_ = lean_ctor_get(v___x_4012_, 1);
lean_inc(v_tail_4013_);
lean_dec_ref_known(v___x_4012_, 2);
if (lean_obj_tag(v_tail_4013_) == 1)
{
lean_object* v_tail_4014_; 
v_tail_4014_ = lean_ctor_get(v_tail_4013_, 1);
lean_inc(v_tail_4014_);
if (lean_obj_tag(v_tail_4014_) == 1)
{
lean_object* v_tail_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4081_; 
v_tail_4015_ = lean_ctor_get(v_tail_4014_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_tail_4014_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v_tail_4014_, 0);
lean_dec(v_unused_4082_);
v___x_4017_ = v_tail_4014_;
v_isShared_4018_ = v_isSharedCheck_4081_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_tail_4015_);
lean_dec(v_tail_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4081_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
if (lean_obj_tag(v_tail_4015_) == 0)
{
lean_object* v_dummy_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v_args_4022_; lean_object* v___x_4023_; lean_object* v_00_u03b1_4024_; lean_object* v_00_u03b2_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_dummy_4019_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3995_);
v___x_4020_ = lean_mk_array(v___x_3995_, v_dummy_4019_);
v___x_4021_ = lean_nat_sub(v___x_3995_, v___x_3997_);
lean_dec(v___x_3995_);
v_args_4022_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3972_, v___x_4020_, v___x_4021_);
v___x_4023_ = lean_unsigned_to_nat(0u);
v_00_u03b1_4024_ = lean_array_get(v___x_3990_, v_args_4022_, v___x_4023_);
v_00_u03b2_4025_ = lean_array_get(v___x_3990_, v_args_4022_, v___x_3997_);
v___x_4026_ = l_Lean_Expr_fvarId_x21(v_F_3971_);
v___x_4027_ = l_Lean_FVarId_getDecl___redArg(v___x_4026_, v_a_3976_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; lean_object* v___f_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___f_4036_; lean_object* v___x_4037_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc_n(v_a_4028_, 2);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_box(v___x_4006_);
lean_inc_ref_n(v_x_3970_, 2);
v___f_4030_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4030_, 0, v_a_4028_);
lean_closure_set(v___f_4030_, 1, v___x_3990_);
lean_closure_set(v___f_4030_, 2, v___x_4023_);
lean_closure_set(v___f_4030_, 3, v_x_3970_);
lean_closure_set(v___f_4030_, 4, v___x_4029_);
v___x_4031_ = lean_unsigned_to_nat(2u);
v___x_4032_ = lean_array_get_borrowed(v___x_3990_, v_args_4022_, v___x_4031_);
v___x_4033_ = 0;
v___x_4034_ = lean_box(v___x_4033_);
v___x_4035_ = lean_box(v___x_4006_);
lean_inc(v_00_u03b2_4025_);
lean_inc(v_00_u03b1_4024_);
v___f_4036_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4036_, 0, v___x_3990_);
lean_closure_set(v___f_4036_, 1, v___x_4023_);
lean_closure_set(v___f_4036_, 2, v___x_3997_);
lean_closure_set(v___f_4036_, 3, v___x_4031_);
lean_closure_set(v___f_4036_, 4, v___x_4034_);
lean_closure_set(v___f_4036_, 5, v___x_4035_);
lean_closure_set(v___f_4036_, 6, v_k_3973_);
lean_closure_set(v___f_4036_, 7, v___x_3994_);
lean_closure_set(v___f_4036_, 8, v_00_u03b1_4024_);
lean_closure_set(v___f_4036_, 9, v_00_u03b2_4025_);
lean_closure_set(v___f_4036_, 10, v___x_4002_);
lean_closure_set(v___f_4036_, 11, v_a_4028_);
lean_closure_set(v___f_4036_, 12, v_x_3970_);
lean_inc(v___x_4032_);
v___x_4037_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4032_, v___f_4030_, v___x_4033_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_fst_4039_; lean_object* v_snd_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v_fst_4039_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_fst_4039_);
v_snd_4040_ = lean_ctor_get(v_a_4038_, 1);
lean_inc(v_snd_4040_);
lean_dec(v_a_4038_);
v___x_4041_ = lean_array_get(v___x_3990_, v_args_4022_, v___x_4002_);
lean_dec_ref(v_args_4022_);
v___x_4042_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4041_, v___f_4036_, v___x_4033_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4064_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4064_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4064_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4047_; lean_object* v___x_4049_; 
v___x_4047_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v_tail_4013_);
lean_ctor_set(v___x_4017_, 0, v_snd_4040_);
v___x_4049_ = v___x_4017_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_snd_4040_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_tail_4013_);
v___x_4049_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4050_ = l_Lean_mkConst(v___x_4047_, v___x_4049_);
v___x_4051_ = lean_unsigned_to_nat(6u);
v___x_4052_ = lean_mk_empty_array_with_capacity(v___x_4051_);
v___x_4053_ = lean_array_push(v___x_4052_, v_00_u03b1_4024_);
v___x_4054_ = lean_array_push(v___x_4053_, v_00_u03b2_4025_);
v___x_4055_ = lean_array_push(v___x_4054_, v_fst_4039_);
v___x_4056_ = lean_array_push(v___x_4055_, v_x_3970_);
v___x_4057_ = lean_array_push(v___x_4056_, v_a_4043_);
v___x_4058_ = lean_array_push(v___x_4057_, v_F_3971_);
v___x_4059_ = l_Lean_mkAppN(v___x_4050_, v___x_4058_);
lean_dec_ref(v___x_4058_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4059_);
v___x_4061_ = v___x_4045_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_dec(v_snd_4040_);
lean_dec(v_fst_4039_);
lean_dec(v_00_u03b2_4025_);
lean_dec(v_00_u03b1_4024_);
lean_del_object(v___x_4017_);
lean_dec_ref_known(v_tail_4013_, 2);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
return v___x_4042_;
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___f_4036_);
lean_dec(v_00_u03b2_4025_);
lean_dec(v_00_u03b1_4024_);
lean_dec_ref(v_args_4022_);
lean_del_object(v___x_4017_);
lean_dec_ref_known(v_tail_4013_, 2);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v_a_4065_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4037_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4037_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_00_u03b2_4025_);
lean_dec(v_00_u03b1_4024_);
lean_dec_ref(v_args_4022_);
lean_del_object(v___x_4017_);
lean_dec_ref_known(v_tail_4013_, 2);
lean_dec_ref(v_k_3973_);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v_a_4073_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4027_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4027_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_del_object(v___x_4017_);
lean_dec(v_tail_4015_);
lean_dec_ref_known(v_tail_4013_, 2);
lean_dec(v___x_3995_);
lean_dec_ref(v_k_3973_);
lean_dec_ref(v_val_3972_);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v___y_3982_ = v_a_3974_;
v___y_3983_ = v_a_3975_;
v___y_3984_ = v_a_3976_;
v___y_3985_ = v_a_3977_;
v___y_3986_ = v_a_3978_;
v___y_3987_ = v_a_3979_;
goto v___jp_3981_;
}
}
}
else
{
lean_dec_ref_known(v_tail_4013_, 2);
lean_dec(v_tail_4014_);
lean_dec(v___x_3995_);
lean_dec_ref(v_k_3973_);
lean_dec_ref(v_val_3972_);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v___y_3982_ = v_a_3974_;
v___y_3983_ = v_a_3975_;
v___y_3984_ = v_a_3976_;
v___y_3985_ = v_a_3977_;
v___y_3986_ = v_a_3978_;
v___y_3987_ = v_a_3979_;
goto v___jp_3981_;
}
}
else
{
lean_dec(v_tail_4013_);
lean_dec(v___x_3995_);
lean_dec_ref(v_k_3973_);
lean_dec_ref(v_val_3972_);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v___y_3982_ = v_a_3974_;
v___y_3983_ = v_a_3975_;
v___y_3984_ = v_a_3976_;
v___y_3985_ = v_a_3977_;
v___y_3986_ = v_a_3978_;
v___y_3987_ = v_a_3979_;
goto v___jp_3981_;
}
}
else
{
lean_dec(v___x_4012_);
lean_dec(v___x_3995_);
lean_dec_ref(v_k_3973_);
lean_dec_ref(v_val_3972_);
lean_dec_ref(v_F_3971_);
lean_dec_ref(v_x_3970_);
v___y_3982_ = v_a_3974_;
v___y_3983_ = v_a_3975_;
v___y_3984_ = v_a_3976_;
v___y_3985_ = v_a_3977_;
v___y_3986_ = v_a_3978_;
v___y_3987_ = v_a_3979_;
goto v___jp_3981_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4087_, lean_object* v_a_4088_, lean_object* v_k_4089_, lean_object* v___x_4090_, lean_object* v___x_4091_, uint8_t v___x_4092_, uint8_t v___x_4093_, uint8_t v___x_4094_, lean_object* v_FNew_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
lean_inc_ref(v_FNew_4095_);
lean_inc_ref(v___x_4087_);
v___x_4103_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4087_, v_FNew_4095_, v_a_4088_, v_k_4089_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v___x_4105_ = lean_mk_empty_array_with_capacity(v___x_4090_);
v___x_4106_ = lean_array_push(v___x_4105_, v___x_4091_);
v___x_4107_ = lean_array_push(v___x_4106_, v___x_4087_);
v___x_4108_ = lean_array_push(v___x_4107_, v_FNew_4095_);
v___x_4109_ = l_Lean_Meta_mkLambdaFVars(v___x_4108_, v_a_4104_, v___x_4092_, v___x_4093_, v___x_4092_, v___x_4093_, v___x_4094_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec_ref(v___x_4108_);
return v___x_4109_;
}
else
{
lean_dec_ref(v_FNew_4095_);
lean_dec_ref(v___x_4091_);
lean_dec_ref(v___x_4087_);
return v___x_4103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4110_, lean_object* v_F_4111_, lean_object* v_val_4112_, lean_object* v_k_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4110_, v_F_4111_, v_val_4112_, v_k_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec(v_a_4115_);
lean_dec_ref(v_a_4114_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_ref_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec_ref_known(v___x_4135_, 1);
v_ref_4136_ = lean_ctor_get(v___y_4132_, 2);
v___x_4137_ = 0;
v___x_4138_ = l_Lean_SourceInfo_fromRef(v_ref_4136_, v___x_4137_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4140_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4138_);
v___x_4141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4138_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l_Lean_Syntax_node1(v___x_4138_, v___x_4139_, v___x_4141_);
v___x_4143_ = l_Lean_Elab_Tactic_evalTactic(v___x_4142_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4143_;
}
else
{
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___f_4163_; lean_object* v___x_4164_; 
v___f_4163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4164_ = l_Lean_Elab_Tactic_run(v_mvarId_4155_, v___f_4163_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4175_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
uint8_t v___x_4169_; 
v___x_4169_ = l_List_isEmpty___redArg(v_a_4165_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; 
lean_del_object(v___x_4167_);
v___x_4170_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4165_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4170_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
lean_dec(v_a_4165_);
v___x_4171_ = lean_box(0);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4171_);
v___x_4173_ = v___x_4167_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4164_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4164_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4193_, lean_object* v_x_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
lean_object* v_ks_4197_; lean_object* v_vs_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4222_; 
v_ks_4197_ = lean_ctor_get(v_x_4193_, 0);
v_vs_4198_ = lean_ctor_get(v_x_4193_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_x_4193_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4200_ = v_x_4193_;
v_isShared_4201_ = v_isSharedCheck_4222_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_vs_4198_);
lean_inc(v_ks_4197_);
lean_dec(v_x_4193_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4222_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4202_ = lean_array_get_size(v_ks_4197_);
v___x_4203_ = lean_nat_dec_lt(v_x_4194_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
lean_dec(v_x_4194_);
v___x_4204_ = lean_array_push(v_ks_4197_, v_x_4195_);
v___x_4205_ = lean_array_push(v_vs_4198_, v_x_4196_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4205_);
lean_ctor_set(v___x_4200_, 0, v___x_4204_);
v___x_4207_ = v___x_4200_;
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
else
{
lean_object* v_k_x27_4209_; uint8_t v___x_4210_; 
v_k_x27_4209_ = lean_array_fget_borrowed(v_ks_4197_, v_x_4194_);
v___x_4210_ = l_Lean_instBEqMVarId_beq(v_x_4195_, v_k_x27_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4212_; 
if (v_isShared_4201_ == 0)
{
v___x_4212_ = v___x_4200_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_ks_4197_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_vs_4198_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_unsigned_to_nat(1u);
v___x_4214_ = lean_nat_add(v_x_4194_, v___x_4213_);
lean_dec(v_x_4194_);
v_x_4193_ = v___x_4212_;
v_x_4194_ = v___x_4214_;
goto _start;
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4217_ = lean_array_fset(v_ks_4197_, v_x_4194_, v_x_4195_);
v___x_4218_ = lean_array_fset(v_vs_4198_, v_x_4194_, v_x_4196_);
lean_dec(v_x_4194_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4218_);
lean_ctor_set(v___x_4200_, 0, v___x_4217_);
v___x_4220_ = v___x_4200_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4223_, lean_object* v_k_4224_, lean_object* v_v_4225_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4223_, v___x_4226_, v_k_4224_, v_v_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4229_, size_t v_x_4230_, size_t v_x_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_){
_start:
{
if (lean_obj_tag(v_x_4229_) == 0)
{
lean_object* v_es_4234_; size_t v___x_4235_; size_t v___x_4236_; lean_object* v_j_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v_es_4234_ = lean_ctor_get(v_x_4229_, 0);
v___x_4235_ = ((size_t)31ULL);
v___x_4236_ = lean_usize_land(v_x_4230_, v___x_4235_);
v_j_4237_ = lean_usize_to_nat(v___x_4236_);
v___x_4238_ = lean_array_get_size(v_es_4234_);
v___x_4239_ = lean_nat_dec_lt(v_j_4237_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_dec(v_j_4237_);
lean_dec(v_x_4233_);
lean_dec(v_x_4232_);
return v_x_4229_;
}
else
{
lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4278_; 
lean_inc_ref(v_es_4234_);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_x_4229_);
if (v_isSharedCheck_4278_ == 0)
{
lean_object* v_unused_4279_; 
v_unused_4279_ = lean_ctor_get(v_x_4229_, 0);
lean_dec(v_unused_4279_);
v___x_4241_ = v_x_4229_;
v_isShared_4242_ = v_isSharedCheck_4278_;
goto v_resetjp_4240_;
}
else
{
lean_dec(v_x_4229_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4278_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v_v_4243_; lean_object* v___x_4244_; lean_object* v_xs_x27_4245_; lean_object* v___y_4247_; 
v_v_4243_ = lean_array_fget(v_es_4234_, v_j_4237_);
v___x_4244_ = lean_box(0);
v_xs_x27_4245_ = lean_array_fset(v_es_4234_, v_j_4237_, v___x_4244_);
switch(lean_obj_tag(v_v_4243_))
{
case 0:
{
lean_object* v_key_4252_; lean_object* v_val_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4263_; 
v_key_4252_ = lean_ctor_get(v_v_4243_, 0);
v_val_4253_ = lean_ctor_get(v_v_4243_, 1);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_v_4243_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4255_ = v_v_4243_;
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_val_4253_);
lean_inc(v_key_4252_);
lean_dec(v_v_4243_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
uint8_t v___x_4257_; 
v___x_4257_ = l_Lean_instBEqMVarId_beq(v_x_4232_, v_key_4252_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_del_object(v___x_4255_);
v___x_4258_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4252_, v_val_4253_, v_x_4232_, v_x_4233_);
v___x_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
v___y_4247_ = v___x_4259_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4261_; 
lean_dec(v_val_4253_);
lean_dec(v_key_4252_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 1, v_x_4233_);
lean_ctor_set(v___x_4255_, 0, v_x_4232_);
v___x_4261_ = v___x_4255_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_x_4232_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_x_4233_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
v___y_4247_ = v___x_4261_;
goto v___jp_4246_;
}
}
}
}
case 1:
{
lean_object* v_node_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4276_; 
v_node_4264_ = lean_ctor_get(v_v_4243_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_v_4243_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4266_ = v_v_4243_;
v_isShared_4267_ = v_isSharedCheck_4276_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_node_4264_);
lean_dec(v_v_4243_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4276_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
size_t v___x_4268_; size_t v___x_4269_; size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4268_ = ((size_t)5ULL);
v___x_4269_ = lean_usize_shift_right(v_x_4230_, v___x_4268_);
v___x_4270_ = ((size_t)1ULL);
v___x_4271_ = lean_usize_add(v_x_4231_, v___x_4270_);
v___x_4272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4264_, v___x_4269_, v___x_4271_, v_x_4232_, v_x_4233_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4272_);
v___x_4274_ = v___x_4266_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
v___y_4247_ = v___x_4274_;
goto v___jp_4246_;
}
}
}
default: 
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v_x_4232_);
lean_ctor_set(v___x_4277_, 1, v_x_4233_);
v___y_4247_ = v___x_4277_;
goto v___jp_4246_;
}
}
v___jp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_array_fset(v_xs_x27_4245_, v_j_4237_, v___y_4247_);
lean_dec(v_j_4237_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4248_);
v___x_4250_ = v___x_4241_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
else
{
lean_object* v_ks_4280_; lean_object* v_vs_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4299_; 
v_ks_4280_ = lean_ctor_get(v_x_4229_, 0);
v_vs_4281_ = lean_ctor_get(v_x_4229_, 1);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_x_4229_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4283_ = v_x_4229_;
v_isShared_4284_ = v_isSharedCheck_4299_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_vs_4281_);
lean_inc(v_ks_4280_);
lean_dec(v_x_4229_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4299_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_ks_4280_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_vs_4281_);
v___x_4286_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v_newNode_4287_; size_t v___x_4288_; uint8_t v___x_4289_; 
v_newNode_4287_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4286_, v_x_4232_, v_x_4233_);
v___x_4288_ = ((size_t)7ULL);
v___x_4289_ = lean_usize_dec_le(v___x_4288_, v_x_4231_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4290_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4287_);
v___x_4291_ = lean_unsigned_to_nat(4u);
v___x_4292_ = lean_nat_dec_lt(v___x_4290_, v___x_4291_);
lean_dec(v___x_4290_);
if (v___x_4292_ == 0)
{
lean_object* v_ks_4293_; lean_object* v_vs_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_ks_4293_ = lean_ctor_get(v_newNode_4287_, 0);
lean_inc_ref(v_ks_4293_);
v_vs_4294_ = lean_ctor_get(v_newNode_4287_, 1);
lean_inc_ref(v_vs_4294_);
lean_dec_ref(v_newNode_4287_);
v___x_4295_ = lean_unsigned_to_nat(0u);
v___x_4296_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4231_, v_ks_4293_, v_vs_4294_, v___x_4295_, v___x_4296_);
lean_dec_ref(v_vs_4294_);
lean_dec_ref(v_ks_4293_);
return v___x_4297_;
}
else
{
return v_newNode_4287_;
}
}
else
{
return v_newNode_4287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4300_, lean_object* v_keys_4301_, lean_object* v_vals_4302_, lean_object* v_i_4303_, lean_object* v_entries_4304_){
_start:
{
lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4305_ = lean_array_get_size(v_keys_4301_);
v___x_4306_ = lean_nat_dec_lt(v_i_4303_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec(v_i_4303_);
return v_entries_4304_;
}
else
{
lean_object* v_k_4307_; lean_object* v_v_4308_; uint64_t v___x_4309_; size_t v_h_4310_; size_t v___x_4311_; lean_object* v___x_4312_; size_t v___x_4313_; size_t v___x_4314_; size_t v___x_4315_; size_t v_h_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_k_4307_ = lean_array_fget_borrowed(v_keys_4301_, v_i_4303_);
v_v_4308_ = lean_array_fget_borrowed(v_vals_4302_, v_i_4303_);
v___x_4309_ = l_Lean_instHashableMVarId_hash(v_k_4307_);
v_h_4310_ = lean_uint64_to_usize(v___x_4309_);
v___x_4311_ = ((size_t)5ULL);
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = ((size_t)1ULL);
v___x_4314_ = lean_usize_sub(v_depth_4300_, v___x_4313_);
v___x_4315_ = lean_usize_mul(v___x_4311_, v___x_4314_);
v_h_4316_ = lean_usize_shift_right(v_h_4310_, v___x_4315_);
v___x_4317_ = lean_nat_add(v_i_4303_, v___x_4312_);
lean_dec(v_i_4303_);
lean_inc(v_v_4308_);
lean_inc(v_k_4307_);
v___x_4318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4304_, v_h_4316_, v_depth_4300_, v_k_4307_, v_v_4308_);
v_i_4303_ = v___x_4317_;
v_entries_4304_ = v___x_4318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4320_, lean_object* v_keys_4321_, lean_object* v_vals_4322_, lean_object* v_i_4323_, lean_object* v_entries_4324_){
_start:
{
size_t v_depth_boxed_4325_; lean_object* v_res_4326_; 
v_depth_boxed_4325_ = lean_unbox_usize(v_depth_4320_);
lean_dec(v_depth_4320_);
v_res_4326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4325_, v_keys_4321_, v_vals_4322_, v_i_4323_, v_entries_4324_);
lean_dec_ref(v_vals_4322_);
lean_dec_ref(v_keys_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4327_, lean_object* v_x_4328_, lean_object* v_x_4329_, lean_object* v_x_4330_, lean_object* v_x_4331_){
_start:
{
size_t v_x_3989__boxed_4332_; size_t v_x_3990__boxed_4333_; lean_object* v_res_4334_; 
v_x_3989__boxed_4332_ = lean_unbox_usize(v_x_4328_);
lean_dec(v_x_4328_);
v_x_3990__boxed_4333_ = lean_unbox_usize(v_x_4329_);
lean_dec(v_x_4329_);
v_res_4334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4327_, v_x_3989__boxed_4332_, v_x_3990__boxed_4333_, v_x_4330_, v_x_4331_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4335_, lean_object* v_x_4336_, lean_object* v_x_4337_){
_start:
{
uint64_t v___x_4338_; size_t v___x_4339_; size_t v___x_4340_; lean_object* v___x_4341_; 
v___x_4338_ = l_Lean_instHashableMVarId_hash(v_x_4336_);
v___x_4339_ = lean_uint64_to_usize(v___x_4338_);
v___x_4340_ = ((size_t)1ULL);
v___x_4341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4335_, v___x_4339_, v___x_4340_, v_x_4336_, v_x_4337_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4342_, lean_object* v_val_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v___x_4346_; lean_object* v_mctx_4347_; lean_object* v_cache_4348_; lean_object* v_zetaDeltaFVarIds_4349_; lean_object* v_postponed_4350_; lean_object* v_diag_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4381_; 
v___x_4346_ = lean_st_ref_take(v___y_4344_);
v_mctx_4347_ = lean_ctor_get(v___x_4346_, 0);
v_cache_4348_ = lean_ctor_get(v___x_4346_, 1);
v_zetaDeltaFVarIds_4349_ = lean_ctor_get(v___x_4346_, 2);
v_postponed_4350_ = lean_ctor_get(v___x_4346_, 3);
v_diag_4351_ = lean_ctor_get(v___x_4346_, 4);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4353_ = v___x_4346_;
v_isShared_4354_ = v_isSharedCheck_4381_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_diag_4351_);
lean_inc(v_postponed_4350_);
lean_inc(v_zetaDeltaFVarIds_4349_);
lean_inc(v_cache_4348_);
lean_inc(v_mctx_4347_);
lean_dec(v___x_4346_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4381_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_depth_4355_; lean_object* v_levelAssignDepth_4356_; lean_object* v_lmvarCounter_4357_; lean_object* v_mvarCounter_4358_; lean_object* v_lDecls_4359_; lean_object* v_decls_4360_; lean_object* v_userNames_4361_; lean_object* v_lAssignment_4362_; lean_object* v_eAssignment_4363_; lean_object* v_dAssignment_4364_; lean_object* v_instanceTypedMVars_4365_; lean_object* v_synthNormMemo_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4380_; 
v_depth_4355_ = lean_ctor_get(v_mctx_4347_, 0);
v_levelAssignDepth_4356_ = lean_ctor_get(v_mctx_4347_, 1);
v_lmvarCounter_4357_ = lean_ctor_get(v_mctx_4347_, 2);
v_mvarCounter_4358_ = lean_ctor_get(v_mctx_4347_, 3);
v_lDecls_4359_ = lean_ctor_get(v_mctx_4347_, 4);
v_decls_4360_ = lean_ctor_get(v_mctx_4347_, 5);
v_userNames_4361_ = lean_ctor_get(v_mctx_4347_, 6);
v_lAssignment_4362_ = lean_ctor_get(v_mctx_4347_, 7);
v_eAssignment_4363_ = lean_ctor_get(v_mctx_4347_, 8);
v_dAssignment_4364_ = lean_ctor_get(v_mctx_4347_, 9);
v_instanceTypedMVars_4365_ = lean_ctor_get(v_mctx_4347_, 10);
v_synthNormMemo_4366_ = lean_ctor_get(v_mctx_4347_, 11);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_mctx_4347_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4368_ = v_mctx_4347_;
v_isShared_4369_ = v_isSharedCheck_4380_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_synthNormMemo_4366_);
lean_inc(v_instanceTypedMVars_4365_);
lean_inc(v_dAssignment_4364_);
lean_inc(v_eAssignment_4363_);
lean_inc(v_lAssignment_4362_);
lean_inc(v_userNames_4361_);
lean_inc(v_decls_4360_);
lean_inc(v_lDecls_4359_);
lean_inc(v_mvarCounter_4358_);
lean_inc(v_lmvarCounter_4357_);
lean_inc(v_levelAssignDepth_4356_);
lean_inc(v_depth_4355_);
lean_dec(v_mctx_4347_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4380_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4370_ = lean_box(0);
v___x_4371_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4363_, v_mvarId_4342_, v_val_4343_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 8, v___x_4371_);
v___x_4373_ = v___x_4368_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_depth_4355_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_levelAssignDepth_4356_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_lmvarCounter_4357_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_mvarCounter_4358_);
lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_lDecls_4359_);
lean_ctor_set(v_reuseFailAlloc_4379_, 5, v_decls_4360_);
lean_ctor_set(v_reuseFailAlloc_4379_, 6, v_userNames_4361_);
lean_ctor_set(v_reuseFailAlloc_4379_, 7, v_lAssignment_4362_);
lean_ctor_set(v_reuseFailAlloc_4379_, 8, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4379_, 9, v_dAssignment_4364_);
lean_ctor_set(v_reuseFailAlloc_4379_, 10, v_instanceTypedMVars_4365_);
lean_ctor_set(v_reuseFailAlloc_4379_, 11, v_synthNormMemo_4366_);
v___x_4373_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4375_; 
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4373_);
v___x_4375_ = v___x_4353_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4373_);
lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_cache_4348_);
lean_ctor_set(v_reuseFailAlloc_4378_, 2, v_zetaDeltaFVarIds_4349_);
lean_ctor_set(v_reuseFailAlloc_4378_, 3, v_postponed_4350_);
lean_ctor_set(v_reuseFailAlloc_4378_, 4, v_diag_4351_);
v___x_4375_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_st_ref_put(v___y_4344_, v___x_4375_);
v___x_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4370_);
return v___x_4377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4382_, lean_object* v_val_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4382_, v_val_4383_, v___y_4384_);
lean_dec(v___y_4384_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4391_, lean_object* v_mv_u2082_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4401_; 
lean_inc(v_mv_u2081_4391_);
v___x_4401_ = l_Lean_MVarId_getDecl(v_mv_u2081_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
lean_inc(v_mv_u2082_4392_);
v___x_4403_ = l_Lean_MVarId_getDecl(v_mv_u2082_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v_lctx_4405_; lean_object* v_type_4406_; lean_object* v_lctx_4407_; lean_object* v_type_4408_; uint8_t v___x_4409_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v_lctx_4405_ = lean_ctor_get(v_a_4402_, 1);
lean_inc_ref(v_lctx_4405_);
v_type_4406_ = lean_ctor_get(v_a_4402_, 2);
lean_inc_ref(v_type_4406_);
lean_dec(v_a_4402_);
v_lctx_4407_ = lean_ctor_get(v_a_4404_, 1);
lean_inc_ref(v_lctx_4407_);
v_type_4408_ = lean_ctor_get(v_a_4404_, 2);
lean_inc_ref(v_type_4408_);
lean_dec(v_a_4404_);
v___x_4409_ = lean_expr_eqv(v_type_4406_, v_type_4408_);
lean_dec_ref(v_type_4408_);
lean_dec_ref(v_type_4406_);
if (v___x_4409_ == 0)
{
lean_dec_ref(v_lctx_4407_);
lean_dec_ref(v_lctx_4405_);
lean_dec(v_mv_u2082_4392_);
lean_dec(v_mv_u2081_4391_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4410_; uint8_t v___x_4411_; 
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4411_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4405_, v_lctx_4407_, v___x_4410_);
if (v___x_4411_ == 0)
{
uint8_t v___x_4412_; 
v___x_4412_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4407_, v_lctx_4405_, v___x_4410_);
lean_dec_ref(v_lctx_4405_);
lean_dec_ref(v_lctx_4407_);
if (v___x_4412_ == 0)
{
lean_dec(v_mv_u2082_4392_);
lean_dec(v_mv_u2081_4391_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4424_; 
v___x_4413_ = l_Lean_Expr_mvar___override(v_mv_u2082_4392_);
v___x_4414_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4391_, v___x_4413_, v___y_4394_);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v___x_4414_, 0);
lean_dec(v_unused_4425_);
v___x_4416_ = v___x_4414_;
v_isShared_4417_ = v_isSharedCheck_4424_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v___x_4414_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4424_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4418_ = lean_box(v___x_4411_);
v___x_4419_ = lean_box(v___x_4409_);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4420_);
v___x_4422_ = v___x_4416_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4438_; 
lean_dec_ref(v_lctx_4407_);
lean_dec_ref(v_lctx_4405_);
v___x_4426_ = l_Lean_Expr_mvar___override(v_mv_u2081_4391_);
v___x_4427_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4392_, v___x_4426_, v___y_4394_);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4438_ == 0)
{
lean_object* v_unused_4439_; 
v_unused_4439_ = lean_ctor_get(v___x_4427_, 0);
lean_dec(v_unused_4439_);
v___x_4429_ = v___x_4427_;
v_isShared_4430_ = v_isSharedCheck_4438_;
goto v_resetjp_4428_;
}
else
{
lean_dec(v___x_4427_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4438_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
uint8_t v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4431_ = 0;
v___x_4432_ = lean_box(v___x_4409_);
v___x_4433_ = lean_box(v___x_4431_);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4434_);
v___x_4436_ = v___x_4429_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v_a_4402_);
lean_dec(v_mv_u2082_4392_);
lean_dec(v_mv_u2081_4391_);
v_a_4440_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4403_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4403_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
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
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_mv_u2082_4392_);
lean_dec(v_mv_u2081_4391_);
v_a_4448_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4401_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4401_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
v___jp_4398_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4456_, lean_object* v_mv_u2082_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4456_, v_mv_u2082_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4464_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4478_, lean_object* v___x_4479_, lean_object* v___x_4480_, lean_object* v___x_4481_, lean_object* v_a_4482_, uint8_t v___x_4483_, lean_object* v_snd_4484_, lean_object* v_fst_4485_, lean_object* v_next_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = lean_apply_7(v_f_4478_, v___x_4479_, v___x_4480_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, lean_box(0));
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4528_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4528_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4528_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_fst_4497_; lean_object* v_snd_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4527_; 
v_fst_4497_ = lean_ctor_get(v_a_4493_, 0);
v_snd_4498_ = lean_ctor_get(v_a_4493_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_a_4493_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4500_ = v_a_4493_;
v_isShared_4501_ = v_isSharedCheck_4527_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_snd_4498_);
lean_inc(v_fst_4497_);
lean_dec(v_a_4493_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4527_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v_removed_4503_; lean_object* v_numRemoved_4504_; uint8_t v___x_4523_; 
v___x_4523_ = lean_unbox(v_fst_4497_);
lean_dec(v_fst_4497_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = lean_nat_add(v_snd_4484_, v___x_4481_);
lean_dec(v_snd_4484_);
v___x_4525_ = lean_box(v___x_4483_);
v___x_4526_ = lean_array_set(v_fst_4485_, v_next_4486_, v___x_4525_);
v_removed_4503_ = v___x_4526_;
v_numRemoved_4504_ = v___x_4524_;
goto v___jp_4502_;
}
else
{
v_removed_4503_ = v_fst_4485_;
v_numRemoved_4504_ = v_snd_4484_;
goto v___jp_4502_;
}
v___jp_4502_:
{
uint8_t v___x_4505_; 
v___x_4505_ = lean_unbox(v_snd_4498_);
lean_dec(v_snd_4498_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4506_ = lean_nat_add(v_numRemoved_4504_, v___x_4481_);
lean_dec(v_numRemoved_4504_);
v___x_4507_ = lean_box(v___x_4483_);
v___x_4508_ = lean_array_set(v_removed_4503_, v_a_4482_, v___x_4507_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 1, v___x_4506_);
lean_ctor_set(v___x_4500_, 0, v___x_4508_);
v___x_4510_ = v___x_4500_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v___x_4506_);
v___x_4510_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4511_);
v___x_4513_ = v___x_4495_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
else
{
lean_object* v___x_4517_; 
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 1, v_numRemoved_4504_);
lean_ctor_set(v___x_4500_, 0, v_removed_4503_);
v___x_4517_ = v___x_4500_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_removed_4503_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_numRemoved_4504_);
v___x_4517_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4518_);
v___x_4520_ = v___x_4495_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_fst_4485_);
lean_dec(v_snd_4484_);
v_a_4529_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4492_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4492_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4537_, lean_object* v___x_4538_, lean_object* v___x_4539_, lean_object* v___x_4540_, lean_object* v_a_4541_, lean_object* v___x_4542_, lean_object* v_snd_4543_, lean_object* v_fst_4544_, lean_object* v_next_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
uint8_t v___x_4362__boxed_4551_; lean_object* v_res_4552_; 
v___x_4362__boxed_4551_ = lean_unbox(v___x_4542_);
v_res_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4537_, v___x_4538_, v___x_4539_, v___x_4540_, v_a_4541_, v___x_4362__boxed_4551_, v_snd_4543_, v_fst_4544_, v_next_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v_next_4545_);
lean_dec(v_a_4541_);
lean_dec(v___x_4540_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4553_, lean_object* v_a_4554_, lean_object* v_next_4555_, lean_object* v_f_4556_, lean_object* v_a_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
uint8_t v___x_4564_; 
v___x_4564_ = lean_nat_dec_lt(v_a_4557_, v_upperBound_4553_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
lean_dec(v_a_4557_);
lean_dec_ref(v_f_4556_);
lean_dec(v_next_4555_);
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_b_4558_);
return v___x_4565_;
}
else
{
lean_object* v_fst_4566_; lean_object* v_snd_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4614_; 
v_fst_4566_ = lean_ctor_get(v_b_4558_, 0);
v_snd_4567_ = lean_ctor_get(v_b_4558_, 1);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_b_4558_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4569_ = v_b_4558_;
v_isShared_4570_ = v_isSharedCheck_4614_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_snd_4567_);
lean_inc(v_fst_4566_);
lean_dec(v_b_4558_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4614_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___y_4573_; uint8_t v___y_4596_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4571_ = lean_unsigned_to_nat(1u);
v___x_4606_ = 0;
v___x_4607_ = lean_box(v___x_4606_);
v___x_4608_ = lean_array_get(v___x_4607_, v_fst_4566_, v_next_4555_);
lean_dec(v___x_4607_);
v___x_4609_ = lean_unbox(v___x_4608_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
lean_dec(v___x_4608_);
v___x_4610_ = lean_box(v___x_4606_);
v___x_4611_ = lean_array_get(v___x_4610_, v_fst_4566_, v_a_4557_);
lean_dec(v___x_4610_);
v___x_4612_ = lean_unbox(v___x_4611_);
lean_dec(v___x_4611_);
v___y_4596_ = v___x_4612_;
goto v___jp_4595_;
}
else
{
uint8_t v___x_4613_; 
v___x_4613_ = lean_unbox(v___x_4608_);
lean_dec(v___x_4608_);
v___y_4596_ = v___x_4613_;
goto v___jp_4595_;
}
v___jp_4572_:
{
lean_object* v___x_4574_; 
lean_inc(v___y_4562_);
lean_inc_ref(v___y_4561_);
lean_inc(v___y_4560_);
lean_inc_ref(v___y_4559_);
v___x_4574_ = lean_apply_5(v___y_4573_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, lean_box(0));
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4586_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4586_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4586_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
if (lean_obj_tag(v_a_4575_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; 
lean_dec(v_a_4557_);
lean_dec_ref(v_f_4556_);
lean_dec(v_next_4555_);
v_a_4579_ = lean_ctor_get(v_a_4575_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v_a_4575_, 1);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v_a_4579_);
v___x_4581_ = v___x_4577_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4584_; 
lean_del_object(v___x_4577_);
v_a_4583_ = lean_ctor_get(v_a_4575_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v_a_4575_, 1);
v___x_4584_ = lean_nat_add(v_a_4557_, v___x_4571_);
lean_dec(v_a_4557_);
v_a_4557_ = v___x_4584_;
v_b_4558_ = v_a_4583_;
goto _start;
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec(v_a_4557_);
lean_dec_ref(v_f_4556_);
lean_dec(v_next_4555_);
v_a_4587_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4574_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4574_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
v___jp_4595_:
{
if (v___y_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___f_4600_; 
lean_del_object(v___x_4569_);
v___x_4597_ = lean_array_fget_borrowed(v_a_4554_, v_next_4555_);
v___x_4598_ = lean_array_fget_borrowed(v_a_4554_, v_a_4557_);
v___x_4599_ = lean_box(v___x_4564_);
lean_inc(v_next_4555_);
lean_inc(v_a_4557_);
lean_inc(v___x_4598_);
lean_inc(v___x_4597_);
lean_inc_ref(v_f_4556_);
v___f_4600_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4600_, 0, v_f_4556_);
lean_closure_set(v___f_4600_, 1, v___x_4597_);
lean_closure_set(v___f_4600_, 2, v___x_4598_);
lean_closure_set(v___f_4600_, 3, v___x_4571_);
lean_closure_set(v___f_4600_, 4, v_a_4557_);
lean_closure_set(v___f_4600_, 5, v___x_4599_);
lean_closure_set(v___f_4600_, 6, v_snd_4567_);
lean_closure_set(v___f_4600_, 7, v_fst_4566_);
lean_closure_set(v___f_4600_, 8, v_next_4555_);
v___y_4573_ = v___f_4600_;
goto v___jp_4572_;
}
else
{
lean_object* v___x_4602_; 
if (v_isShared_4570_ == 0)
{
v___x_4602_ = v___x_4569_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_fst_4566_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_snd_4567_);
v___x_4602_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; lean_object* v___f_4604_; 
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
v___f_4604_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4604_, 0, v___x_4603_);
v___y_4573_ = v___f_4604_;
goto v___jp_4572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4615_, lean_object* v_a_4616_, lean_object* v_next_4617_, lean_object* v_f_4618_, lean_object* v_a_4619_, lean_object* v_b_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4615_, v_a_4616_, v_next_4617_, v_f_4618_, v_a_4619_, v_b_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec_ref(v_a_4616_);
lean_dec(v_upperBound_4615_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4627_, lean_object* v___x_4628_, lean_object* v_a_4629_, lean_object* v_f_4630_, lean_object* v_a_4631_, lean_object* v_b_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v___x_4638_; 
v___x_4638_ = lean_nat_dec_lt(v_a_4631_, v_upperBound_4627_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; 
lean_dec(v_a_4631_);
lean_dec_ref(v_f_4630_);
v___x_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4639_, 0, v_b_4632_);
return v___x_4639_;
}
else
{
lean_object* v_fst_4640_; lean_object* v_snd_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4662_; 
v_fst_4640_ = lean_ctor_get(v_b_4632_, 0);
v_snd_4641_ = lean_ctor_get(v_b_4632_, 1);
v_isSharedCheck_4662_ = !lean_is_exclusive(v_b_4632_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4643_ = v_b_4632_;
v_isShared_4644_ = v_isSharedCheck_4662_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_snd_4641_);
lean_inc(v_fst_4640_);
lean_dec(v_b_4632_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4662_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
v___x_4645_ = lean_unsigned_to_nat(1u);
v___x_4646_ = lean_nat_add(v_a_4631_, v___x_4645_);
if (v_isShared_4644_ == 0)
{
v___x_4648_ = v___x_4643_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_fst_4640_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_snd_4641_);
v___x_4648_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; 
lean_inc(v___x_4646_);
lean_inc_ref(v_f_4630_);
v___x_4649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4628_, v_a_4629_, v_a_4631_, v_f_4630_, v___x_4646_, v___x_4648_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v_fst_4651_; lean_object* v_snd_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4660_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref_known(v___x_4649_, 1);
v_fst_4651_ = lean_ctor_get(v_a_4650_, 0);
v_snd_4652_ = lean_ctor_get(v_a_4650_, 1);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_a_4650_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4654_ = v_a_4650_;
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_snd_4652_);
lean_inc(v_fst_4651_);
lean_dec(v_a_4650_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_fst_4651_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_snd_4652_);
v___x_4657_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
v_a_4631_ = v___x_4646_;
v_b_4632_ = v___x_4657_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4646_);
lean_dec_ref(v_f_4630_);
return v___x_4649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4663_, lean_object* v___x_4664_, lean_object* v_a_4665_, lean_object* v_f_4666_, lean_object* v_a_4667_, lean_object* v_b_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4663_, v___x_4664_, v_a_4665_, v_f_4666_, v_a_4667_, v_b_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec_ref(v_a_4665_);
lean_dec(v___x_4664_);
lean_dec(v_upperBound_4663_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4675_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4689_, lean_object* v_removed_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___y_4700_; uint8_t v___x_4723_; 
v___x_4723_ = lean_nat_dec_lt(v_a_4692_, v_upperBound_4689_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4724_; 
lean_dec(v_a_4692_);
v___x_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4724_, 0, v_b_4693_);
return v___x_4724_;
}
else
{
uint8_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4725_ = 0;
v___x_4726_ = lean_box(v___x_4725_);
v___x_4727_ = lean_array_get(v___x_4726_, v_removed_4690_, v_a_4692_);
lean_dec(v___x_4726_);
v___x_4728_ = lean_unbox(v___x_4727_);
lean_dec(v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___f_4732_; 
v___x_4729_ = lean_array_fget_borrowed(v_a_4691_, v_a_4692_);
lean_inc(v___x_4729_);
v___x_4730_ = lean_array_push(v_b_4693_, v___x_4729_);
v___x_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
v___f_4732_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4732_, 0, v___x_4731_);
v___y_4700_ = v___f_4732_;
goto v___jp_4699_;
}
else
{
lean_object* v___x_4733_; lean_object* v___f_4734_; 
v___x_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4733_, 0, v_b_4693_);
v___f_4734_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4734_, 0, v___x_4733_);
v___y_4700_ = v___f_4734_;
goto v___jp_4699_;
}
}
v___jp_4699_:
{
lean_object* v___x_4701_; 
lean_inc(v___y_4697_);
lean_inc_ref(v___y_4696_);
lean_inc(v___y_4695_);
lean_inc_ref(v___y_4694_);
v___x_4701_ = lean_apply_5(v___y_4700_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, lean_box(0));
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4714_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4714_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4714_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
if (lean_obj_tag(v_a_4702_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; 
lean_dec(v_a_4692_);
v_a_4706_ = lean_ctor_get(v_a_4702_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v_a_4702_, 1);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v_a_4706_);
v___x_4708_ = v___x_4704_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4706_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
lean_del_object(v___x_4704_);
v_a_4710_ = lean_ctor_get(v_a_4702_, 0);
lean_inc(v_a_4710_);
lean_dec_ref_known(v_a_4702_, 1);
v___x_4711_ = lean_unsigned_to_nat(1u);
v___x_4712_ = lean_nat_add(v_a_4692_, v___x_4711_);
lean_dec(v_a_4692_);
v_a_4692_ = v___x_4712_;
v_b_4693_ = v_a_4710_;
goto _start;
}
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec(v_a_4692_);
v_a_4715_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4701_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4701_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4735_, lean_object* v_removed_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_b_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4735_, v_removed_4736_, v_a_4737_, v_a_4738_, v_b_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec_ref(v_a_4737_);
lean_dec_ref(v_removed_4736_);
lean_dec(v_upperBound_4735_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4746_, lean_object* v_f_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v_removed_4756_; lean_object* v_numRemoved_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4753_ = lean_array_get_size(v_a_4746_);
v___x_4754_ = 0;
v___x_4755_ = lean_box(v___x_4754_);
v_removed_4756_ = lean_mk_array(v___x_4753_, v___x_4755_);
v_numRemoved_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v_removed_4756_);
lean_ctor_set(v___x_4758_, 1, v_numRemoved_4757_);
v___x_4759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4753_, v___x_4753_, v_a_4746_, v_f_4747_, v_numRemoved_4757_, v___x_4758_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v_fst_4761_; lean_object* v_snd_4762_; lean_object* v_a_x27_4763_; lean_object* v___x_4764_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v_fst_4761_ = lean_ctor_get(v_a_4760_, 0);
lean_inc(v_fst_4761_);
v_snd_4762_ = lean_ctor_get(v_a_4760_, 1);
lean_inc(v_snd_4762_);
lean_dec(v_a_4760_);
v_a_x27_4763_ = lean_mk_empty_array_with_capacity(v_snd_4762_);
lean_dec(v_snd_4762_);
v___x_4764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4753_, v_fst_4761_, v_a_4746_, v_numRemoved_4757_, v_a_x27_4763_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v_fst_4761_);
return v___x_4764_;
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
v_a_4765_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4759_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4759_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4773_, lean_object* v_f_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4773_, v_f_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec_ref(v_a_4773_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___f_4788_; lean_object* v___x_4789_; 
v___f_4788_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4789_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4782_, v___f_4788_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
lean_dec_ref(v_mvars_4790_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4797_, lean_object* v_val_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v___x_4804_; 
v___x_4804_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4797_, v_val_4798_, v___y_4800_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4805_, lean_object* v_val_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4805_, v_val_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4813_, lean_object* v_a_4814_, lean_object* v_f_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4814_, v_f_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4822_, lean_object* v_a_4823_, lean_object* v_f_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4822_, v_a_4823_, v_f_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec_ref(v_a_4823_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4831_, lean_object* v_x_4832_, lean_object* v_x_4833_, lean_object* v_x_4834_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4832_, v_x_4833_, v_x_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4836_, lean_object* v_00_u03b1_4837_, lean_object* v_a_4838_, lean_object* v_next_4839_, lean_object* v_f_4840_, lean_object* v_inst_4841_, lean_object* v_R_4842_, lean_object* v_a_4843_, lean_object* v_b_4844_, lean_object* v_c_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4836_, v_a_4838_, v_next_4839_, v_f_4840_, v_a_4843_, v_b_4844_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4852_, lean_object* v_00_u03b1_4853_, lean_object* v_a_4854_, lean_object* v_next_4855_, lean_object* v_f_4856_, lean_object* v_inst_4857_, lean_object* v_R_4858_, lean_object* v_a_4859_, lean_object* v_b_4860_, lean_object* v_c_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4852_, v_00_u03b1_4853_, v_a_4854_, v_next_4855_, v_f_4856_, v_inst_4857_, v_R_4858_, v_a_4859_, v_b_4860_, v_c_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_a_4854_);
lean_dec(v_upperBound_4852_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4868_, lean_object* v_upperBound_4869_, lean_object* v_removed_4870_, lean_object* v_a_4871_, lean_object* v_inst_4872_, lean_object* v_R_4873_, lean_object* v_a_4874_, lean_object* v_b_4875_, lean_object* v_c_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4869_, v_removed_4870_, v_a_4871_, v_a_4874_, v_b_4875_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4883_, lean_object* v_upperBound_4884_, lean_object* v_removed_4885_, lean_object* v_a_4886_, lean_object* v_inst_4887_, lean_object* v_R_4888_, lean_object* v_a_4889_, lean_object* v_b_4890_, lean_object* v_c_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4883_, v_upperBound_4884_, v_removed_4885_, v_a_4886_, v_inst_4887_, v_R_4888_, v_a_4889_, v_b_4890_, v_c_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec_ref(v_a_4886_);
lean_dec_ref(v_removed_4885_);
lean_dec(v_upperBound_4884_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4898_, lean_object* v___x_4899_, lean_object* v_00_u03b1_4900_, lean_object* v_a_4901_, lean_object* v_f_4902_, lean_object* v_inst_4903_, lean_object* v_R_4904_, lean_object* v_a_4905_, lean_object* v_b_4906_, lean_object* v_c_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4898_, v___x_4899_, v_a_4901_, v_f_4902_, v_a_4905_, v_b_4906_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4914_, lean_object* v___x_4915_, lean_object* v_00_u03b1_4916_, lean_object* v_a_4917_, lean_object* v_f_4918_, lean_object* v_inst_4919_, lean_object* v_R_4920_, lean_object* v_a_4921_, lean_object* v_b_4922_, lean_object* v_c_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4914_, v___x_4915_, v_00_u03b1_4916_, v_a_4917_, v_f_4918_, v_inst_4919_, v_R_4920_, v_a_4921_, v_b_4922_, v_c_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec_ref(v_a_4917_);
lean_dec(v___x_4915_);
lean_dec(v_upperBound_4914_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4930_, lean_object* v_x_4931_, size_t v_x_4932_, size_t v_x_4933_, lean_object* v_x_4934_, lean_object* v_x_4935_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4931_, v_x_4932_, v_x_4933_, v_x_4934_, v_x_4935_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4937_, lean_object* v_x_4938_, lean_object* v_x_4939_, lean_object* v_x_4940_, lean_object* v_x_4941_, lean_object* v_x_4942_){
_start:
{
size_t v_x_4932__boxed_4943_; size_t v_x_4933__boxed_4944_; lean_object* v_res_4945_; 
v_x_4932__boxed_4943_ = lean_unbox_usize(v_x_4939_);
lean_dec(v_x_4939_);
v_x_4933__boxed_4944_ = lean_unbox_usize(v_x_4940_);
lean_dec(v_x_4940_);
v_res_4945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4937_, v_x_4938_, v_x_4932__boxed_4943_, v_x_4933__boxed_4944_, v_x_4941_, v_x_4942_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4946_, lean_object* v_n_4947_, lean_object* v_k_4948_, lean_object* v_v_4949_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4947_, v_k_4948_, v_v_4949_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4951_, size_t v_depth_4952_, lean_object* v_keys_4953_, lean_object* v_vals_4954_, lean_object* v_heq_4955_, lean_object* v_i_4956_, lean_object* v_entries_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4952_, v_keys_4953_, v_vals_4954_, v_i_4956_, v_entries_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4959_, lean_object* v_depth_4960_, lean_object* v_keys_4961_, lean_object* v_vals_4962_, lean_object* v_heq_4963_, lean_object* v_i_4964_, lean_object* v_entries_4965_){
_start:
{
size_t v_depth_boxed_4966_; lean_object* v_res_4967_; 
v_depth_boxed_4966_ = lean_unbox_usize(v_depth_4960_);
lean_dec(v_depth_4960_);
v_res_4967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4959_, v_depth_boxed_4966_, v_keys_4961_, v_vals_4962_, v_heq_4963_, v_i_4964_, v_entries_4965_);
lean_dec_ref(v_vals_4962_);
lean_dec_ref(v_keys_4961_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4968_, lean_object* v_x_4969_, lean_object* v_x_4970_, lean_object* v_x_4971_, lean_object* v_x_4972_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4969_, v_x_4970_, v_x_4971_, v_x_4972_);
return v___x_4973_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4976_ = l_Lean_stringToMessageData(v___x_4975_);
return v___x_4976_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4979_ = l_Lean_stringToMessageData(v___x_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4980_, lean_object* v_as_4981_, size_t v_sz_4982_, size_t v_i_4983_, lean_object* v_b_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v_a_4991_; uint8_t v___x_4995_; 
v___x_4995_ = lean_usize_dec_lt(v_i_4983_, v_sz_4982_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v_b_4984_);
return v___x_4996_;
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4998_; 
v_a_4997_ = lean_array_uget_borrowed(v_as_4981_, v_i_4983_);
lean_inc(v_a_4997_);
v___x_4998_ = l_Lean_MVarId_getType(v_a_4997_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref_known(v___x_4998_, 1);
if (lean_obj_tag(v_a_4999_) == 10)
{
lean_object* v_expr_5017_; 
v_expr_5017_ = lean_ctor_get(v_a_4999_, 1);
if (lean_obj_tag(v_expr_5017_) == 5)
{
lean_object* v_arg_5018_; lean_object* v___x_5019_; 
lean_inc_ref(v_expr_5017_);
lean_dec_ref_known(v_a_4999_, 2);
v_arg_5018_ = lean_ctor_get(v_expr_5017_, 1);
lean_inc_ref_n(v_arg_5018_, 2);
lean_dec_ref_known(v_expr_5017_, 2);
v___x_5019_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4980_, v_arg_5018_);
if (lean_obj_tag(v___x_5019_) == 1)
{
lean_object* v_val_5020_; lean_object* v_fst_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
lean_dec_ref(v_arg_5018_);
v_val_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_val_5020_);
lean_dec_ref_known(v___x_5019_, 1);
v_fst_5021_ = lean_ctor_get(v_val_5020_, 0);
lean_inc(v_fst_5021_);
lean_dec(v_val_5020_);
v___x_5022_ = lean_array_get_size(v_b_4984_);
v___x_5023_ = lean_nat_dec_lt(v_fst_5021_, v___x_5022_);
if (v___x_5023_ == 0)
{
lean_dec(v_fst_5021_);
v_a_4991_ = v_b_4984_;
goto v___jp_4990_;
}
else
{
lean_object* v_v_5024_; lean_object* v___x_5025_; lean_object* v_xs_x27_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v_v_5024_ = lean_array_fget(v_b_4984_, v_fst_5021_);
v___x_5025_ = lean_box(0);
v_xs_x27_5026_ = lean_array_fset(v_b_4984_, v_fst_5021_, v___x_5025_);
lean_inc(v_a_4997_);
v___x_5027_ = lean_array_push(v_v_5024_, v_a_4997_);
v___x_5028_ = lean_array_fset(v_xs_x27_5026_, v_fst_5021_, v___x_5027_);
lean_dec(v_fst_5021_);
v_a_4991_ = v___x_5028_;
goto v___jp_4990_;
}
}
else
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
lean_dec(v___x_5019_);
v___x_5029_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5030_ = l_Lean_indentExpr(v_arg_5018_);
v___x_5031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5029_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
v___x_5032_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5031_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_dec_ref_known(v___x_5032_, 1);
v_a_4991_ = v_b_4984_;
goto v___jp_4990_;
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
lean_dec_ref(v_b_4984_);
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5032_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5032_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
else
{
v___y_5001_ = v___y_4985_;
v___y_5002_ = v___y_4986_;
v___y_5003_ = v___y_4987_;
v___y_5004_ = v___y_4988_;
goto v___jp_5000_;
}
}
else
{
v___y_5001_ = v___y_4985_;
v___y_5002_ = v___y_4986_;
v___y_5003_ = v___y_4987_;
v___y_5004_ = v___y_4988_;
goto v___jp_5000_;
}
v___jp_5000_:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5006_ = l_Lean_indentExpr(v_a_4999_);
v___x_5007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5005_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5007_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_dec_ref_known(v___x_5008_, 1);
v_a_4991_ = v_b_4984_;
goto v___jp_4990_;
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
lean_dec_ref(v_b_4984_);
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_5008_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec_ref(v_b_4984_);
v_a_5041_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_4998_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_4998_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
v___jp_4990_:
{
size_t v___x_4992_; size_t v___x_4993_; 
v___x_4992_ = ((size_t)1ULL);
v___x_4993_ = lean_usize_add(v_i_4983_, v___x_4992_);
v_i_4983_ = v___x_4993_;
v_b_4984_ = v_a_4991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5049_, lean_object* v_as_5050_, lean_object* v_sz_5051_, lean_object* v_i_5052_, lean_object* v_b_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
size_t v_sz_boxed_5059_; size_t v_i_boxed_5060_; lean_object* v_res_5061_; 
v_sz_boxed_5059_ = lean_unbox_usize(v_sz_5051_);
lean_dec(v_sz_5051_);
v_i_boxed_5060_ = lean_unbox_usize(v_i_5052_);
lean_dec(v_i_5052_);
v_res_5061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5049_, v_as_5050_, v_sz_boxed_5059_, v_i_boxed_5060_, v_b_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec_ref(v_as_5050_);
lean_dec_ref(v_argsPacker_5049_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5062_, lean_object* v_numFuncs_5063_, lean_object* v_goals_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v___x_5070_; lean_object* v_r_5071_; size_t v_sz_5072_; size_t v___x_5073_; lean_object* v___x_5074_; 
v___x_5070_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5071_ = lean_mk_array(v_numFuncs_5063_, v___x_5070_);
v_sz_5072_ = lean_array_size(v_goals_5064_);
v___x_5073_ = ((size_t)0ULL);
v___x_5074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5062_, v_goals_5064_, v_sz_5072_, v___x_5073_, v_r_5071_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5075_, lean_object* v_numFuncs_5076_, lean_object* v_goals_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5075_, v_numFuncs_5076_, v_goals_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
lean_dec_ref(v_goals_5077_);
lean_dec_ref(v_argsPacker_5075_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v___x_5087_; lean_object* v_infoState_5088_; uint8_t v_enabled_5089_; 
v___x_5087_ = lean_st_ref_get(v___y_5085_);
v_infoState_5088_ = lean_ctor_get(v___x_5087_, 8);
lean_inc_ref(v_infoState_5088_);
lean_dec(v___x_5087_);
v_enabled_5089_ = lean_ctor_get_uint8(v_infoState_5088_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5088_);
if (v_enabled_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
lean_dec_ref(v_t_5084_);
v___x_5090_ = lean_box(0);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
return v___x_5091_;
}
else
{
lean_object* v___x_5092_; lean_object* v_infoState_5093_; lean_object* v_env_5094_; lean_object* v_nextMacroScope_5095_; lean_object* v_ngen_5096_; lean_object* v_auxDeclNGen_5097_; lean_object* v_traceState_5098_; lean_object* v_cache_5099_; lean_object* v_recordedDeps_5100_; lean_object* v_messages_5101_; lean_object* v_snapshotTasks_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5124_; 
v___x_5092_ = lean_st_ref_take(v___y_5085_);
v_infoState_5093_ = lean_ctor_get(v___x_5092_, 8);
v_env_5094_ = lean_ctor_get(v___x_5092_, 0);
v_nextMacroScope_5095_ = lean_ctor_get(v___x_5092_, 1);
v_ngen_5096_ = lean_ctor_get(v___x_5092_, 2);
v_auxDeclNGen_5097_ = lean_ctor_get(v___x_5092_, 3);
v_traceState_5098_ = lean_ctor_get(v___x_5092_, 4);
v_cache_5099_ = lean_ctor_get(v___x_5092_, 5);
v_recordedDeps_5100_ = lean_ctor_get(v___x_5092_, 6);
v_messages_5101_ = lean_ctor_get(v___x_5092_, 7);
v_snapshotTasks_5102_ = lean_ctor_get(v___x_5092_, 9);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5104_ = v___x_5092_;
v_isShared_5105_ = v_isSharedCheck_5124_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_snapshotTasks_5102_);
lean_inc(v_infoState_5093_);
lean_inc(v_messages_5101_);
lean_inc(v_recordedDeps_5100_);
lean_inc(v_cache_5099_);
lean_inc(v_traceState_5098_);
lean_inc(v_auxDeclNGen_5097_);
lean_inc(v_ngen_5096_);
lean_inc(v_nextMacroScope_5095_);
lean_inc(v_env_5094_);
lean_dec(v___x_5092_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5124_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
uint8_t v_enabled_5106_; lean_object* v_assignment_5107_; lean_object* v_lazyAssignment_5108_; lean_object* v_trees_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5123_; 
v_enabled_5106_ = lean_ctor_get_uint8(v_infoState_5093_, sizeof(void*)*3);
v_assignment_5107_ = lean_ctor_get(v_infoState_5093_, 0);
v_lazyAssignment_5108_ = lean_ctor_get(v_infoState_5093_, 1);
v_trees_5109_ = lean_ctor_get(v_infoState_5093_, 2);
v_isSharedCheck_5123_ = !lean_is_exclusive(v_infoState_5093_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5111_ = v_infoState_5093_;
v_isShared_5112_ = v_isSharedCheck_5123_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_trees_5109_);
lean_inc(v_lazyAssignment_5108_);
lean_inc(v_assignment_5107_);
lean_dec(v_infoState_5093_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5123_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5116_; 
v___x_5113_ = lean_box(0);
v___x_5114_ = l_Lean_PersistentArray_push___redArg(v_trees_5109_, v_t_5084_);
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 2, v___x_5114_);
v___x_5116_ = v___x_5111_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_assignment_5107_);
lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_lazyAssignment_5108_);
lean_ctor_set(v_reuseFailAlloc_5122_, 2, v___x_5114_);
lean_ctor_set_uint8(v_reuseFailAlloc_5122_, sizeof(void*)*3, v_enabled_5106_);
v___x_5116_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
lean_object* v___x_5118_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 8, v___x_5116_);
v___x_5118_ = v___x_5104_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_env_5094_);
lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_nextMacroScope_5095_);
lean_ctor_set(v_reuseFailAlloc_5121_, 2, v_ngen_5096_);
lean_ctor_set(v_reuseFailAlloc_5121_, 3, v_auxDeclNGen_5097_);
lean_ctor_set(v_reuseFailAlloc_5121_, 4, v_traceState_5098_);
lean_ctor_set(v_reuseFailAlloc_5121_, 5, v_cache_5099_);
lean_ctor_set(v_reuseFailAlloc_5121_, 6, v_recordedDeps_5100_);
lean_ctor_set(v_reuseFailAlloc_5121_, 7, v_messages_5101_);
lean_ctor_set(v_reuseFailAlloc_5121_, 8, v___x_5116_);
lean_ctor_set(v_reuseFailAlloc_5121_, 9, v_snapshotTasks_5102_);
v___x_5118_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = lean_st_ref_put(v___y_5085_, v___x_5118_);
v___x_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5113_);
return v___x_5120_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5125_, v___y_5126_);
lean_dec(v___y_5126_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v___x_5137_; 
v___x_5137_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5129_, v___y_5135_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
lean_object* v_res_5146_; 
v_res_5146_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5147_, lean_object* v___y_5148_){
_start:
{
uint8_t v___x_5150_; 
v___x_5150_ = l_Lean_Expr_hasMVar(v_e_5147_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; 
v___x_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5151_, 0, v_e_5147_);
return v___x_5151_;
}
else
{
lean_object* v___x_5152_; lean_object* v_mctx_5153_; lean_object* v___x_5154_; lean_object* v_fst_5155_; lean_object* v_snd_5156_; lean_object* v___x_5157_; lean_object* v_cache_5158_; lean_object* v_zetaDeltaFVarIds_5159_; lean_object* v_postponed_5160_; lean_object* v_diag_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5170_; 
v___x_5152_ = lean_st_ref_get(v___y_5148_);
v_mctx_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc_ref(v_mctx_5153_);
lean_dec(v___x_5152_);
v___x_5154_ = l_Lean_instantiateMVarsCore(v_mctx_5153_, v_e_5147_);
v_fst_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_fst_5155_);
v_snd_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_snd_5156_);
lean_dec_ref(v___x_5154_);
v___x_5157_ = lean_st_ref_take(v___y_5148_);
v_cache_5158_ = lean_ctor_get(v___x_5157_, 1);
v_zetaDeltaFVarIds_5159_ = lean_ctor_get(v___x_5157_, 2);
v_postponed_5160_ = lean_ctor_get(v___x_5157_, 3);
v_diag_5161_ = lean_ctor_get(v___x_5157_, 4);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; 
v_unused_5171_ = lean_ctor_get(v___x_5157_, 0);
lean_dec(v_unused_5171_);
v___x_5163_ = v___x_5157_;
v_isShared_5164_ = v_isSharedCheck_5170_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_diag_5161_);
lean_inc(v_postponed_5160_);
lean_inc(v_zetaDeltaFVarIds_5159_);
lean_inc(v_cache_5158_);
lean_dec(v___x_5157_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5170_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 0, v_snd_5156_);
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_snd_5156_);
lean_ctor_set(v_reuseFailAlloc_5169_, 1, v_cache_5158_);
lean_ctor_set(v_reuseFailAlloc_5169_, 2, v_zetaDeltaFVarIds_5159_);
lean_ctor_set(v_reuseFailAlloc_5169_, 3, v_postponed_5160_);
lean_ctor_set(v_reuseFailAlloc_5169_, 4, v_diag_5161_);
v___x_5166_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5167_; lean_object* v___x_5168_; 
v___x_5167_ = lean_st_ref_put(v___y_5148_, v___x_5166_);
v___x_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5168_, 0, v_fst_5155_);
return v___x_5168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5172_, v___y_5173_);
lean_dec(v___y_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5176_, v___y_5178_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5190_, size_t v_i_5191_, size_t v_stop_5192_, lean_object* v_b_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_){
_start:
{
uint8_t v___x_5201_; 
v___x_5201_ = lean_usize_dec_eq(v_i_5191_, v_stop_5192_);
if (v___x_5201_ == 0)
{
lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5202_ = lean_array_uget_borrowed(v_as_5190_, v_i_5191_);
lean_inc(v___x_5202_);
v___x_5203_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
v___x_5204_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5203_, v___y_5199_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; size_t v___x_5206_; size_t v___x_5207_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref_known(v___x_5204_, 1);
v___x_5206_ = ((size_t)1ULL);
v___x_5207_ = lean_usize_add(v_i_5191_, v___x_5206_);
v_i_5191_ = v___x_5207_;
v_b_5193_ = v_a_5205_;
goto _start;
}
else
{
return v___x_5204_;
}
}
else
{
lean_object* v___x_5209_; 
v___x_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5209_, 0, v_b_5193_);
return v___x_5209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5210_, lean_object* v_i_5211_, lean_object* v_stop_5212_, lean_object* v_b_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
size_t v_i_boxed_5221_; size_t v_stop_boxed_5222_; lean_object* v_res_5223_; 
v_i_boxed_5221_ = lean_unbox_usize(v_i_5211_);
lean_dec(v_i_5211_);
v_stop_boxed_5222_ = lean_unbox_usize(v_stop_5212_);
lean_dec(v_stop_5212_);
v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5210_, v_i_boxed_5221_, v_stop_boxed_5222_, v_b_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec_ref(v_as_5210_);
return v_res_5223_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5224_ = lean_unsigned_to_nat(32u);
v___x_5225_ = lean_mk_empty_array_with_capacity(v___x_5224_);
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5225_);
return v___x_5226_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
v___x_5227_ = ((size_t)5ULL);
v___x_5228_ = lean_unsigned_to_nat(0u);
v___x_5229_ = lean_unsigned_to_nat(32u);
v___x_5230_ = lean_mk_empty_array_with_capacity(v___x_5229_);
v___x_5231_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5232_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
lean_ctor_set(v___x_5232_, 1, v___x_5230_);
lean_ctor_set(v___x_5232_, 2, v___x_5228_);
lean_ctor_set(v___x_5232_, 3, v___x_5228_);
lean_ctor_set_usize(v___x_5232_, 4, v___x_5227_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5233_){
_start:
{
lean_object* v___x_5235_; lean_object* v_infoState_5236_; lean_object* v_trees_5237_; lean_object* v___x_5238_; lean_object* v_infoState_5239_; lean_object* v_env_5240_; lean_object* v_nextMacroScope_5241_; lean_object* v_ngen_5242_; lean_object* v_auxDeclNGen_5243_; lean_object* v_traceState_5244_; lean_object* v_cache_5245_; lean_object* v_recordedDeps_5246_; lean_object* v_messages_5247_; lean_object* v_snapshotTasks_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5269_; 
v___x_5235_ = lean_st_ref_get(v___y_5233_);
v_infoState_5236_ = lean_ctor_get(v___x_5235_, 8);
lean_inc_ref(v_infoState_5236_);
lean_dec(v___x_5235_);
v_trees_5237_ = lean_ctor_get(v_infoState_5236_, 2);
lean_inc_ref(v_trees_5237_);
lean_dec_ref(v_infoState_5236_);
v___x_5238_ = lean_st_ref_take(v___y_5233_);
v_infoState_5239_ = lean_ctor_get(v___x_5238_, 8);
v_env_5240_ = lean_ctor_get(v___x_5238_, 0);
v_nextMacroScope_5241_ = lean_ctor_get(v___x_5238_, 1);
v_ngen_5242_ = lean_ctor_get(v___x_5238_, 2);
v_auxDeclNGen_5243_ = lean_ctor_get(v___x_5238_, 3);
v_traceState_5244_ = lean_ctor_get(v___x_5238_, 4);
v_cache_5245_ = lean_ctor_get(v___x_5238_, 5);
v_recordedDeps_5246_ = lean_ctor_get(v___x_5238_, 6);
v_messages_5247_ = lean_ctor_get(v___x_5238_, 7);
v_snapshotTasks_5248_ = lean_ctor_get(v___x_5238_, 9);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5250_ = v___x_5238_;
v_isShared_5251_ = v_isSharedCheck_5269_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_snapshotTasks_5248_);
lean_inc(v_infoState_5239_);
lean_inc(v_messages_5247_);
lean_inc(v_recordedDeps_5246_);
lean_inc(v_cache_5245_);
lean_inc(v_traceState_5244_);
lean_inc(v_auxDeclNGen_5243_);
lean_inc(v_ngen_5242_);
lean_inc(v_nextMacroScope_5241_);
lean_inc(v_env_5240_);
lean_dec(v___x_5238_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5269_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
uint8_t v_enabled_5252_; lean_object* v_assignment_5253_; lean_object* v_lazyAssignment_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5267_; 
v_enabled_5252_ = lean_ctor_get_uint8(v_infoState_5239_, sizeof(void*)*3);
v_assignment_5253_ = lean_ctor_get(v_infoState_5239_, 0);
v_lazyAssignment_5254_ = lean_ctor_get(v_infoState_5239_, 1);
v_isSharedCheck_5267_ = !lean_is_exclusive(v_infoState_5239_);
if (v_isSharedCheck_5267_ == 0)
{
lean_object* v_unused_5268_; 
v_unused_5268_ = lean_ctor_get(v_infoState_5239_, 2);
lean_dec(v_unused_5268_);
v___x_5256_ = v_infoState_5239_;
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_lazyAssignment_5254_);
lean_inc(v_assignment_5253_);
lean_dec(v_infoState_5239_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v___x_5260_; 
v___x_5258_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 2, v___x_5258_);
v___x_5260_ = v___x_5256_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_assignment_5253_);
lean_ctor_set(v_reuseFailAlloc_5266_, 1, v_lazyAssignment_5254_);
lean_ctor_set(v_reuseFailAlloc_5266_, 2, v___x_5258_);
lean_ctor_set_uint8(v_reuseFailAlloc_5266_, sizeof(void*)*3, v_enabled_5252_);
v___x_5260_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5262_; 
if (v_isShared_5251_ == 0)
{
lean_ctor_set(v___x_5250_, 8, v___x_5260_);
v___x_5262_ = v___x_5250_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_env_5240_);
lean_ctor_set(v_reuseFailAlloc_5265_, 1, v_nextMacroScope_5241_);
lean_ctor_set(v_reuseFailAlloc_5265_, 2, v_ngen_5242_);
lean_ctor_set(v_reuseFailAlloc_5265_, 3, v_auxDeclNGen_5243_);
lean_ctor_set(v_reuseFailAlloc_5265_, 4, v_traceState_5244_);
lean_ctor_set(v_reuseFailAlloc_5265_, 5, v_cache_5245_);
lean_ctor_set(v_reuseFailAlloc_5265_, 6, v_recordedDeps_5246_);
lean_ctor_set(v_reuseFailAlloc_5265_, 7, v_messages_5247_);
lean_ctor_set(v_reuseFailAlloc_5265_, 8, v___x_5260_);
lean_ctor_set(v_reuseFailAlloc_5265_, 9, v_snapshotTasks_5248_);
v___x_5262_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = lean_st_ref_put(v___y_5233_, v___x_5262_);
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v_trees_5237_);
return v___x_5264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5270_);
lean_dec(v___y_5270_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5273_, lean_object* v_mkInfoTree_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v_a_5282_, lean_object* v_a_x3f_5283_){
_start:
{
lean_object* v___x_5285_; lean_object* v_infoState_5286_; lean_object* v_trees_5287_; lean_object* v___x_5288_; 
v___x_5285_ = lean_st_ref_get(v___y_5273_);
v_infoState_5286_ = lean_ctor_get(v___x_5285_, 8);
lean_inc_ref(v_infoState_5286_);
lean_dec(v___x_5285_);
v_trees_5287_ = lean_ctor_get(v_infoState_5286_, 2);
lean_inc_ref(v_trees_5287_);
lean_dec_ref(v_infoState_5286_);
lean_inc(v___y_5273_);
lean_inc_ref(v___y_5281_);
lean_inc(v___y_5280_);
lean_inc_ref(v___y_5279_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
lean_inc(v___y_5276_);
lean_inc_ref(v___y_5275_);
v___x_5288_ = lean_apply_10(v_mkInfoTree_5274_, v_trees_5287_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5273_, lean_box(0));
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5328_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5328_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5328_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5293_; lean_object* v_infoState_5294_; lean_object* v_env_5295_; lean_object* v_nextMacroScope_5296_; lean_object* v_ngen_5297_; lean_object* v_auxDeclNGen_5298_; lean_object* v_traceState_5299_; lean_object* v_cache_5300_; lean_object* v_recordedDeps_5301_; lean_object* v_messages_5302_; lean_object* v_snapshotTasks_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5327_; 
v___x_5293_ = lean_st_ref_take(v___y_5273_);
v_infoState_5294_ = lean_ctor_get(v___x_5293_, 8);
v_env_5295_ = lean_ctor_get(v___x_5293_, 0);
v_nextMacroScope_5296_ = lean_ctor_get(v___x_5293_, 1);
v_ngen_5297_ = lean_ctor_get(v___x_5293_, 2);
v_auxDeclNGen_5298_ = lean_ctor_get(v___x_5293_, 3);
v_traceState_5299_ = lean_ctor_get(v___x_5293_, 4);
v_cache_5300_ = lean_ctor_get(v___x_5293_, 5);
v_recordedDeps_5301_ = lean_ctor_get(v___x_5293_, 6);
v_messages_5302_ = lean_ctor_get(v___x_5293_, 7);
v_snapshotTasks_5303_ = lean_ctor_get(v___x_5293_, 9);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5305_ = v___x_5293_;
v_isShared_5306_ = v_isSharedCheck_5327_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_snapshotTasks_5303_);
lean_inc(v_infoState_5294_);
lean_inc(v_messages_5302_);
lean_inc(v_recordedDeps_5301_);
lean_inc(v_cache_5300_);
lean_inc(v_traceState_5299_);
lean_inc(v_auxDeclNGen_5298_);
lean_inc(v_ngen_5297_);
lean_inc(v_nextMacroScope_5296_);
lean_inc(v_env_5295_);
lean_dec(v___x_5293_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5327_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
uint8_t v_enabled_5307_; lean_object* v_assignment_5308_; lean_object* v_lazyAssignment_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5325_; 
v_enabled_5307_ = lean_ctor_get_uint8(v_infoState_5294_, sizeof(void*)*3);
v_assignment_5308_ = lean_ctor_get(v_infoState_5294_, 0);
v_lazyAssignment_5309_ = lean_ctor_get(v_infoState_5294_, 1);
v_isSharedCheck_5325_ = !lean_is_exclusive(v_infoState_5294_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v_infoState_5294_, 2);
lean_dec(v_unused_5326_);
v___x_5311_ = v_infoState_5294_;
v_isShared_5312_ = v_isSharedCheck_5325_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_lazyAssignment_5309_);
lean_inc(v_assignment_5308_);
lean_dec(v_infoState_5294_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5325_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5316_; 
v___x_5313_ = lean_box(0);
v___x_5314_ = l_Lean_PersistentArray_push___redArg(v_a_5282_, v_a_5289_);
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 2, v___x_5314_);
v___x_5316_ = v___x_5311_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_assignment_5308_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v_lazyAssignment_5309_);
lean_ctor_set(v_reuseFailAlloc_5324_, 2, v___x_5314_);
lean_ctor_set_uint8(v_reuseFailAlloc_5324_, sizeof(void*)*3, v_enabled_5307_);
v___x_5316_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5318_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 8, v___x_5316_);
v___x_5318_ = v___x_5305_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_env_5295_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v_nextMacroScope_5296_);
lean_ctor_set(v_reuseFailAlloc_5323_, 2, v_ngen_5297_);
lean_ctor_set(v_reuseFailAlloc_5323_, 3, v_auxDeclNGen_5298_);
lean_ctor_set(v_reuseFailAlloc_5323_, 4, v_traceState_5299_);
lean_ctor_set(v_reuseFailAlloc_5323_, 5, v_cache_5300_);
lean_ctor_set(v_reuseFailAlloc_5323_, 6, v_recordedDeps_5301_);
lean_ctor_set(v_reuseFailAlloc_5323_, 7, v_messages_5302_);
lean_ctor_set(v_reuseFailAlloc_5323_, 8, v___x_5316_);
lean_ctor_set(v_reuseFailAlloc_5323_, 9, v_snapshotTasks_5303_);
v___x_5318_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
lean_object* v___x_5319_; lean_object* v___x_5321_; 
v___x_5319_ = lean_st_ref_put(v___y_5273_, v___x_5318_);
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5313_);
v___x_5321_ = v___x_5291_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5313_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec_ref(v_a_5282_);
v_a_5329_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5288_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5288_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5337_, lean_object* v_mkInfoTree_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v_a_5346_, lean_object* v_a_x3f_5347_, lean_object* v___y_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5337_, v_mkInfoTree_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v_a_5346_, v_a_x3f_5347_);
lean_dec(v_a_x3f_5347_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5337_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5350_, lean_object* v_mkInfoTree_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___x_5361_; lean_object* v_infoState_5362_; uint8_t v_enabled_5363_; 
v___x_5361_ = lean_st_ref_get(v___y_5359_);
v_infoState_5362_ = lean_ctor_get(v___x_5361_, 8);
lean_inc_ref(v_infoState_5362_);
lean_dec(v___x_5361_);
v_enabled_5363_ = lean_ctor_get_uint8(v_infoState_5362_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5362_);
if (v_enabled_5363_ == 0)
{
lean_object* v___x_5364_; 
lean_dec_ref(v_mkInfoTree_5351_);
lean_inc(v___y_5359_);
lean_inc_ref(v___y_5358_);
lean_inc(v___y_5357_);
lean_inc_ref(v___y_5356_);
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5354_);
lean_inc(v___y_5353_);
lean_inc_ref(v___y_5352_);
v___x_5364_ = lean_apply_9(v_x_5350_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, lean_box(0));
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; lean_object* v_a_5366_; lean_object* v_r_5367_; 
v___x_5365_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5359_);
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
lean_dec_ref(v___x_5365_);
lean_inc(v___y_5359_);
lean_inc_ref(v___y_5358_);
lean_inc(v___y_5357_);
lean_inc_ref(v___y_5356_);
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5354_);
lean_inc(v___y_5353_);
lean_inc_ref(v___y_5352_);
v_r_5367_ = lean_apply_9(v_x_5350_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, lean_box(0));
if (lean_obj_tag(v_r_5367_) == 0)
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5392_; 
v_a_5368_ = lean_ctor_get(v_r_5367_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v_r_5367_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5370_ = v_r_5367_;
v_isShared_5371_ = v_isSharedCheck_5392_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v_r_5367_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5392_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
lean_inc(v_a_5368_);
if (v_isShared_5371_ == 0)
{
lean_ctor_set_tag(v___x_5370_, 1);
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
lean_object* v___x_5374_; 
v___x_5374_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5359_, v_mkInfoTree_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v_a_5366_, v___x_5373_);
lean_dec_ref(v___x_5373_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5381_ == 0)
{
lean_object* v_unused_5382_; 
v_unused_5382_ = lean_ctor_get(v___x_5374_, 0);
lean_dec(v_unused_5382_);
v___x_5376_ = v___x_5374_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_dec(v___x_5374_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v_a_5368_);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5368_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec(v_a_5368_);
v_a_5383_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5374_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5374_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
}
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v_a_5393_ = lean_ctor_get(v_r_5367_, 0);
lean_inc(v_a_5393_);
lean_dec_ref_known(v_r_5367_, 1);
v___x_5394_ = lean_box(0);
v___x_5395_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5359_, v_mkInfoTree_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v_a_5366_, v___x_5394_);
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
lean_ctor_set_tag(v___x_5397_, 1);
lean_ctor_set(v___x_5397_, 0, v_a_5393_);
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5393_);
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
lean_dec(v_a_5393_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5412_, lean_object* v_mkInfoTree_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5412_, v_mkInfoTree_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5424_, lean_object* v_trees_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v___x_5435_; 
lean_inc(v___y_5433_);
lean_inc_ref(v___y_5432_);
lean_inc(v___y_5431_);
lean_inc_ref(v___y_5430_);
lean_inc(v___y_5429_);
lean_inc_ref(v___y_5428_);
lean_inc(v___y_5427_);
lean_inc_ref(v___y_5426_);
v___x_5435_ = lean_apply_9(v_a_5424_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, lean_box(0));
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5444_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5438_ = v___x_5435_;
v_isShared_5439_ = v_isSharedCheck_5444_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5435_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5444_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5440_; lean_object* v___x_5442_; 
v___x_5440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5440_, 0, v_a_5436_);
lean_ctor_set(v___x_5440_, 1, v_trees_5425_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 0, v___x_5440_);
v___x_5442_ = v___x_5438_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5440_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
else
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_dec_ref(v_trees_5425_);
v_a_5445_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5435_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5435_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5453_, lean_object* v_trees_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5453_, v_trees_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5465_, lean_object* v_tactic_5466_, lean_object* v_ref_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5465_, v___y_5469_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v___x_5478_; 
lean_dec_ref_known(v___x_5477_, 1);
v___x_5478_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v___x_5479_; lean_object* v___x_5480_; 
lean_dec_ref_known(v___x_5478_, 1);
v___x_5479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5479_, 0, v_tactic_5466_);
v___x_5480_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
if (lean_obj_tag(v___x_5480_) == 0)
{
lean_object* v_a_5481_; lean_object* v___f_5482_; lean_object* v___x_5483_; 
v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc(v_a_5481_);
lean_dec_ref_known(v___x_5480_, 1);
v___f_5482_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5482_, 0, v_a_5481_);
v___x_5483_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5479_, v___f_5482_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
return v___x_5483_;
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
lean_dec_ref(v___x_5479_);
v_a_5484_ = lean_ctor_get(v___x_5480_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5480_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5480_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
else
{
lean_dec(v_ref_5467_);
lean_dec(v_tactic_5466_);
return v___x_5478_;
}
}
else
{
lean_dec(v_ref_5467_);
lean_dec(v_tactic_5466_);
return v___x_5477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5492_, lean_object* v_tactic_5493_, lean_object* v_ref_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_){
_start:
{
lean_object* v_res_5504_; 
v_res_5504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5492_, v_tactic_5493_, v_ref_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
lean_dec(v___y_5502_);
lean_dec_ref(v___y_5501_);
lean_dec(v___y_5500_);
lean_dec_ref(v___y_5499_);
lean_dec(v___y_5498_);
lean_dec_ref(v___y_5497_);
lean_dec(v___y_5496_);
lean_dec_ref(v___y_5495_);
return v_res_5504_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5505_ = lean_box(1);
v___x_5506_ = l_Lean_MessageData_ofFormat(v___x_5505_);
return v___x_5506_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5511_ = l_Lean_MessageData_ofFormat(v___x_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5512_, lean_object* v_x_5513_){
_start:
{
if (lean_obj_tag(v_x_5513_) == 0)
{
return v_x_5512_;
}
else
{
lean_object* v_head_5514_; lean_object* v_tail_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5537_; 
v_head_5514_ = lean_ctor_get(v_x_5513_, 0);
v_tail_5515_ = lean_ctor_get(v_x_5513_, 1);
v_isSharedCheck_5537_ = !lean_is_exclusive(v_x_5513_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5517_ = v_x_5513_;
v_isShared_5518_ = v_isSharedCheck_5537_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_tail_5515_);
lean_inc(v_head_5514_);
lean_dec(v_x_5513_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5537_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v_before_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5535_; 
v_before_5519_ = lean_ctor_get(v_head_5514_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_head_5514_);
if (v_isSharedCheck_5535_ == 0)
{
lean_object* v_unused_5536_; 
v_unused_5536_ = lean_ctor_get(v_head_5514_, 1);
lean_dec(v_unused_5536_);
v___x_5521_ = v_head_5514_;
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_before_5519_);
lean_dec(v_head_5514_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; lean_object* v___x_5525_; 
v___x_5523_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5522_ == 0)
{
lean_ctor_set_tag(v___x_5521_, 7);
lean_ctor_set(v___x_5521_, 1, v___x_5523_);
lean_ctor_set(v___x_5521_, 0, v_x_5512_);
v___x_5525_ = v___x_5521_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_x_5512_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5526_; lean_object* v___x_5528_; 
v___x_5526_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5518_ == 0)
{
lean_ctor_set_tag(v___x_5517_, 7);
lean_ctor_set(v___x_5517_, 1, v___x_5526_);
lean_ctor_set(v___x_5517_, 0, v___x_5525_);
v___x_5528_ = v___x_5517_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5525_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5529_ = l_Lean_MessageData_ofSyntax(v_before_5519_);
v___x_5530_ = l_Lean_indentD(v___x_5529_);
v___x_5531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5528_);
lean_ctor_set(v___x_5531_, 1, v___x_5530_);
v_x_5512_ = v___x_5531_;
v_x_5513_ = v_tail_5515_;
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
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5542_ = l_Lean_MessageData_ofFormat(v___x_5541_);
return v___x_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5543_, lean_object* v_macroStack_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v___x_5547_; lean_object* v___x_5548_; uint8_t v___x_5549_; 
v___x_5547_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5545_);
v___x_5548_ = l_Lean_Elab_pp_macroStack;
v___x_5549_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v___x_5547_, v___x_5548_);
lean_dec_ref(v___x_5547_);
if (v___x_5549_ == 0)
{
lean_object* v___x_5550_; 
lean_dec(v_macroStack_5544_);
v___x_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5550_, 0, v_msgData_5543_);
return v___x_5550_;
}
else
{
if (lean_obj_tag(v_macroStack_5544_) == 0)
{
lean_object* v___x_5551_; 
v___x_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5551_, 0, v_msgData_5543_);
return v___x_5551_;
}
else
{
lean_object* v_head_5552_; lean_object* v_after_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5568_; 
v_head_5552_ = lean_ctor_get(v_macroStack_5544_, 0);
lean_inc(v_head_5552_);
v_after_5553_ = lean_ctor_get(v_head_5552_, 1);
v_isSharedCheck_5568_ = !lean_is_exclusive(v_head_5552_);
if (v_isSharedCheck_5568_ == 0)
{
lean_object* v_unused_5569_; 
v_unused_5569_ = lean_ctor_get(v_head_5552_, 0);
lean_dec(v_unused_5569_);
v___x_5555_ = v_head_5552_;
v_isShared_5556_ = v_isSharedCheck_5568_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_after_5553_);
lean_dec(v_head_5552_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5568_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v___x_5559_; 
v___x_5557_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5556_ == 0)
{
lean_ctor_set_tag(v___x_5555_, 7);
lean_ctor_set(v___x_5555_, 1, v___x_5557_);
lean_ctor_set(v___x_5555_, 0, v_msgData_5543_);
v___x_5559_ = v___x_5555_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_msgData_5543_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v_msgData_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5560_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___x_5559_);
lean_ctor_set(v___x_5561_, 1, v___x_5560_);
v___x_5562_ = l_Lean_MessageData_ofSyntax(v_after_5553_);
v___x_5563_ = l_Lean_indentD(v___x_5562_);
v_msgData_5564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5564_, 0, v___x_5561_);
lean_ctor_set(v_msgData_5564_, 1, v___x_5563_);
v___x_5565_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5564_, v_macroStack_5544_);
v___x_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
return v___x_5566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5570_, lean_object* v_macroStack_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_){
_start:
{
lean_object* v_res_5574_; 
v_res_5574_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5570_, v_macroStack_5571_, v___y_5572_);
lean_dec_ref(v___y_5572_);
return v_res_5574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_ref_5583_; lean_object* v_macroStack_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v_a_5587_; lean_object* v___x_5588_; lean_object* v_a_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5597_; 
v_ref_5583_ = lean_ctor_get(v___y_5580_, 2);
v_macroStack_5584_ = lean_ctor_get(v___y_5576_, 1);
v___x_5585_ = l_Lean_Elab_getBetterRef(v_ref_5583_, v_macroStack_5584_);
v___x_5586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5575_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v_a_5587_);
lean_dec_ref(v___x_5586_);
lean_inc(v_macroStack_5584_);
v___x_5588_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5587_, v_macroStack_5584_, v___y_5580_);
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5591_ = v___x_5588_;
v_isShared_5592_ = v_isSharedCheck_5597_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_dec(v___x_5588_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5597_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5593_, 0, v___x_5585_);
lean_ctor_set(v___x_5593_, 1, v_a_5589_);
if (v_isShared_5592_ == 0)
{
lean_ctor_set_tag(v___x_5591_, 1);
lean_ctor_set(v___x_5591_, 0, v___x_5593_);
v___x_5595_ = v___x_5591_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
lean_object* v_res_5606_; 
v_res_5606_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
return v_res_5606_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5608_; lean_object* v___x_5609_; 
v___x_5608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5609_ = l_Lean_stringToMessageData(v___x_5608_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5610_, size_t v_sz_5611_, size_t v_i_5612_, lean_object* v_b_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
lean_object* v_a_5622_; uint8_t v___x_5626_; 
v___x_5626_ = lean_usize_dec_lt(v_i_5612_, v_sz_5611_);
if (v___x_5626_ == 0)
{
lean_object* v___x_5627_; 
v___x_5627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5627_, 0, v_b_5613_);
return v___x_5627_;
}
else
{
lean_object* v___x_5628_; lean_object* v_a_5629_; lean_object* v___x_5630_; 
v___x_5628_ = lean_box(0);
v_a_5629_ = lean_array_uget_borrowed(v_as_5610_, v_i_5612_);
lean_inc(v_a_5629_);
v___x_5630_ = l_Lean_MVarId_getType(v_a_5629_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; lean_object* v___x_5632_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5630_, 1);
lean_inc(v_a_5629_);
v___x_5632_ = l_Lean_MVarId_getType(v_a_5629_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v_a_5633_; lean_object* v___x_5634_; 
v_a_5633_ = lean_ctor_get(v___x_5632_, 0);
lean_inc(v_a_5633_);
lean_dec_ref_known(v___x_5632_, 1);
v___x_5634_ = l_Lean_getRecAppSyntax_x3f(v_a_5633_);
lean_dec(v_a_5633_);
if (lean_obj_tag(v___x_5634_) == 1)
{
lean_object* v_val_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v_val_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_val_5635_);
lean_dec_ref_known(v___x_5634_, 1);
v___x_5636_ = l_Lean_Expr_mdataExpr_x21(v_a_5631_);
lean_dec(v_a_5631_);
lean_inc(v_a_5629_);
v___x_5637_ = l_Lean_MVarId_setType___redArg(v_a_5629_, v___x_5636_, v___y_5617_);
if (lean_obj_tag(v___x_5637_) == 0)
{
lean_object* v_toCold_5638_; lean_object* v_currRecDepth_5639_; lean_object* v_ref_5640_; uint16_t v_optionFlags_5641_; uint8_t v_suppressElabErrors_5642_; uint8_t v_isRecordingDeps_5643_; lean_object* v_ref_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
lean_dec_ref_known(v___x_5637_, 1);
v_toCold_5638_ = lean_ctor_get(v___y_5618_, 0);
v_currRecDepth_5639_ = lean_ctor_get(v___y_5618_, 1);
v_ref_5640_ = lean_ctor_get(v___y_5618_, 2);
v_optionFlags_5641_ = lean_ctor_get_uint16(v___y_5618_, sizeof(void*)*3);
v_suppressElabErrors_5642_ = lean_ctor_get_uint8(v___y_5618_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5643_ = lean_ctor_get_uint8(v___y_5618_, sizeof(void*)*3 + 3);
v_ref_5644_ = l_Lean_replaceRef(v_val_5635_, v_ref_5640_);
lean_dec(v_val_5635_);
lean_inc(v_currRecDepth_5639_);
lean_inc_ref(v_toCold_5638_);
v___x_5645_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5645_, 0, v_toCold_5638_);
lean_ctor_set(v___x_5645_, 1, v_currRecDepth_5639_);
lean_ctor_set(v___x_5645_, 2, v_ref_5644_);
lean_ctor_set_uint16(v___x_5645_, sizeof(void*)*3, v_optionFlags_5641_);
lean_ctor_set_uint8(v___x_5645_, sizeof(void*)*3 + 2, v_suppressElabErrors_5642_);
lean_ctor_set_uint8(v___x_5645_, sizeof(void*)*3 + 3, v_isRecordingDeps_5643_);
lean_inc(v_a_5629_);
v___x_5646_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5629_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___x_5645_, v___y_5619_);
lean_dec_ref_known(v___x_5645_, 3);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_dec_ref_known(v___x_5646_, 1);
v_a_5622_ = v___x_5628_;
goto v___jp_5621_;
}
else
{
return v___x_5646_;
}
}
else
{
lean_dec(v_val_5635_);
return v___x_5637_;
}
}
else
{
lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; 
lean_dec(v___x_5634_);
v___x_5647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5648_ = l_Lean_indentExpr(v_a_5631_);
v___x_5649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5647_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5649_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_dec_ref_known(v___x_5650_, 1);
v_a_5622_ = v___x_5628_;
goto v___jp_5621_;
}
else
{
return v___x_5650_;
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_dec(v_a_5631_);
v_a_5651_ = lean_ctor_get(v___x_5632_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5632_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5632_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5632_);
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
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
v_a_5659_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5630_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5630_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
v___jp_5621_:
{
size_t v___x_5623_; size_t v___x_5624_; 
v___x_5623_ = ((size_t)1ULL);
v___x_5624_ = lean_usize_add(v_i_5612_, v___x_5623_);
v_i_5612_ = v___x_5624_;
v_b_5613_ = v_a_5622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5667_, lean_object* v_sz_5668_, lean_object* v_i_5669_, lean_object* v_b_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
size_t v_sz_boxed_5678_; size_t v_i_boxed_5679_; lean_object* v_res_5680_; 
v_sz_boxed_5678_ = lean_unbox_usize(v_sz_5668_);
lean_dec(v_sz_5668_);
v_i_boxed_5679_ = lean_unbox_usize(v_i_5669_);
lean_dec(v_i_5669_);
v_res_5680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5667_, v_sz_boxed_5678_, v_i_boxed_5679_, v_b_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec_ref(v_as_5667_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5681_, size_t v_i_5682_, size_t v_stop_5683_, lean_object* v_b_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_){
_start:
{
uint8_t v___x_5690_; 
v___x_5690_ = lean_usize_dec_eq(v_i_5682_, v_stop_5683_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = lean_array_uget_borrowed(v_as_5681_, v_i_5682_);
lean_inc(v___x_5691_);
v___x_5692_ = l_Lean_MVarId_getType(v___x_5691_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_object* v_a_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; 
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_a_5693_);
lean_dec_ref_known(v___x_5692_, 1);
v___x_5694_ = l_Lean_Expr_mdataExpr_x21(v_a_5693_);
lean_dec(v_a_5693_);
lean_inc(v___x_5691_);
v___x_5695_ = l_Lean_MVarId_setType___redArg(v___x_5691_, v___x_5694_, v___y_5686_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v_a_5696_; size_t v___x_5697_; size_t v___x_5698_; 
v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
lean_inc(v_a_5696_);
lean_dec_ref_known(v___x_5695_, 1);
v___x_5697_ = ((size_t)1ULL);
v___x_5698_ = lean_usize_add(v_i_5682_, v___x_5697_);
v_i_5682_ = v___x_5698_;
v_b_5684_ = v_a_5696_;
goto _start;
}
else
{
return v___x_5695_;
}
}
else
{
lean_object* v_a_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5707_; 
v_a_5700_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5707_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5707_ == 0)
{
v___x_5702_ = v___x_5692_;
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_a_5700_);
lean_dec(v___x_5692_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v___x_5705_; 
if (v_isShared_5703_ == 0)
{
v___x_5705_ = v___x_5702_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
}
}
}
}
else
{
lean_object* v___x_5708_; 
v___x_5708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5708_, 0, v_b_5684_);
return v___x_5708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5709_, lean_object* v_i_5710_, lean_object* v_stop_5711_, lean_object* v_b_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_){
_start:
{
size_t v_i_boxed_5718_; size_t v_stop_boxed_5719_; lean_object* v_res_5720_; 
v_i_boxed_5718_ = lean_unbox_usize(v_i_5710_);
lean_dec(v_i_5710_);
v_stop_boxed_5719_ = lean_unbox_usize(v_stop_5711_);
lean_dec(v_stop_5711_);
v_res_5720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5709_, v_i_boxed_5718_, v_stop_boxed_5719_, v_b_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec_ref(v_as_5709_);
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5721_, lean_object* v___x_5722_, lean_object* v___x_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v___x_5731_; size_t v_sz_5732_; size_t v___x_5733_; lean_object* v___x_5734_; 
v___x_5731_ = lean_box(0);
v_sz_5732_ = lean_array_size(v___x_5722_);
v___x_5733_ = ((size_t)0ULL);
v___x_5734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5722_, v_sz_5732_, v___x_5733_, v___x_5731_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec_ref(v___x_5722_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5741_ == 0)
{
lean_object* v_unused_5742_; 
v_unused_5742_ = lean_ctor_get(v___x_5734_, 0);
lean_dec(v_unused_5742_);
v___x_5736_ = v___x_5734_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v___x_5734_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 0, v___x_5731_);
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5731_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
else
{
return v___x_5734_;
}
}
else
{
lean_object* v_val_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5811_; 
v_val_5743_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5811_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5811_ == 0)
{
v___x_5745_ = v___x_5721_;
v_isShared_5746_ = v_isSharedCheck_5811_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_val_5743_);
lean_dec(v___x_5721_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5811_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v_ref_5747_; lean_object* v_tactic_5748_; lean_object* v_toCold_5749_; lean_object* v_currRecDepth_5750_; lean_object* v_ref_5751_; uint16_t v_optionFlags_5752_; uint8_t v_suppressElabErrors_5753_; uint8_t v_isRecordingDeps_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v_ref_5757_; lean_object* v___x_5758_; lean_object* v___y_5784_; lean_object* v___y_5801_; uint8_t v___x_5802_; 
v_ref_5747_ = lean_ctor_get(v_val_5743_, 0);
lean_inc(v_ref_5747_);
v_tactic_5748_ = lean_ctor_get(v_val_5743_, 1);
lean_inc(v_tactic_5748_);
lean_dec(v_val_5743_);
v_toCold_5749_ = lean_ctor_get(v___y_5728_, 0);
v_currRecDepth_5750_ = lean_ctor_get(v___y_5728_, 1);
v_ref_5751_ = lean_ctor_get(v___y_5728_, 2);
v_optionFlags_5752_ = lean_ctor_get_uint16(v___y_5728_, sizeof(void*)*3);
v_suppressElabErrors_5753_ = lean_ctor_get_uint8(v___y_5728_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5754_ = lean_ctor_get_uint8(v___y_5728_, sizeof(void*)*3 + 3);
v___x_5755_ = lean_unsigned_to_nat(0u);
v___x_5756_ = lean_array_get_size(v___x_5722_);
v_ref_5757_ = l_Lean_replaceRef(v_ref_5747_, v_ref_5751_);
lean_inc(v_currRecDepth_5750_);
lean_inc_ref(v_toCold_5749_);
v___x_5758_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5758_, 0, v_toCold_5749_);
lean_ctor_set(v___x_5758_, 1, v_currRecDepth_5750_);
lean_ctor_set(v___x_5758_, 2, v_ref_5757_);
lean_ctor_set_uint16(v___x_5758_, sizeof(void*)*3, v_optionFlags_5752_);
lean_ctor_set_uint8(v___x_5758_, sizeof(void*)*3 + 2, v_suppressElabErrors_5753_);
lean_ctor_set_uint8(v___x_5758_, sizeof(void*)*3 + 3, v_isRecordingDeps_5754_);
v___x_5802_ = lean_nat_dec_lt(v___x_5755_, v___x_5756_);
if (v___x_5802_ == 0)
{
goto v___jp_5785_;
}
else
{
lean_object* v___x_5803_; uint8_t v___x_5804_; 
v___x_5803_ = lean_box(0);
v___x_5804_ = lean_nat_dec_le(v___x_5756_, v___x_5756_);
if (v___x_5804_ == 0)
{
if (v___x_5802_ == 0)
{
goto v___jp_5785_;
}
else
{
size_t v___x_5805_; size_t v___x_5806_; lean_object* v___x_5807_; 
v___x_5805_ = ((size_t)0ULL);
v___x_5806_ = lean_usize_of_nat(v___x_5756_);
v___x_5807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5722_, v___x_5805_, v___x_5806_, v___x_5803_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
v___y_5801_ = v___x_5807_;
goto v___jp_5800_;
}
}
else
{
size_t v___x_5808_; size_t v___x_5809_; lean_object* v___x_5810_; 
v___x_5808_ = ((size_t)0ULL);
v___x_5809_ = lean_usize_of_nat(v___x_5756_);
v___x_5810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5722_, v___x_5808_, v___x_5809_, v___x_5803_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
v___y_5801_ = v___x_5810_;
goto v___jp_5800_;
}
}
v___jp_5759_:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___f_5762_; lean_object* v___x_5763_; 
v___x_5760_ = lean_array_get(v___x_5723_, v___x_5722_, v___x_5755_);
v___x_5761_ = lean_array_to_list(v___x_5722_);
v___f_5762_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5762_, 0, v___x_5761_);
lean_closure_set(v___f_5762_, 1, v_tactic_5748_);
lean_closure_set(v___f_5762_, 2, v_ref_5747_);
v___x_5763_ = l_Lean_Elab_Tactic_run(v___x_5760_, v___f_5762_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5774_; 
v_a_5764_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5766_ = v___x_5763_;
v_isShared_5767_ = v_isSharedCheck_5774_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5763_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5774_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
uint8_t v___x_5768_; 
v___x_5768_ = l_List_isEmpty___redArg(v_a_5764_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; 
lean_del_object(v___x_5766_);
v___x_5769_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5764_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
lean_dec_ref_known(v___x_5758_, 3);
return v___x_5769_;
}
else
{
lean_object* v___x_5770_; lean_object* v___x_5772_; 
lean_dec(v_a_5764_);
lean_dec_ref_known(v___x_5758_, 3);
v___x_5770_ = lean_box(0);
if (v_isShared_5767_ == 0)
{
lean_ctor_set(v___x_5766_, 0, v___x_5770_);
v___x_5772_ = v___x_5766_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
else
{
lean_object* v_a_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5782_; 
lean_dec_ref_known(v___x_5758_, 3);
v_a_5775_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5777_ = v___x_5763_;
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_a_5775_);
lean_dec(v___x_5763_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5780_; 
if (v_isShared_5778_ == 0)
{
v___x_5780_ = v___x_5777_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
v___jp_5783_:
{
if (lean_obj_tag(v___y_5784_) == 0)
{
lean_dec_ref_known(v___y_5784_, 1);
goto v___jp_5759_;
}
else
{
lean_dec_ref_known(v___x_5758_, 3);
lean_dec(v_tactic_5748_);
lean_dec(v_ref_5747_);
lean_dec_ref(v___x_5722_);
return v___y_5784_;
}
}
v___jp_5785_:
{
uint8_t v___x_5786_; 
v___x_5786_ = lean_nat_dec_eq(v___x_5756_, v___x_5755_);
if (v___x_5786_ == 0)
{
uint8_t v___x_5787_; 
lean_del_object(v___x_5745_);
v___x_5787_ = lean_nat_dec_lt(v___x_5755_, v___x_5756_);
if (v___x_5787_ == 0)
{
goto v___jp_5759_;
}
else
{
lean_object* v___x_5788_; uint8_t v___x_5789_; 
v___x_5788_ = lean_box(0);
v___x_5789_ = lean_nat_dec_le(v___x_5756_, v___x_5756_);
if (v___x_5789_ == 0)
{
if (v___x_5787_ == 0)
{
goto v___jp_5759_;
}
else
{
size_t v___x_5790_; size_t v___x_5791_; lean_object* v___x_5792_; 
v___x_5790_ = ((size_t)0ULL);
v___x_5791_ = lean_usize_of_nat(v___x_5756_);
v___x_5792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5722_, v___x_5790_, v___x_5791_, v___x_5788_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
v___y_5784_ = v___x_5792_;
goto v___jp_5783_;
}
}
else
{
size_t v___x_5793_; size_t v___x_5794_; lean_object* v___x_5795_; 
v___x_5793_ = ((size_t)0ULL);
v___x_5794_ = lean_usize_of_nat(v___x_5756_);
v___x_5795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5722_, v___x_5793_, v___x_5794_, v___x_5788_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___x_5758_, v___y_5729_);
v___y_5784_ = v___x_5795_;
goto v___jp_5783_;
}
}
}
else
{
lean_object* v___x_5796_; lean_object* v___x_5798_; 
lean_dec_ref_known(v___x_5758_, 3);
lean_dec(v_tactic_5748_);
lean_dec(v_ref_5747_);
lean_dec_ref(v___x_5722_);
v___x_5796_ = lean_box(0);
if (v_isShared_5746_ == 0)
{
lean_ctor_set_tag(v___x_5745_, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5796_);
v___x_5798_ = v___x_5745_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5796_);
v___x_5798_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
return v___x_5798_;
}
}
}
v___jp_5800_:
{
if (lean_obj_tag(v___y_5801_) == 0)
{
lean_dec_ref_known(v___y_5801_, 1);
goto v___jp_5785_;
}
else
{
lean_dec_ref_known(v___x_5758_, 3);
lean_dec(v_tactic_5748_);
lean_dec(v_ref_5747_);
lean_del_object(v___x_5745_);
lean_dec_ref(v___x_5722_);
return v___y_5801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5812_, lean_object* v___x_5813_, lean_object* v___x_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5812_, v___x_5813_, v___x_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___x_5814_);
return v_res_5822_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5823_){
_start:
{
uint8_t v___x_5824_; 
v___x_5824_ = 0;
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5825_){
_start:
{
uint8_t v_res_5826_; lean_object* v_r_5827_; 
v_res_5826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5825_);
lean_dec(v_x_5825_);
v_r_5827_ = lean_box(v_res_5826_);
return v_r_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5834_, size_t v_sz_5835_, size_t v_i_5836_, lean_object* v_b_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_){
_start:
{
uint8_t v___x_5843_; 
v___x_5843_ = lean_usize_dec_lt(v_i_5836_, v_sz_5835_);
if (v___x_5843_ == 0)
{
lean_object* v___x_5844_; 
v___x_5844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5844_, 0, v_b_5837_);
return v___x_5844_;
}
else
{
lean_object* v_snd_5845_; lean_object* v_fst_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5918_; 
v_snd_5845_ = lean_ctor_get(v_b_5837_, 1);
v_fst_5846_ = lean_ctor_get(v_b_5837_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v_b_5837_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5848_ = v_b_5837_;
v_isShared_5849_ = v_isSharedCheck_5918_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_snd_5845_);
lean_inc(v_fst_5846_);
lean_dec(v_b_5837_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5918_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v_array_5850_; lean_object* v_start_5851_; lean_object* v_stop_5852_; uint8_t v___x_5853_; 
v_array_5850_ = lean_ctor_get(v_snd_5845_, 0);
v_start_5851_ = lean_ctor_get(v_snd_5845_, 1);
v_stop_5852_ = lean_ctor_get(v_snd_5845_, 2);
v___x_5853_ = lean_nat_dec_lt(v_start_5851_, v_stop_5852_);
if (v___x_5853_ == 0)
{
lean_object* v___x_5855_; 
if (v_isShared_5849_ == 0)
{
v___x_5855_ = v___x_5848_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_fst_5846_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_snd_5845_);
v___x_5855_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
lean_object* v___x_5856_; 
v___x_5856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
return v___x_5856_;
}
}
else
{
lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5914_; 
lean_inc(v_stop_5852_);
lean_inc(v_start_5851_);
lean_inc_ref(v_array_5850_);
v_isSharedCheck_5914_ = !lean_is_exclusive(v_snd_5845_);
if (v_isSharedCheck_5914_ == 0)
{
lean_object* v_unused_5915_; lean_object* v_unused_5916_; lean_object* v_unused_5917_; 
v_unused_5915_ = lean_ctor_get(v_snd_5845_, 2);
lean_dec(v_unused_5915_);
v_unused_5916_ = lean_ctor_get(v_snd_5845_, 1);
lean_dec(v_unused_5916_);
v_unused_5917_ = lean_ctor_get(v_snd_5845_, 0);
lean_dec(v_unused_5917_);
v___x_5859_ = v_snd_5845_;
v_isShared_5860_ = v_isSharedCheck_5914_;
goto v_resetjp_5858_;
}
else
{
lean_dec(v_snd_5845_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5914_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
lean_object* v_array_5861_; lean_object* v_start_5862_; lean_object* v_stop_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5868_; 
v_array_5861_ = lean_ctor_get(v_fst_5846_, 0);
v_start_5862_ = lean_ctor_get(v_fst_5846_, 1);
v_stop_5863_ = lean_ctor_get(v_fst_5846_, 2);
v___x_5864_ = lean_array_fget(v_array_5850_, v_start_5851_);
v___x_5865_ = lean_unsigned_to_nat(1u);
v___x_5866_ = lean_nat_add(v_start_5851_, v___x_5865_);
lean_dec(v_start_5851_);
if (v_isShared_5860_ == 0)
{
lean_ctor_set(v___x_5859_, 1, v___x_5866_);
v___x_5868_ = v___x_5859_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_array_5850_);
lean_ctor_set(v_reuseFailAlloc_5913_, 1, v___x_5866_);
lean_ctor_set(v_reuseFailAlloc_5913_, 2, v_stop_5852_);
v___x_5868_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
uint8_t v___x_5869_; 
v___x_5869_ = lean_nat_dec_lt(v_start_5862_, v_stop_5863_);
if (v___x_5869_ == 0)
{
lean_object* v___x_5871_; 
lean_dec(v___x_5864_);
if (v_isShared_5849_ == 0)
{
lean_ctor_set(v___x_5848_, 1, v___x_5868_);
v___x_5871_ = v___x_5848_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_fst_5846_);
lean_ctor_set(v_reuseFailAlloc_5873_, 1, v___x_5868_);
v___x_5871_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
lean_object* v___x_5872_; 
v___x_5872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
return v___x_5872_;
}
}
else
{
lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5909_; 
lean_inc(v_stop_5863_);
lean_inc(v_start_5862_);
lean_inc_ref(v_array_5861_);
v_isSharedCheck_5909_ = !lean_is_exclusive(v_fst_5846_);
if (v_isSharedCheck_5909_ == 0)
{
lean_object* v_unused_5910_; lean_object* v_unused_5911_; lean_object* v_unused_5912_; 
v_unused_5910_ = lean_ctor_get(v_fst_5846_, 2);
lean_dec(v_unused_5910_);
v_unused_5911_ = lean_ctor_get(v_fst_5846_, 1);
lean_dec(v_unused_5911_);
v_unused_5912_ = lean_ctor_get(v_fst_5846_, 0);
lean_dec(v_unused_5912_);
v___x_5875_ = v_fst_5846_;
v_isShared_5876_ = v_isSharedCheck_5909_;
goto v_resetjp_5874_;
}
else
{
lean_dec(v_fst_5846_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5909_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___f_5877_; lean_object* v___x_5878_; lean_object* v_a_5879_; lean_object* v___x_5880_; lean_object* v___y_5881_; lean_object* v___x_5882_; lean_object* v___x_5884_; 
v___f_5877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5878_ = lean_box(0);
v_a_5879_ = lean_array_uget_borrowed(v_as_5834_, v_i_5836_);
v___x_5880_ = lean_array_fget_borrowed(v_array_5861_, v_start_5862_);
lean_inc(v___x_5880_);
v___y_5881_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5881_, 0, v___x_5864_);
lean_closure_set(v___y_5881_, 1, v___x_5880_);
lean_closure_set(v___y_5881_, 2, v___x_5878_);
v___x_5882_ = lean_nat_add(v_start_5862_, v___x_5865_);
lean_dec(v_start_5862_);
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 1, v___x_5882_);
v___x_5884_ = v___x_5875_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_array_5861_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v___x_5882_);
lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_stop_5863_);
v___x_5884_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; uint8_t v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
lean_inc(v_a_5879_);
v___x_5885_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5885_, 0, lean_box(0));
lean_closure_set(v___x_5885_, 1, v_a_5879_);
lean_closure_set(v___x_5885_, 2, v___y_5881_);
v___x_5886_ = lean_box(0);
v___x_5887_ = lean_box(0);
v___x_5888_ = lean_box(1);
v___x_5889_ = 0;
v___x_5890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5891_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5891_, 0, v___x_5886_);
lean_ctor_set(v___x_5891_, 1, v___x_5887_);
lean_ctor_set(v___x_5891_, 2, v___x_5886_);
lean_ctor_set(v___x_5891_, 3, v___f_5877_);
lean_ctor_set(v___x_5891_, 4, v___x_5888_);
lean_ctor_set(v___x_5891_, 5, v___x_5888_);
lean_ctor_set(v___x_5891_, 6, v___x_5886_);
lean_ctor_set(v___x_5891_, 7, v___x_5890_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8, v___x_5869_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 1, v___x_5869_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 2, v___x_5869_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 3, v___x_5869_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 4, v___x_5889_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 5, v___x_5889_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 6, v___x_5889_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 7, v___x_5889_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 8, v___x_5869_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 9, v___x_5889_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*8 + 10, v___x_5869_);
v___x_5892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5893_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5885_, v___x_5891_, v___x_5892_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v___x_5895_; 
lean_dec_ref_known(v___x_5893_, 1);
if (v_isShared_5849_ == 0)
{
lean_ctor_set(v___x_5848_, 1, v___x_5868_);
lean_ctor_set(v___x_5848_, 0, v___x_5884_);
v___x_5895_ = v___x_5848_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5884_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v___x_5868_);
v___x_5895_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
size_t v___x_5896_; size_t v___x_5897_; 
v___x_5896_ = ((size_t)1ULL);
v___x_5897_ = lean_usize_add(v_i_5836_, v___x_5896_);
v_i_5836_ = v___x_5897_;
v_b_5837_ = v___x_5895_;
goto _start;
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_dec_ref(v___x_5884_);
lean_dec_ref(v___x_5868_);
lean_del_object(v___x_5848_);
v_a_5900_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5893_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5893_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5919_, lean_object* v_sz_5920_, lean_object* v_i_5921_, lean_object* v_b_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
size_t v_sz_boxed_5928_; size_t v_i_boxed_5929_; lean_object* v_res_5930_; 
v_sz_boxed_5928_ = lean_unbox_usize(v_sz_5920_);
lean_dec(v_sz_5920_);
v_i_boxed_5929_ = lean_unbox_usize(v_i_5921_);
lean_dec(v_i_5921_);
v_res_5930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5919_, v_sz_boxed_5928_, v_i_boxed_5929_, v_b_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec_ref(v_as_5919_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5931_, lean_object* v_decrTactics_5932_, lean_object* v_argsPacker_5933_, lean_object* v_funNames_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_){
_start:
{
lean_object* v___x_5940_; 
lean_inc_ref(v_value_5931_);
v___x_5940_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5931_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5940_) == 0)
{
lean_object* v_a_5941_; lean_object* v___x_5942_; 
v_a_5941_ = lean_ctor_get(v___x_5940_, 0);
lean_inc(v_a_5941_);
lean_dec_ref_known(v___x_5940_, 1);
v___x_5942_ = l_Lean_Elab_WF_assignSubsumed(v_a_5941_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
lean_dec(v_a_5941_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref_known(v___x_5942_, 1);
v___x_5944_ = lean_array_get_size(v_decrTactics_5932_);
v___x_5945_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5933_, v___x_5944_, v_a_5943_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
lean_dec(v_a_5943_);
if (lean_obj_tag(v___x_5945_) == 0)
{
lean_object* v_a_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; size_t v_sz_5952_; size_t v___x_5953_; lean_object* v___x_5954_; 
v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
lean_inc(v_a_5946_);
lean_dec_ref_known(v___x_5945_, 1);
v___x_5947_ = lean_unsigned_to_nat(0u);
v___x_5948_ = lean_array_get_size(v_a_5946_);
v___x_5949_ = l_Array_toSubarray___redArg(v_a_5946_, v___x_5947_, v___x_5948_);
v___x_5950_ = l_Array_toSubarray___redArg(v_decrTactics_5932_, v___x_5947_, v___x_5944_);
v___x_5951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5949_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
v_sz_5952_ = lean_array_size(v_funNames_5934_);
v___x_5953_ = ((size_t)0ULL);
v___x_5954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5934_, v_sz_5952_, v___x_5953_, v___x_5951_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5954_) == 0)
{
lean_object* v___x_5955_; 
lean_dec_ref_known(v___x_5954_, 1);
v___x_5955_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5931_, v___y_5936_);
return v___x_5955_;
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5963_; 
lean_dec_ref(v_value_5931_);
v_a_5956_ = lean_ctor_get(v___x_5954_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5958_ = v___x_5954_;
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5954_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
}
else
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5971_; 
lean_dec_ref(v_decrTactics_5932_);
lean_dec_ref(v_value_5931_);
v_a_5964_ = lean_ctor_get(v___x_5945_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v___x_5945_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5966_ = v___x_5945_;
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5945_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
if (v_isShared_5967_ == 0)
{
v___x_5969_ = v___x_5966_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
else
{
lean_object* v_a_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5979_; 
lean_dec_ref(v_decrTactics_5932_);
lean_dec_ref(v_value_5931_);
v_a_5972_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_5979_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5974_ = v___x_5942_;
v_isShared_5975_ = v_isSharedCheck_5979_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_a_5972_);
lean_dec(v___x_5942_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5979_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v___x_5977_; 
if (v_isShared_5975_ == 0)
{
v___x_5977_ = v___x_5974_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_a_5972_);
v___x_5977_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
return v___x_5977_;
}
}
}
}
else
{
lean_object* v_a_5980_; lean_object* v___x_5982_; uint8_t v_isShared_5983_; uint8_t v_isSharedCheck_5987_; 
lean_dec_ref(v_decrTactics_5932_);
lean_dec_ref(v_value_5931_);
v_a_5980_ = lean_ctor_get(v___x_5940_, 0);
v_isSharedCheck_5987_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_5987_ == 0)
{
v___x_5982_ = v___x_5940_;
v_isShared_5983_ = v_isSharedCheck_5987_;
goto v_resetjp_5981_;
}
else
{
lean_inc(v_a_5980_);
lean_dec(v___x_5940_);
v___x_5982_ = lean_box(0);
v_isShared_5983_ = v_isSharedCheck_5987_;
goto v_resetjp_5981_;
}
v_resetjp_5981_:
{
lean_object* v___x_5985_; 
if (v_isShared_5983_ == 0)
{
v___x_5985_ = v___x_5982_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5986_; 
v_reuseFailAlloc_5986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5986_, 0, v_a_5980_);
v___x_5985_ = v_reuseFailAlloc_5986_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
return v___x_5985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5988_, lean_object* v_decrTactics_5989_, lean_object* v_argsPacker_5990_, lean_object* v_funNames_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5988_, v_decrTactics_5989_, v_argsPacker_5990_, v_funNames_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
lean_dec(v___y_5995_);
lean_dec_ref(v___y_5994_);
lean_dec(v___y_5993_);
lean_dec_ref(v___y_5992_);
lean_dec_ref(v_funNames_5991_);
lean_dec_ref(v_argsPacker_5990_);
return v_res_5997_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5998_, uint8_t v_isExporting_5999_, lean_object* v___x_6000_, lean_object* v___y_6001_, lean_object* v___x_6002_, lean_object* v_a_x3f_6003_){
_start:
{
lean_object* v___x_6005_; lean_object* v_env_6006_; lean_object* v_nextMacroScope_6007_; lean_object* v_ngen_6008_; lean_object* v_auxDeclNGen_6009_; lean_object* v_traceState_6010_; lean_object* v_recordedDeps_6011_; lean_object* v_messages_6012_; lean_object* v_infoState_6013_; lean_object* v_snapshotTasks_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6039_; 
v___x_6005_ = lean_st_ref_take(v___y_5998_);
v_env_6006_ = lean_ctor_get(v___x_6005_, 0);
v_nextMacroScope_6007_ = lean_ctor_get(v___x_6005_, 1);
v_ngen_6008_ = lean_ctor_get(v___x_6005_, 2);
v_auxDeclNGen_6009_ = lean_ctor_get(v___x_6005_, 3);
v_traceState_6010_ = lean_ctor_get(v___x_6005_, 4);
v_recordedDeps_6011_ = lean_ctor_get(v___x_6005_, 6);
v_messages_6012_ = lean_ctor_get(v___x_6005_, 7);
v_infoState_6013_ = lean_ctor_get(v___x_6005_, 8);
v_snapshotTasks_6014_ = lean_ctor_get(v___x_6005_, 9);
v_isSharedCheck_6039_ = !lean_is_exclusive(v___x_6005_);
if (v_isSharedCheck_6039_ == 0)
{
lean_object* v_unused_6040_; 
v_unused_6040_ = lean_ctor_get(v___x_6005_, 5);
lean_dec(v_unused_6040_);
v___x_6016_ = v___x_6005_;
v_isShared_6017_ = v_isSharedCheck_6039_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_snapshotTasks_6014_);
lean_inc(v_infoState_6013_);
lean_inc(v_messages_6012_);
lean_inc(v_recordedDeps_6011_);
lean_inc(v_traceState_6010_);
lean_inc(v_auxDeclNGen_6009_);
lean_inc(v_ngen_6008_);
lean_inc(v_nextMacroScope_6007_);
lean_inc(v_env_6006_);
lean_dec(v___x_6005_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6039_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6018_; lean_object* v___x_6020_; 
v___x_6018_ = l_Lean_Environment_setExporting(v_env_6006_, v_isExporting_5999_);
if (v_isShared_6017_ == 0)
{
lean_ctor_set(v___x_6016_, 5, v___x_6000_);
lean_ctor_set(v___x_6016_, 0, v___x_6018_);
v___x_6020_ = v___x_6016_;
goto v_reusejp_6019_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6018_);
lean_ctor_set(v_reuseFailAlloc_6038_, 1, v_nextMacroScope_6007_);
lean_ctor_set(v_reuseFailAlloc_6038_, 2, v_ngen_6008_);
lean_ctor_set(v_reuseFailAlloc_6038_, 3, v_auxDeclNGen_6009_);
lean_ctor_set(v_reuseFailAlloc_6038_, 4, v_traceState_6010_);
lean_ctor_set(v_reuseFailAlloc_6038_, 5, v___x_6000_);
lean_ctor_set(v_reuseFailAlloc_6038_, 6, v_recordedDeps_6011_);
lean_ctor_set(v_reuseFailAlloc_6038_, 7, v_messages_6012_);
lean_ctor_set(v_reuseFailAlloc_6038_, 8, v_infoState_6013_);
lean_ctor_set(v_reuseFailAlloc_6038_, 9, v_snapshotTasks_6014_);
v___x_6020_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6019_;
}
v_reusejp_6019_:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v_mctx_6023_; lean_object* v_zetaDeltaFVarIds_6024_; lean_object* v_postponed_6025_; lean_object* v_diag_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6036_; 
v___x_6021_ = lean_st_ref_put(v___y_5998_, v___x_6020_);
v___x_6022_ = lean_st_ref_take(v___y_6001_);
v_mctx_6023_ = lean_ctor_get(v___x_6022_, 0);
v_zetaDeltaFVarIds_6024_ = lean_ctor_get(v___x_6022_, 2);
v_postponed_6025_ = lean_ctor_get(v___x_6022_, 3);
v_diag_6026_ = lean_ctor_get(v___x_6022_, 4);
v_isSharedCheck_6036_ = !lean_is_exclusive(v___x_6022_);
if (v_isSharedCheck_6036_ == 0)
{
lean_object* v_unused_6037_; 
v_unused_6037_ = lean_ctor_get(v___x_6022_, 1);
lean_dec(v_unused_6037_);
v___x_6028_ = v___x_6022_;
v_isShared_6029_ = v_isSharedCheck_6036_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_diag_6026_);
lean_inc(v_postponed_6025_);
lean_inc(v_zetaDeltaFVarIds_6024_);
lean_inc(v_mctx_6023_);
lean_dec(v___x_6022_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6036_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
lean_object* v___x_6030_; lean_object* v___x_6032_; 
v___x_6030_ = lean_box(0);
if (v_isShared_6029_ == 0)
{
lean_ctor_set(v___x_6028_, 1, v___x_6002_);
v___x_6032_ = v___x_6028_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_mctx_6023_);
lean_ctor_set(v_reuseFailAlloc_6035_, 1, v___x_6002_);
lean_ctor_set(v_reuseFailAlloc_6035_, 2, v_zetaDeltaFVarIds_6024_);
lean_ctor_set(v_reuseFailAlloc_6035_, 3, v_postponed_6025_);
lean_ctor_set(v_reuseFailAlloc_6035_, 4, v_diag_6026_);
v___x_6032_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6033_ = lean_st_ref_put(v___y_6001_, v___x_6032_);
v___x_6034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6030_);
return v___x_6034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6041_, lean_object* v_isExporting_6042_, lean_object* v___x_6043_, lean_object* v___y_6044_, lean_object* v___x_6045_, lean_object* v_a_x3f_6046_, lean_object* v___y_6047_){
_start:
{
uint8_t v_isExporting_boxed_6048_; lean_object* v_res_6049_; 
v_isExporting_boxed_6048_ = lean_unbox(v_isExporting_6042_);
v_res_6049_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6041_, v_isExporting_boxed_6048_, v___x_6043_, v___y_6044_, v___x_6045_, v_a_x3f_6046_);
lean_dec(v_a_x3f_6046_);
lean_dec(v___y_6044_);
lean_dec(v___y_6041_);
return v_res_6049_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_6051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
return v___x_6051_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6052_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
return v___x_6053_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6054_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6055_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
lean_ctor_set(v___x_6055_, 2, v___x_6054_);
lean_ctor_set(v___x_6055_, 3, v___x_6054_);
lean_ctor_set(v___x_6055_, 4, v___x_6054_);
lean_ctor_set(v___x_6055_, 5, v___x_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6056_, uint8_t v_isExporting_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_){
_start:
{
lean_object* v___x_6063_; lean_object* v_env_6064_; lean_object* v___x_6065_; uint8_t v_isModule_6066_; 
v___x_6063_ = lean_st_ref_get(v___y_6061_);
v_env_6064_ = lean_ctor_get(v___x_6063_, 0);
lean_inc_ref(v_env_6064_);
lean_dec(v___x_6063_);
v___x_6065_ = l_Lean_Environment_header(v_env_6064_);
v_isModule_6066_ = lean_ctor_get_uint8(v___x_6065_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_6065_);
if (v_isModule_6066_ == 0)
{
lean_object* v___x_6067_; 
lean_dec_ref(v_env_6064_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
v___x_6067_ = lean_apply_5(v_x_6056_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, lean_box(0));
return v___x_6067_;
}
else
{
uint8_t v_isExporting_6068_; 
v_isExporting_6068_ = lean_ctor_get_uint8(v_env_6064_, sizeof(void*)*13);
lean_dec_ref(v_env_6064_);
if (v_isExporting_6057_ == 0)
{
if (v_isExporting_6068_ == 0)
{
lean_object* v___x_6135_; 
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
v___x_6135_ = lean_apply_5(v_x_6056_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, lean_box(0));
return v___x_6135_;
}
else
{
goto v___jp_6069_;
}
}
else
{
if (v_isExporting_6068_ == 0)
{
goto v___jp_6069_;
}
else
{
lean_object* v___x_6136_; 
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
v___x_6136_ = lean_apply_5(v_x_6056_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, lean_box(0));
return v___x_6136_;
}
}
v___jp_6069_:
{
lean_object* v___x_6070_; lean_object* v_env_6071_; lean_object* v_nextMacroScope_6072_; lean_object* v_ngen_6073_; lean_object* v_auxDeclNGen_6074_; lean_object* v_traceState_6075_; lean_object* v_recordedDeps_6076_; lean_object* v_messages_6077_; lean_object* v_infoState_6078_; lean_object* v_snapshotTasks_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6133_; 
v___x_6070_ = lean_st_ref_take(v___y_6061_);
v_env_6071_ = lean_ctor_get(v___x_6070_, 0);
v_nextMacroScope_6072_ = lean_ctor_get(v___x_6070_, 1);
v_ngen_6073_ = lean_ctor_get(v___x_6070_, 2);
v_auxDeclNGen_6074_ = lean_ctor_get(v___x_6070_, 3);
v_traceState_6075_ = lean_ctor_get(v___x_6070_, 4);
v_recordedDeps_6076_ = lean_ctor_get(v___x_6070_, 6);
v_messages_6077_ = lean_ctor_get(v___x_6070_, 7);
v_infoState_6078_ = lean_ctor_get(v___x_6070_, 8);
v_snapshotTasks_6079_ = lean_ctor_get(v___x_6070_, 9);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6070_);
if (v_isSharedCheck_6133_ == 0)
{
lean_object* v_unused_6134_; 
v_unused_6134_ = lean_ctor_get(v___x_6070_, 5);
lean_dec(v_unused_6134_);
v___x_6081_ = v___x_6070_;
v_isShared_6082_ = v_isSharedCheck_6133_;
goto v_resetjp_6080_;
}
else
{
lean_inc(v_snapshotTasks_6079_);
lean_inc(v_infoState_6078_);
lean_inc(v_messages_6077_);
lean_inc(v_recordedDeps_6076_);
lean_inc(v_traceState_6075_);
lean_inc(v_auxDeclNGen_6074_);
lean_inc(v_ngen_6073_);
lean_inc(v_nextMacroScope_6072_);
lean_inc(v_env_6071_);
lean_dec(v___x_6070_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6133_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6086_; 
v___x_6083_ = l_Lean_Environment_setExporting(v_env_6071_, v_isExporting_6057_);
v___x_6084_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 5, v___x_6084_);
lean_ctor_set(v___x_6081_, 0, v___x_6083_);
v___x_6086_ = v___x_6081_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v___x_6083_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v_nextMacroScope_6072_);
lean_ctor_set(v_reuseFailAlloc_6132_, 2, v_ngen_6073_);
lean_ctor_set(v_reuseFailAlloc_6132_, 3, v_auxDeclNGen_6074_);
lean_ctor_set(v_reuseFailAlloc_6132_, 4, v_traceState_6075_);
lean_ctor_set(v_reuseFailAlloc_6132_, 5, v___x_6084_);
lean_ctor_set(v_reuseFailAlloc_6132_, 6, v_recordedDeps_6076_);
lean_ctor_set(v_reuseFailAlloc_6132_, 7, v_messages_6077_);
lean_ctor_set(v_reuseFailAlloc_6132_, 8, v_infoState_6078_);
lean_ctor_set(v_reuseFailAlloc_6132_, 9, v_snapshotTasks_6079_);
v___x_6086_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v_mctx_6089_; lean_object* v_zetaDeltaFVarIds_6090_; lean_object* v_postponed_6091_; lean_object* v_diag_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6130_; 
v___x_6087_ = lean_st_ref_put(v___y_6061_, v___x_6086_);
v___x_6088_ = lean_st_ref_take(v___y_6059_);
v_mctx_6089_ = lean_ctor_get(v___x_6088_, 0);
v_zetaDeltaFVarIds_6090_ = lean_ctor_get(v___x_6088_, 2);
v_postponed_6091_ = lean_ctor_get(v___x_6088_, 3);
v_diag_6092_ = lean_ctor_get(v___x_6088_, 4);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6130_ == 0)
{
lean_object* v_unused_6131_; 
v_unused_6131_ = lean_ctor_get(v___x_6088_, 1);
lean_dec(v_unused_6131_);
v___x_6094_ = v___x_6088_;
v_isShared_6095_ = v_isSharedCheck_6130_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_diag_6092_);
lean_inc(v_postponed_6091_);
lean_inc(v_zetaDeltaFVarIds_6090_);
lean_inc(v_mctx_6089_);
lean_dec(v___x_6088_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6130_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6096_; lean_object* v___x_6098_; 
v___x_6096_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 1, v___x_6096_);
v___x_6098_ = v___x_6094_;
goto v_reusejp_6097_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_mctx_6089_);
lean_ctor_set(v_reuseFailAlloc_6129_, 1, v___x_6096_);
lean_ctor_set(v_reuseFailAlloc_6129_, 2, v_zetaDeltaFVarIds_6090_);
lean_ctor_set(v_reuseFailAlloc_6129_, 3, v_postponed_6091_);
lean_ctor_set(v_reuseFailAlloc_6129_, 4, v_diag_6092_);
v___x_6098_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6097_;
}
v_reusejp_6097_:
{
lean_object* v___x_6099_; lean_object* v_r_6100_; 
v___x_6099_ = lean_st_ref_put(v___y_6059_, v___x_6098_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
v_r_6100_ = lean_apply_5(v_x_6056_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, lean_box(0));
if (lean_obj_tag(v_r_6100_) == 0)
{
lean_object* v_a_6101_; lean_object* v___x_6103_; uint8_t v_isShared_6104_; uint8_t v_isSharedCheck_6117_; 
v_a_6101_ = lean_ctor_get(v_r_6100_, 0);
v_isSharedCheck_6117_ = !lean_is_exclusive(v_r_6100_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6103_ = v_r_6100_;
v_isShared_6104_ = v_isSharedCheck_6117_;
goto v_resetjp_6102_;
}
else
{
lean_inc(v_a_6101_);
lean_dec(v_r_6100_);
v___x_6103_ = lean_box(0);
v_isShared_6104_ = v_isSharedCheck_6117_;
goto v_resetjp_6102_;
}
v_resetjp_6102_:
{
lean_object* v___x_6106_; 
lean_inc(v_a_6101_);
if (v_isShared_6104_ == 0)
{
lean_ctor_set_tag(v___x_6103_, 1);
v___x_6106_ = v___x_6103_;
goto v_reusejp_6105_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6101_);
v___x_6106_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6105_;
}
v_reusejp_6105_:
{
lean_object* v___x_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6114_; 
v___x_6107_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6061_, v_isExporting_6068_, v___x_6084_, v___y_6059_, v___x_6096_, v___x_6106_);
lean_dec_ref(v___x_6106_);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6107_);
if (v_isSharedCheck_6114_ == 0)
{
lean_object* v_unused_6115_; 
v_unused_6115_ = lean_ctor_get(v___x_6107_, 0);
lean_dec(v_unused_6115_);
v___x_6109_ = v___x_6107_;
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
else
{
lean_dec(v___x_6107_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6112_; 
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 0, v_a_6101_);
v___x_6112_ = v___x_6109_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_a_6101_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
}
}
else
{
lean_object* v_a_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6122_; uint8_t v_isShared_6123_; uint8_t v_isSharedCheck_6127_; 
v_a_6118_ = lean_ctor_get(v_r_6100_, 0);
lean_inc(v_a_6118_);
lean_dec_ref_known(v_r_6100_, 1);
v___x_6119_ = lean_box(0);
v___x_6120_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6061_, v_isExporting_6068_, v___x_6084_, v___y_6059_, v___x_6096_, v___x_6119_);
v_isSharedCheck_6127_ = !lean_is_exclusive(v___x_6120_);
if (v_isSharedCheck_6127_ == 0)
{
lean_object* v_unused_6128_; 
v_unused_6128_ = lean_ctor_get(v___x_6120_, 0);
lean_dec(v_unused_6128_);
v___x_6122_ = v___x_6120_;
v_isShared_6123_ = v_isSharedCheck_6127_;
goto v_resetjp_6121_;
}
else
{
lean_dec(v___x_6120_);
v___x_6122_ = lean_box(0);
v_isShared_6123_ = v_isSharedCheck_6127_;
goto v_resetjp_6121_;
}
v_resetjp_6121_:
{
lean_object* v___x_6125_; 
if (v_isShared_6123_ == 0)
{
lean_ctor_set_tag(v___x_6122_, 1);
lean_ctor_set(v___x_6122_, 0, v_a_6118_);
v___x_6125_ = v___x_6122_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_a_6118_);
v___x_6125_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
return v___x_6125_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6137_, lean_object* v_isExporting_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
uint8_t v_isExporting_boxed_6144_; lean_object* v_res_6145_; 
v_isExporting_boxed_6144_ = lean_unbox(v_isExporting_6138_);
v_res_6145_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6137_, v_isExporting_boxed_6144_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
return v_res_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6146_, uint8_t v_when_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_){
_start:
{
if (v_when_6147_ == 0)
{
lean_object* v___x_6153_; 
lean_inc(v___y_6151_);
lean_inc_ref(v___y_6150_);
lean_inc(v___y_6149_);
lean_inc_ref(v___y_6148_);
v___x_6153_ = lean_apply_5(v_x_6146_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, lean_box(0));
return v___x_6153_;
}
else
{
uint8_t v___x_6154_; lean_object* v___x_6155_; 
v___x_6154_ = 0;
v___x_6155_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6146_, v___x_6154_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
return v___x_6155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6156_, lean_object* v_when_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_){
_start:
{
uint8_t v_when_boxed_6163_; lean_object* v_res_6164_; 
v_when_boxed_6163_ = lean_unbox(v_when_6157_);
v_res_6164_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6156_, v_when_boxed_6163_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6165_, lean_object* v_argsPacker_6166_, lean_object* v_decrTactics_6167_, lean_object* v_value_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_, lean_object* v_a_6172_){
_start:
{
lean_object* v___f_6174_; uint8_t v___x_6175_; lean_object* v___x_6176_; 
v___f_6174_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6174_, 0, v_value_6168_);
lean_closure_set(v___f_6174_, 1, v_decrTactics_6167_);
lean_closure_set(v___f_6174_, 2, v_argsPacker_6166_);
lean_closure_set(v___f_6174_, 3, v_funNames_6165_);
v___x_6175_ = 1;
v___x_6176_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6174_, v___x_6175_, v_a_6169_, v_a_6170_, v_a_6171_, v_a_6172_);
return v___x_6176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6177_, lean_object* v_argsPacker_6178_, lean_object* v_decrTactics_6179_, lean_object* v_value_6180_, lean_object* v_a_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_){
_start:
{
lean_object* v_res_6186_; 
v_res_6186_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6177_, v_argsPacker_6178_, v_decrTactics_6179_, v_value_6180_, v_a_6181_, v_a_6182_, v_a_6183_, v_a_6184_);
lean_dec(v_a_6184_);
lean_dec_ref(v_a_6183_);
lean_dec(v_a_6182_);
lean_dec_ref(v_a_6181_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6187_, lean_object* v_msg_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
lean_object* v___x_6196_; 
v___x_6196_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6197_, lean_object* v_msg_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6197_, v_msg_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
lean_object* v___x_6216_; 
v___x_6216_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6214_);
return v___x_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_);
lean_dec(v___y_6224_);
lean_dec_ref(v___y_6223_);
lean_dec(v___y_6222_);
lean_dec_ref(v___y_6221_);
lean_dec(v___y_6220_);
lean_dec_ref(v___y_6219_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
return v_res_6226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6227_, lean_object* v_x_6228_, lean_object* v_mkInfoTree_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6228_, v_mkInfoTree_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6240_, lean_object* v_x_6241_, lean_object* v_mkInfoTree_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_){
_start:
{
lean_object* v_res_6252_; 
v_res_6252_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6240_, v_x_6241_, v_mkInfoTree_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
lean_dec(v___y_6250_);
lean_dec_ref(v___y_6249_);
lean_dec(v___y_6248_);
lean_dec_ref(v___y_6247_);
lean_dec(v___y_6246_);
lean_dec_ref(v___y_6245_);
lean_dec(v___y_6244_);
lean_dec_ref(v___y_6243_);
return v_res_6252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6253_, size_t v_i_6254_, size_t v_stop_6255_, lean_object* v_b_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_){
_start:
{
lean_object* v___x_6264_; 
v___x_6264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6253_, v_i_6254_, v_stop_6255_, v_b_6256_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
return v___x_6264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6265_, lean_object* v_i_6266_, lean_object* v_stop_6267_, lean_object* v_b_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
size_t v_i_boxed_6276_; size_t v_stop_boxed_6277_; lean_object* v_res_6278_; 
v_i_boxed_6276_ = lean_unbox_usize(v_i_6266_);
lean_dec(v_i_6266_);
v_stop_boxed_6277_ = lean_unbox_usize(v_stop_6267_);
lean_dec(v_stop_6267_);
v_res_6278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6265_, v_i_boxed_6276_, v_stop_boxed_6277_, v_b_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
lean_dec(v___y_6274_);
lean_dec_ref(v___y_6273_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec_ref(v_as_6265_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6279_, lean_object* v_x_6280_, uint8_t v_isExporting_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
lean_object* v___x_6287_; 
v___x_6287_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6280_, v_isExporting_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6288_, lean_object* v_x_6289_, lean_object* v_isExporting_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_){
_start:
{
uint8_t v_isExporting_boxed_6296_; lean_object* v_res_6297_; 
v_isExporting_boxed_6296_ = lean_unbox(v_isExporting_6290_);
v_res_6297_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6288_, v_x_6289_, v_isExporting_boxed_6296_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
lean_dec(v___y_6292_);
lean_dec_ref(v___y_6291_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6298_, lean_object* v_x_6299_, uint8_t v_when_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6299_, v_when_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6307_, lean_object* v_x_6308_, lean_object* v_when_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_){
_start:
{
uint8_t v_when_boxed_6315_; lean_object* v_res_6316_; 
v_when_boxed_6315_ = lean_unbox(v_when_6309_);
v_res_6316_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6307_, v_x_6308_, v_when_boxed_6315_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
return v_res_6316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6317_, lean_object* v_macroStack_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_){
_start:
{
lean_object* v___x_6326_; 
v___x_6326_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6317_, v_macroStack_6318_, v___y_6323_);
return v___x_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6327_, lean_object* v_macroStack_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_){
_start:
{
lean_object* v_res_6336_; 
v_res_6336_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6327_, v_macroStack_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
lean_dec(v___y_6334_);
lean_dec_ref(v___y_6333_);
lean_dec(v___y_6332_);
lean_dec_ref(v___y_6331_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
return v_res_6336_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6343_ = lean_box(0);
v___x_6344_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6345_ = l_Lean_mkConst(v___x_6344_, v___x_6343_);
return v___x_6345_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; 
v___x_6350_ = lean_box(0);
v___x_6351_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6352_ = l_Lean_mkConst(v___x_6351_, v___x_6350_);
return v___x_6352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6353_, lean_object* v_a_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_){
_start:
{
lean_object* v___x_6362_; 
v___x_6362_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6353_, v_a_6355_);
if (lean_obj_tag(v___x_6362_) == 0)
{
lean_object* v_a_6363_; lean_object* v___x_6364_; uint8_t v___x_6365_; 
v_a_6363_ = lean_ctor_get(v___x_6362_, 0);
lean_inc(v_a_6363_);
lean_dec_ref_known(v___x_6362_, 1);
v___x_6364_ = l_Lean_Expr_cleanupAnnotations(v_a_6363_);
v___x_6365_ = l_Lean_Expr_isApp(v___x_6364_);
if (v___x_6365_ == 0)
{
lean_dec_ref(v___x_6364_);
goto v___jp_6359_;
}
else
{
lean_object* v_arg_6366_; lean_object* v___x_6367_; uint8_t v___x_6368_; 
v_arg_6366_ = lean_ctor_get(v___x_6364_, 1);
lean_inc_ref(v_arg_6366_);
v___x_6367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6364_);
v___x_6368_ = l_Lean_Expr_isApp(v___x_6367_);
if (v___x_6368_ == 0)
{
lean_dec_ref(v___x_6367_);
lean_dec_ref(v_arg_6366_);
goto v___jp_6359_;
}
else
{
lean_object* v_arg_6369_; lean_object* v___x_6370_; uint8_t v___x_6371_; 
v_arg_6369_ = lean_ctor_get(v___x_6367_, 1);
lean_inc_ref(v_arg_6369_);
v___x_6370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6367_);
v___x_6371_ = l_Lean_Expr_isApp(v___x_6370_);
if (v___x_6371_ == 0)
{
lean_dec_ref(v___x_6370_);
lean_dec_ref(v_arg_6369_);
lean_dec_ref(v_arg_6366_);
goto v___jp_6359_;
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
lean_dec_ref(v_arg_6369_);
lean_dec_ref(v_arg_6366_);
goto v___jp_6359_;
}
else
{
lean_object* v___x_6375_; lean_object* v___x_6376_; uint8_t v___x_6377_; 
v___x_6375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6373_);
v___x_6376_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6377_ = l_Lean_Expr_isConstOf(v___x_6375_, v___x_6376_);
lean_dec_ref(v___x_6375_);
if (v___x_6377_ == 0)
{
lean_dec_ref(v_arg_6372_);
lean_dec_ref(v_arg_6369_);
lean_dec_ref(v_arg_6366_);
goto v___jp_6359_;
}
else
{
lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6378_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6379_ = l_Lean_Meta_isExprDefEq(v_arg_6372_, v___x_6378_, v_a_6354_, v_a_6355_, v_a_6356_, v_a_6357_);
if (lean_obj_tag(v___x_6379_) == 0)
{
lean_object* v_a_6380_; lean_object* v___x_6382_; uint8_t v_isShared_6383_; uint8_t v_isSharedCheck_6413_; 
v_a_6380_ = lean_ctor_get(v___x_6379_, 0);
v_isSharedCheck_6413_ = !lean_is_exclusive(v___x_6379_);
if (v_isSharedCheck_6413_ == 0)
{
v___x_6382_ = v___x_6379_;
v_isShared_6383_ = v_isSharedCheck_6413_;
goto v_resetjp_6381_;
}
else
{
lean_inc(v_a_6380_);
lean_dec(v___x_6379_);
v___x_6382_ = lean_box(0);
v_isShared_6383_ = v_isSharedCheck_6413_;
goto v_resetjp_6381_;
}
v_resetjp_6381_:
{
uint8_t v___x_6384_; 
v___x_6384_ = lean_unbox(v_a_6380_);
lean_dec(v_a_6380_);
if (v___x_6384_ == 0)
{
lean_object* v___x_6385_; lean_object* v___x_6387_; 
lean_dec_ref(v_arg_6369_);
lean_dec_ref(v_arg_6366_);
v___x_6385_ = lean_box(0);
if (v_isShared_6383_ == 0)
{
lean_ctor_set(v___x_6382_, 0, v___x_6385_);
v___x_6387_ = v___x_6382_;
goto v_reusejp_6386_;
}
else
{
lean_object* v_reuseFailAlloc_6388_; 
v_reuseFailAlloc_6388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6388_, 0, v___x_6385_);
v___x_6387_ = v_reuseFailAlloc_6388_;
goto v_reusejp_6386_;
}
v_reusejp_6386_:
{
return v___x_6387_;
}
}
else
{
lean_object* v___x_6389_; lean_object* v___x_6390_; 
lean_del_object(v___x_6382_);
v___x_6389_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6390_ = l_Lean_Meta_isExprDefEq(v_arg_6366_, v___x_6389_, v_a_6354_, v_a_6355_, v_a_6356_, v_a_6357_);
if (lean_obj_tag(v___x_6390_) == 0)
{
lean_object* v_a_6391_; lean_object* v___x_6393_; uint8_t v_isShared_6394_; uint8_t v_isSharedCheck_6404_; 
v_a_6391_ = lean_ctor_get(v___x_6390_, 0);
v_isSharedCheck_6404_ = !lean_is_exclusive(v___x_6390_);
if (v_isSharedCheck_6404_ == 0)
{
v___x_6393_ = v___x_6390_;
v_isShared_6394_ = v_isSharedCheck_6404_;
goto v_resetjp_6392_;
}
else
{
lean_inc(v_a_6391_);
lean_dec(v___x_6390_);
v___x_6393_ = lean_box(0);
v_isShared_6394_ = v_isSharedCheck_6404_;
goto v_resetjp_6392_;
}
v_resetjp_6392_:
{
uint8_t v___x_6395_; 
v___x_6395_ = lean_unbox(v_a_6391_);
lean_dec(v_a_6391_);
if (v___x_6395_ == 0)
{
lean_object* v___x_6396_; lean_object* v___x_6398_; 
lean_dec_ref(v_arg_6369_);
v___x_6396_ = lean_box(0);
if (v_isShared_6394_ == 0)
{
lean_ctor_set(v___x_6393_, 0, v___x_6396_);
v___x_6398_ = v___x_6393_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6399_; 
v_reuseFailAlloc_6399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6399_, 0, v___x_6396_);
v___x_6398_ = v_reuseFailAlloc_6399_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
return v___x_6398_;
}
}
else
{
lean_object* v___x_6400_; lean_object* v___x_6402_; 
v___x_6400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6400_, 0, v_arg_6369_);
if (v_isShared_6394_ == 0)
{
lean_ctor_set(v___x_6393_, 0, v___x_6400_);
v___x_6402_ = v___x_6393_;
goto v_reusejp_6401_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v___x_6400_);
v___x_6402_ = v_reuseFailAlloc_6403_;
goto v_reusejp_6401_;
}
v_reusejp_6401_:
{
return v___x_6402_;
}
}
}
}
else
{
lean_object* v_a_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6412_; 
lean_dec_ref(v_arg_6369_);
v_a_6405_ = lean_ctor_get(v___x_6390_, 0);
v_isSharedCheck_6412_ = !lean_is_exclusive(v___x_6390_);
if (v_isSharedCheck_6412_ == 0)
{
v___x_6407_ = v___x_6390_;
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_a_6405_);
lean_dec(v___x_6390_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6410_; 
if (v_isShared_6408_ == 0)
{
v___x_6410_ = v___x_6407_;
goto v_reusejp_6409_;
}
else
{
lean_object* v_reuseFailAlloc_6411_; 
v_reuseFailAlloc_6411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_a_6405_);
v___x_6410_ = v_reuseFailAlloc_6411_;
goto v_reusejp_6409_;
}
v_reusejp_6409_:
{
return v___x_6410_;
}
}
}
}
}
}
else
{
lean_object* v_a_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6421_; 
lean_dec_ref(v_arg_6369_);
lean_dec_ref(v_arg_6366_);
v_a_6414_ = lean_ctor_get(v___x_6379_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6379_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6416_ = v___x_6379_;
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_a_6414_);
lean_dec(v___x_6379_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v___x_6419_; 
if (v_isShared_6417_ == 0)
{
v___x_6419_ = v___x_6416_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
return v___x_6419_;
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
lean_object* v_a_6422_; lean_object* v___x_6424_; uint8_t v_isShared_6425_; uint8_t v_isSharedCheck_6429_; 
v_a_6422_ = lean_ctor_get(v___x_6362_, 0);
v_isSharedCheck_6429_ = !lean_is_exclusive(v___x_6362_);
if (v_isSharedCheck_6429_ == 0)
{
v___x_6424_ = v___x_6362_;
v_isShared_6425_ = v_isSharedCheck_6429_;
goto v_resetjp_6423_;
}
else
{
lean_inc(v_a_6422_);
lean_dec(v___x_6362_);
v___x_6424_ = lean_box(0);
v_isShared_6425_ = v_isSharedCheck_6429_;
goto v_resetjp_6423_;
}
v_resetjp_6423_:
{
lean_object* v___x_6427_; 
if (v_isShared_6425_ == 0)
{
v___x_6427_ = v___x_6424_;
goto v_reusejp_6426_;
}
else
{
lean_object* v_reuseFailAlloc_6428_; 
v_reuseFailAlloc_6428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_a_6422_);
v___x_6427_ = v_reuseFailAlloc_6428_;
goto v_reusejp_6426_;
}
v_reusejp_6426_:
{
return v___x_6427_;
}
}
}
v___jp_6359_:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = lean_box(0);
v___x_6361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6361_, 0, v___x_6360_);
return v___x_6361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_){
_start:
{
lean_object* v_res_6436_; 
v_res_6436_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6430_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec(v_a_6434_);
lean_dec_ref(v_a_6433_);
lean_dec(v_a_6432_);
lean_dec_ref(v_a_6431_);
return v_res_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6437_, lean_object* v_maxFVars_x3f_6438_, lean_object* v_k_6439_, uint8_t v_cleanupAnnotations_6440_, uint8_t v_whnfType_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_){
_start:
{
lean_object* v___f_6449_; lean_object* v___x_6450_; 
lean_inc(v___y_6443_);
lean_inc_ref(v___y_6442_);
v___f_6449_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6449_, 0, v_k_6439_);
lean_closure_set(v___f_6449_, 1, v___y_6442_);
lean_closure_set(v___f_6449_, 2, v___y_6443_);
v___x_6450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6437_, v_maxFVars_x3f_6438_, v___f_6449_, v_cleanupAnnotations_6440_, v_whnfType_6441_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
if (lean_obj_tag(v___x_6450_) == 0)
{
return v___x_6450_;
}
else
{
lean_object* v_a_6451_; lean_object* v___x_6453_; uint8_t v_isShared_6454_; uint8_t v_isSharedCheck_6458_; 
v_a_6451_ = lean_ctor_get(v___x_6450_, 0);
v_isSharedCheck_6458_ = !lean_is_exclusive(v___x_6450_);
if (v_isSharedCheck_6458_ == 0)
{
v___x_6453_ = v___x_6450_;
v_isShared_6454_ = v_isSharedCheck_6458_;
goto v_resetjp_6452_;
}
else
{
lean_inc(v_a_6451_);
lean_dec(v___x_6450_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6459_, lean_object* v_maxFVars_x3f_6460_, lean_object* v_k_6461_, lean_object* v_cleanupAnnotations_6462_, lean_object* v_whnfType_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6471_; uint8_t v_whnfType_boxed_6472_; lean_object* v_res_6473_; 
v_cleanupAnnotations_boxed_6471_ = lean_unbox(v_cleanupAnnotations_6462_);
v_whnfType_boxed_6472_ = lean_unbox(v_whnfType_6463_);
v_res_6473_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6459_, v_maxFVars_x3f_6460_, v_k_6461_, v_cleanupAnnotations_boxed_6471_, v_whnfType_boxed_6472_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
lean_dec(v___y_6469_);
lean_dec_ref(v___y_6468_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
lean_dec(v___y_6465_);
lean_dec_ref(v___y_6464_);
return v_res_6473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6474_, lean_object* v_type_6475_, lean_object* v_maxFVars_x3f_6476_, lean_object* v_k_6477_, uint8_t v_cleanupAnnotations_6478_, uint8_t v_whnfType_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_){
_start:
{
lean_object* v___x_6487_; 
v___x_6487_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6475_, v_maxFVars_x3f_6476_, v_k_6477_, v_cleanupAnnotations_6478_, v_whnfType_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_, v___y_6485_);
return v___x_6487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6488_, lean_object* v_type_6489_, lean_object* v_maxFVars_x3f_6490_, lean_object* v_k_6491_, lean_object* v_cleanupAnnotations_6492_, lean_object* v_whnfType_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6501_; uint8_t v_whnfType_boxed_6502_; lean_object* v_res_6503_; 
v_cleanupAnnotations_boxed_6501_ = lean_unbox(v_cleanupAnnotations_6492_);
v_whnfType_boxed_6502_ = lean_unbox(v_whnfType_6493_);
v_res_6503_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6488_, v_type_6489_, v_maxFVars_x3f_6490_, v_k_6491_, v_cleanupAnnotations_boxed_6501_, v_whnfType_boxed_6502_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
lean_dec(v___y_6499_);
lean_dec_ref(v___y_6498_);
lean_dec(v___y_6497_);
lean_dec_ref(v___y_6496_);
lean_dec(v___y_6495_);
lean_dec_ref(v___y_6494_);
return v_res_6503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6504_, lean_object* v_x_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_){
_start:
{
lean_object* v_keyedConfig_6513_; uint8_t v_trackZetaDelta_6514_; lean_object* v_zetaDeltaSet_6515_; lean_object* v_localInstances_6516_; lean_object* v_defEqCtx_x3f_6517_; lean_object* v_synthPendingDepth_6518_; lean_object* v_customCanUnfoldPredicate_x3f_6519_; uint8_t v_univApprox_6520_; uint8_t v_inTypeClassResolution_6521_; uint8_t v_cacheInferType_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v_keyedConfig_6513_ = lean_ctor_get(v___y_6508_, 0);
v_trackZetaDelta_6514_ = lean_ctor_get_uint8(v___y_6508_, sizeof(void*)*7);
v_zetaDeltaSet_6515_ = lean_ctor_get(v___y_6508_, 1);
v_localInstances_6516_ = lean_ctor_get(v___y_6508_, 3);
v_defEqCtx_x3f_6517_ = lean_ctor_get(v___y_6508_, 4);
v_synthPendingDepth_6518_ = lean_ctor_get(v___y_6508_, 5);
v_customCanUnfoldPredicate_x3f_6519_ = lean_ctor_get(v___y_6508_, 6);
v_univApprox_6520_ = lean_ctor_get_uint8(v___y_6508_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6521_ = lean_ctor_get_uint8(v___y_6508_, sizeof(void*)*7 + 2);
v_cacheInferType_6522_ = lean_ctor_get_uint8(v___y_6508_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6519_);
lean_inc(v_synthPendingDepth_6518_);
lean_inc(v_defEqCtx_x3f_6517_);
lean_inc_ref(v_localInstances_6516_);
lean_inc(v_zetaDeltaSet_6515_);
lean_inc_ref(v_keyedConfig_6513_);
v___x_6523_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6523_, 0, v_keyedConfig_6513_);
lean_ctor_set(v___x_6523_, 1, v_zetaDeltaSet_6515_);
lean_ctor_set(v___x_6523_, 2, v_lctx_6504_);
lean_ctor_set(v___x_6523_, 3, v_localInstances_6516_);
lean_ctor_set(v___x_6523_, 4, v_defEqCtx_x3f_6517_);
lean_ctor_set(v___x_6523_, 5, v_synthPendingDepth_6518_);
lean_ctor_set(v___x_6523_, 6, v_customCanUnfoldPredicate_x3f_6519_);
lean_ctor_set_uint8(v___x_6523_, sizeof(void*)*7, v_trackZetaDelta_6514_);
lean_ctor_set_uint8(v___x_6523_, sizeof(void*)*7 + 1, v_univApprox_6520_);
lean_ctor_set_uint8(v___x_6523_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6521_);
lean_ctor_set_uint8(v___x_6523_, sizeof(void*)*7 + 3, v_cacheInferType_6522_);
lean_inc(v___y_6511_);
lean_inc_ref(v___y_6510_);
lean_inc(v___y_6509_);
lean_inc(v___y_6507_);
lean_inc_ref(v___y_6506_);
v___x_6524_ = lean_apply_7(v_x_6505_, v___y_6506_, v___y_6507_, v___x_6523_, v___y_6509_, v___y_6510_, v___y_6511_, lean_box(0));
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_object* v_a_6525_; lean_object* v___x_6527_; uint8_t v_isShared_6528_; uint8_t v_isSharedCheck_6532_; 
v_a_6525_ = lean_ctor_get(v___x_6524_, 0);
v_isSharedCheck_6532_ = !lean_is_exclusive(v___x_6524_);
if (v_isSharedCheck_6532_ == 0)
{
v___x_6527_ = v___x_6524_;
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
else
{
lean_inc(v_a_6525_);
lean_dec(v___x_6524_);
v___x_6527_ = lean_box(0);
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
v_resetjp_6526_:
{
lean_object* v___x_6530_; 
if (v_isShared_6528_ == 0)
{
v___x_6530_ = v___x_6527_;
goto v_reusejp_6529_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_a_6525_);
v___x_6530_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6529_;
}
v_reusejp_6529_:
{
return v___x_6530_;
}
}
}
else
{
return v___x_6524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6533_, lean_object* v_x_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_){
_start:
{
lean_object* v_res_6542_; 
v_res_6542_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6533_, v_x_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
lean_dec(v___y_6540_);
lean_dec_ref(v___y_6539_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6535_);
return v_res_6542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6543_, lean_object* v_lctx_6544_, lean_object* v_x_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_){
_start:
{
lean_object* v___x_6553_; 
v___x_6553_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6544_, v_x_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_);
return v___x_6553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6554_, lean_object* v_lctx_6555_, lean_object* v_x_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_){
_start:
{
lean_object* v_res_6564_; 
v_res_6564_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6554_, v_lctx_6555_, v_x_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_);
lean_dec(v___y_6562_);
lean_dec_ref(v___y_6561_);
lean_dec(v___y_6560_);
lean_dec_ref(v___y_6559_);
lean_dec(v___y_6558_);
lean_dec_ref(v___y_6557_);
return v_res_6564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v_prefixArgs_6565_, lean_object* v_declName_6566_, lean_object* v_x_6567_, lean_object* v_F_6568_, lean_object* v_val_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_){
_start:
{
lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; 
v___x_6577_ = lean_array_get_size(v_prefixArgs_6565_);
v___x_6578_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6578_, 0, v_declName_6566_);
lean_closure_set(v___x_6578_, 1, v___x_6577_);
v___x_6579_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6567_, v_F_6568_, v_val_6569_, v___x_6578_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_);
return v___x_6579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v_prefixArgs_6580_, lean_object* v_declName_6581_, lean_object* v_x_6582_, lean_object* v_F_6583_, lean_object* v_val_6584_, lean_object* v___y_6585_, lean_object* v___y_6586_, lean_object* v___y_6587_, lean_object* v___y_6588_, lean_object* v___y_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_){
_start:
{
lean_object* v_res_6592_; 
v_res_6592_ = l_Lean_Elab_WF_mkFix___lam__0(v_prefixArgs_6580_, v_declName_6581_, v_x_6582_, v_F_6583_, v_val_6584_, v___y_6585_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_, v___y_6590_);
lean_dec(v___y_6590_);
lean_dec_ref(v___y_6589_);
lean_dec(v___y_6588_);
lean_dec_ref(v___y_6587_);
lean_dec(v___y_6586_);
lean_dec_ref(v___y_6585_);
lean_dec_ref(v_prefixArgs_6580_);
return v_res_6592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v___x_6609_, lean_object* v___x_6610_, lean_object* v_wfRel_6611_, lean_object* v_x_6612_, lean_object* v_type_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_){
_start:
{
lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; 
v___x_6621_ = lean_unsigned_to_nat(0u);
v___x_6622_ = lean_array_get_borrowed(v___x_6609_, v_x_6612_, v___x_6621_);
v___x_6623_ = l_Lean_Expr_fvarId_x21(v___x_6622_);
v___x_6624_ = l_Lean_FVarId_getUserName___redArg(v___x_6623_, v___y_6616_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6624_) == 0)
{
lean_object* v_a_6625_; lean_object* v___x_6626_; 
v_a_6625_ = lean_ctor_get(v___x_6624_, 0);
lean_inc(v_a_6625_);
lean_dec_ref_known(v___x_6624_, 1);
lean_inc(v___y_6619_);
lean_inc_ref(v___y_6618_);
lean_inc(v___y_6617_);
lean_inc_ref(v___y_6616_);
lean_inc(v___x_6622_);
v___x_6626_ = lean_infer_type(v___x_6622_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6626_) == 0)
{
lean_object* v_a_6627_; lean_object* v___x_6628_; 
v_a_6627_ = lean_ctor_get(v___x_6626_, 0);
lean_inc_n(v_a_6627_, 2);
lean_dec_ref_known(v___x_6626_, 1);
v___x_6628_ = l_Lean_Meta_getLevel(v_a_6627_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6628_) == 0)
{
lean_object* v_a_6629_; lean_object* v___x_6630_; 
v_a_6629_ = lean_ctor_get(v___x_6628_, 0);
lean_inc(v_a_6629_);
lean_dec_ref_known(v___x_6628_, 1);
lean_inc_ref(v_type_6613_);
v___x_6630_ = l_Lean_Meta_getLevel(v_type_6613_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6630_) == 0)
{
lean_object* v_a_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; uint8_t v___x_6634_; uint8_t v___x_6635_; uint8_t v___x_6636_; lean_object* v___x_6637_; 
v_a_6631_ = lean_ctor_get(v___x_6630_, 0);
lean_inc(v_a_6631_);
lean_dec_ref_known(v___x_6630_, 1);
v___x_6632_ = lean_mk_empty_array_with_capacity(v___x_6610_);
lean_inc(v___x_6622_);
lean_inc_ref(v___x_6632_);
v___x_6633_ = lean_array_push(v___x_6632_, v___x_6622_);
v___x_6634_ = 0;
v___x_6635_ = 1;
v___x_6636_ = 1;
v___x_6637_ = l_Lean_Meta_mkLambdaFVars(v___x_6633_, v_type_6613_, v___x_6634_, v___x_6635_, v___x_6634_, v___x_6635_, v___x_6636_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
lean_dec_ref(v___x_6633_);
if (lean_obj_tag(v___x_6637_) == 0)
{
lean_object* v_a_6638_; lean_object* v___x_6639_; 
v_a_6638_ = lean_ctor_get(v___x_6637_, 0);
lean_inc(v_a_6638_);
lean_dec_ref_known(v___x_6637_, 1);
lean_inc_ref(v_wfRel_6611_);
v___x_6639_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6611_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6639_) == 0)
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6684_; 
v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6684_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6684_ == 0)
{
v___x_6642_ = v___x_6639_;
v_isShared_6643_ = v_isSharedCheck_6684_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6639_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6684_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
if (lean_obj_tag(v_a_6640_) == 1)
{
lean_object* v_val_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6653_; 
lean_dec_ref(v___x_6632_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_val_6644_ = lean_ctor_get(v_a_6640_, 0);
lean_inc(v_val_6644_);
lean_dec_ref_known(v_a_6640_, 1);
v___x_6645_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__2));
v___x_6646_ = lean_box(0);
v___x_6647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6647_, 0, v_a_6631_);
lean_ctor_set(v___x_6647_, 1, v___x_6646_);
v___x_6648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6648_, 0, v_a_6629_);
lean_ctor_set(v___x_6648_, 1, v___x_6647_);
v___x_6649_ = l_Lean_mkConst(v___x_6645_, v___x_6648_);
v___x_6650_ = l_Lean_mkApp3(v___x_6649_, v_a_6627_, v_a_6638_, v_val_6644_);
v___x_6651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6651_, 0, v___x_6650_);
lean_ctor_set(v___x_6651_, 1, v_a_6625_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6651_);
v___x_6653_ = v___x_6642_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v___x_6651_);
v___x_6653_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
return v___x_6653_;
}
}
else
{
lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; 
lean_del_object(v___x_6642_);
lean_dec(v_a_6640_);
v___x_6655_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__4));
lean_inc_ref(v_wfRel_6611_);
v___x_6656_ = l_Lean_mkProj(v___x_6655_, v___x_6621_, v_wfRel_6611_);
v___x_6657_ = l_Lean_mkProj(v___x_6655_, v___x_6610_, v_wfRel_6611_);
v___x_6658_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__6));
v___x_6659_ = lean_array_push(v___x_6632_, v___x_6657_);
v___x_6660_ = l_Lean_Meta_mkAppM(v___x_6658_, v___x_6659_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
if (lean_obj_tag(v___x_6660_) == 0)
{
lean_object* v_a_6661_; lean_object* v___x_6663_; uint8_t v_isShared_6664_; uint8_t v_isSharedCheck_6675_; 
v_a_6661_ = lean_ctor_get(v___x_6660_, 0);
v_isSharedCheck_6675_ = !lean_is_exclusive(v___x_6660_);
if (v_isSharedCheck_6675_ == 0)
{
v___x_6663_ = v___x_6660_;
v_isShared_6664_ = v_isSharedCheck_6675_;
goto v_resetjp_6662_;
}
else
{
lean_inc(v_a_6661_);
lean_dec(v___x_6660_);
v___x_6663_ = lean_box(0);
v_isShared_6664_ = v_isSharedCheck_6675_;
goto v_resetjp_6662_;
}
v_resetjp_6662_:
{
lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6673_; 
v___x_6665_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__7));
v___x_6666_ = lean_box(0);
v___x_6667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6667_, 0, v_a_6631_);
lean_ctor_set(v___x_6667_, 1, v___x_6666_);
v___x_6668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6668_, 0, v_a_6629_);
lean_ctor_set(v___x_6668_, 1, v___x_6667_);
v___x_6669_ = l_Lean_mkConst(v___x_6665_, v___x_6668_);
v___x_6670_ = l_Lean_mkApp4(v___x_6669_, v_a_6627_, v_a_6638_, v___x_6656_, v_a_6661_);
v___x_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6671_, 0, v___x_6670_);
lean_ctor_set(v___x_6671_, 1, v_a_6625_);
if (v_isShared_6664_ == 0)
{
lean_ctor_set(v___x_6663_, 0, v___x_6671_);
v___x_6673_ = v___x_6663_;
goto v_reusejp_6672_;
}
else
{
lean_object* v_reuseFailAlloc_6674_; 
v_reuseFailAlloc_6674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6674_, 0, v___x_6671_);
v___x_6673_ = v_reuseFailAlloc_6674_;
goto v_reusejp_6672_;
}
v_reusejp_6672_:
{
return v___x_6673_;
}
}
}
else
{
lean_object* v_a_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6683_; 
lean_dec_ref(v___x_6656_);
lean_dec(v_a_6638_);
lean_dec(v_a_6631_);
lean_dec(v_a_6629_);
lean_dec(v_a_6627_);
lean_dec(v_a_6625_);
v_a_6676_ = lean_ctor_get(v___x_6660_, 0);
v_isSharedCheck_6683_ = !lean_is_exclusive(v___x_6660_);
if (v_isSharedCheck_6683_ == 0)
{
v___x_6678_ = v___x_6660_;
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_a_6676_);
lean_dec(v___x_6660_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v___x_6681_; 
if (v_isShared_6679_ == 0)
{
v___x_6681_ = v___x_6678_;
goto v_reusejp_6680_;
}
else
{
lean_object* v_reuseFailAlloc_6682_; 
v_reuseFailAlloc_6682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_a_6676_);
v___x_6681_ = v_reuseFailAlloc_6682_;
goto v_reusejp_6680_;
}
v_reusejp_6680_:
{
return v___x_6681_;
}
}
}
}
}
}
else
{
lean_object* v_a_6685_; lean_object* v___x_6687_; uint8_t v_isShared_6688_; uint8_t v_isSharedCheck_6692_; 
lean_dec(v_a_6638_);
lean_dec_ref(v___x_6632_);
lean_dec(v_a_6631_);
lean_dec(v_a_6629_);
lean_dec(v_a_6627_);
lean_dec(v_a_6625_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6685_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6692_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6692_ == 0)
{
v___x_6687_ = v___x_6639_;
v_isShared_6688_ = v_isSharedCheck_6692_;
goto v_resetjp_6686_;
}
else
{
lean_inc(v_a_6685_);
lean_dec(v___x_6639_);
v___x_6687_ = lean_box(0);
v_isShared_6688_ = v_isSharedCheck_6692_;
goto v_resetjp_6686_;
}
v_resetjp_6686_:
{
lean_object* v___x_6690_; 
if (v_isShared_6688_ == 0)
{
v___x_6690_ = v___x_6687_;
goto v_reusejp_6689_;
}
else
{
lean_object* v_reuseFailAlloc_6691_; 
v_reuseFailAlloc_6691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6691_, 0, v_a_6685_);
v___x_6690_ = v_reuseFailAlloc_6691_;
goto v_reusejp_6689_;
}
v_reusejp_6689_:
{
return v___x_6690_;
}
}
}
}
else
{
lean_object* v_a_6693_; lean_object* v___x_6695_; uint8_t v_isShared_6696_; uint8_t v_isSharedCheck_6700_; 
lean_dec_ref(v___x_6632_);
lean_dec(v_a_6631_);
lean_dec(v_a_6629_);
lean_dec(v_a_6627_);
lean_dec(v_a_6625_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6693_ = lean_ctor_get(v___x_6637_, 0);
v_isSharedCheck_6700_ = !lean_is_exclusive(v___x_6637_);
if (v_isSharedCheck_6700_ == 0)
{
v___x_6695_ = v___x_6637_;
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
else
{
lean_inc(v_a_6693_);
lean_dec(v___x_6637_);
v___x_6695_ = lean_box(0);
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
v_resetjp_6694_:
{
lean_object* v___x_6698_; 
if (v_isShared_6696_ == 0)
{
v___x_6698_ = v___x_6695_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6699_; 
v_reuseFailAlloc_6699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6699_, 0, v_a_6693_);
v___x_6698_ = v_reuseFailAlloc_6699_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
return v___x_6698_;
}
}
}
}
else
{
lean_object* v_a_6701_; lean_object* v___x_6703_; uint8_t v_isShared_6704_; uint8_t v_isSharedCheck_6708_; 
lean_dec(v_a_6629_);
lean_dec(v_a_6627_);
lean_dec(v_a_6625_);
lean_dec_ref(v_type_6613_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6701_ = lean_ctor_get(v___x_6630_, 0);
v_isSharedCheck_6708_ = !lean_is_exclusive(v___x_6630_);
if (v_isSharedCheck_6708_ == 0)
{
v___x_6703_ = v___x_6630_;
v_isShared_6704_ = v_isSharedCheck_6708_;
goto v_resetjp_6702_;
}
else
{
lean_inc(v_a_6701_);
lean_dec(v___x_6630_);
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
lean_dec(v_a_6627_);
lean_dec(v_a_6625_);
lean_dec_ref(v_type_6613_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6709_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6716_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6716_ == 0)
{
v___x_6711_ = v___x_6628_;
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
else
{
lean_inc(v_a_6709_);
lean_dec(v___x_6628_);
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
lean_dec(v_a_6625_);
lean_dec_ref(v_type_6613_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6717_ = lean_ctor_get(v___x_6626_, 0);
v_isSharedCheck_6724_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6724_ == 0)
{
v___x_6719_ = v___x_6626_;
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_a_6717_);
lean_dec(v___x_6626_);
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
lean_dec_ref(v_type_6613_);
lean_dec_ref(v_wfRel_6611_);
lean_dec(v___x_6610_);
v_a_6725_ = lean_ctor_get(v___x_6624_, 0);
v_isSharedCheck_6732_ = !lean_is_exclusive(v___x_6624_);
if (v_isSharedCheck_6732_ == 0)
{
v___x_6727_ = v___x_6624_;
v_isShared_6728_ = v_isSharedCheck_6732_;
goto v_resetjp_6726_;
}
else
{
lean_inc(v_a_6725_);
lean_dec(v___x_6624_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v___x_6733_, lean_object* v___x_6734_, lean_object* v_wfRel_6735_, lean_object* v_x_6736_, lean_object* v_type_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_){
_start:
{
lean_object* v_res_6745_; 
v_res_6745_ = l_Lean_Elab_WF_mkFix___lam__1(v___x_6733_, v___x_6734_, v_wfRel_6735_, v_x_6736_, v_type_6737_, v___y_6738_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_);
lean_dec(v___y_6743_);
lean_dec_ref(v___y_6742_);
lean_dec(v___y_6741_);
lean_dec_ref(v___y_6740_);
lean_dec(v___y_6739_);
lean_dec_ref(v___y_6738_);
lean_dec_ref(v_x_6736_);
lean_dec_ref(v___x_6733_);
return v_res_6745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6746_, lean_object* v___x_6747_, lean_object* v___x_6748_, lean_object* v___f_6749_, lean_object* v_funNames_6750_, lean_object* v_argsPacker_6751_, lean_object* v_decrTactics_6752_, uint8_t v___x_6753_, lean_object* v_fst_6754_, lean_object* v_prefixArgs_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_){
_start:
{
lean_object* v___x_6763_; 
lean_inc_ref(v___x_6747_);
lean_inc_ref(v___x_6746_);
v___x_6763_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6746_, v___x_6747_, v___x_6748_, v___f_6749_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_);
if (lean_obj_tag(v___x_6763_) == 0)
{
lean_object* v_a_6764_; lean_object* v___x_6765_; 
v_a_6764_ = lean_ctor_get(v___x_6763_, 0);
lean_inc(v_a_6764_);
lean_dec_ref_known(v___x_6763_, 1);
v___x_6765_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6750_, v_argsPacker_6751_, v_decrTactics_6752_, v_a_6764_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_);
if (lean_obj_tag(v___x_6765_) == 0)
{
lean_object* v_a_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; uint8_t v___x_6771_; uint8_t v___x_6772_; lean_object* v___x_6773_; 
v_a_6766_ = lean_ctor_get(v___x_6765_, 0);
lean_inc(v_a_6766_);
lean_dec_ref_known(v___x_6765_, 1);
v___x_6767_ = lean_unsigned_to_nat(2u);
v___x_6768_ = lean_mk_empty_array_with_capacity(v___x_6767_);
v___x_6769_ = lean_array_push(v___x_6768_, v___x_6746_);
v___x_6770_ = lean_array_push(v___x_6769_, v___x_6747_);
v___x_6771_ = 1;
v___x_6772_ = 1;
v___x_6773_ = l_Lean_Meta_mkLambdaFVars(v___x_6770_, v_a_6766_, v___x_6753_, v___x_6771_, v___x_6753_, v___x_6771_, v___x_6772_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_);
lean_dec_ref(v___x_6770_);
if (lean_obj_tag(v___x_6773_) == 0)
{
lean_object* v_a_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; 
v_a_6774_ = lean_ctor_get(v___x_6773_, 0);
lean_inc(v_a_6774_);
lean_dec_ref_known(v___x_6773_, 1);
v___x_6775_ = l_Lean_Expr_app___override(v_fst_6754_, v_a_6774_);
v___x_6776_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6755_, v___x_6775_, v___x_6753_, v___x_6771_, v___x_6753_, v___x_6771_, v___x_6772_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_);
return v___x_6776_;
}
else
{
lean_dec_ref(v_fst_6754_);
return v___x_6773_;
}
}
else
{
lean_dec_ref(v_fst_6754_);
lean_dec_ref(v___x_6747_);
lean_dec_ref(v___x_6746_);
return v___x_6765_;
}
}
else
{
lean_dec_ref(v_fst_6754_);
lean_dec_ref(v_decrTactics_6752_);
lean_dec_ref(v_argsPacker_6751_);
lean_dec_ref(v_funNames_6750_);
lean_dec_ref(v___x_6747_);
lean_dec_ref(v___x_6746_);
return v___x_6763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6777_ = _args[0];
lean_object* v___x_6778_ = _args[1];
lean_object* v___x_6779_ = _args[2];
lean_object* v___f_6780_ = _args[3];
lean_object* v_funNames_6781_ = _args[4];
lean_object* v_argsPacker_6782_ = _args[5];
lean_object* v_decrTactics_6783_ = _args[6];
lean_object* v___x_6784_ = _args[7];
lean_object* v_fst_6785_ = _args[8];
lean_object* v_prefixArgs_6786_ = _args[9];
lean_object* v___y_6787_ = _args[10];
lean_object* v___y_6788_ = _args[11];
lean_object* v___y_6789_ = _args[12];
lean_object* v___y_6790_ = _args[13];
lean_object* v___y_6791_ = _args[14];
lean_object* v___y_6792_ = _args[15];
lean_object* v___y_6793_ = _args[16];
_start:
{
uint8_t v___x_5939__boxed_6794_; lean_object* v_res_6795_; 
v___x_5939__boxed_6794_ = lean_unbox(v___x_6784_);
v_res_6795_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6777_, v___x_6778_, v___x_6779_, v___f_6780_, v_funNames_6781_, v_argsPacker_6782_, v_decrTactics_6783_, v___x_5939__boxed_6794_, v_fst_6785_, v_prefixArgs_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_);
lean_dec(v___y_6792_);
lean_dec_ref(v___y_6791_);
lean_dec(v___y_6790_);
lean_dec_ref(v___y_6789_);
lean_dec(v___y_6788_);
lean_dec_ref(v___y_6787_);
lean_dec_ref(v_prefixArgs_6786_);
return v_res_6795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6796_, lean_object* v_snd_6797_, lean_object* v___x_6798_, lean_object* v_prefixArgs_6799_, lean_object* v_value_6800_, lean_object* v___f_6801_, lean_object* v_funNames_6802_, lean_object* v_argsPacker_6803_, lean_object* v_decrTactics_6804_, uint8_t v___x_6805_, lean_object* v_fst_6806_, lean_object* v_xs_6807_, lean_object* v_x_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_){
_start:
{
lean_object* v_lctx_6816_; lean_object* v___x_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___x_6822_; lean_object* v___x_6823_; lean_object* v___x_6824_; lean_object* v___f_6825_; lean_object* v___x_6826_; 
v_lctx_6816_ = lean_ctor_get(v___y_6811_, 2);
v___x_6817_ = lean_unsigned_to_nat(0u);
v___x_6818_ = lean_array_get_borrowed(v___x_6796_, v_xs_6807_, v___x_6817_);
v___x_6819_ = l_Lean_Expr_fvarId_x21(v___x_6818_);
lean_inc_ref(v_lctx_6816_);
v___x_6820_ = l_Lean_LocalContext_setUserName(v_lctx_6816_, v___x_6819_, v_snd_6797_);
v___x_6821_ = lean_array_get_borrowed(v___x_6796_, v_xs_6807_, v___x_6798_);
lean_inc_n(v___x_6818_, 2);
lean_inc_ref(v_prefixArgs_6799_);
v___x_6822_ = lean_array_push(v_prefixArgs_6799_, v___x_6818_);
v___x_6823_ = l_Lean_Expr_beta(v_value_6800_, v___x_6822_);
v___x_6824_ = lean_box(v___x_6805_);
lean_inc(v___x_6821_);
v___f_6825_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6825_, 0, v___x_6818_);
lean_closure_set(v___f_6825_, 1, v___x_6821_);
lean_closure_set(v___f_6825_, 2, v___x_6823_);
lean_closure_set(v___f_6825_, 3, v___f_6801_);
lean_closure_set(v___f_6825_, 4, v_funNames_6802_);
lean_closure_set(v___f_6825_, 5, v_argsPacker_6803_);
lean_closure_set(v___f_6825_, 6, v_decrTactics_6804_);
lean_closure_set(v___f_6825_, 7, v___x_6824_);
lean_closure_set(v___f_6825_, 8, v_fst_6806_);
lean_closure_set(v___f_6825_, 9, v_prefixArgs_6799_);
v___x_6826_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6820_, v___f_6825_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_);
return v___x_6826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6827_ = _args[0];
lean_object* v_snd_6828_ = _args[1];
lean_object* v___x_6829_ = _args[2];
lean_object* v_prefixArgs_6830_ = _args[3];
lean_object* v_value_6831_ = _args[4];
lean_object* v___f_6832_ = _args[5];
lean_object* v_funNames_6833_ = _args[6];
lean_object* v_argsPacker_6834_ = _args[7];
lean_object* v_decrTactics_6835_ = _args[8];
lean_object* v___x_6836_ = _args[9];
lean_object* v_fst_6837_ = _args[10];
lean_object* v_xs_6838_ = _args[11];
lean_object* v_x_6839_ = _args[12];
lean_object* v___y_6840_ = _args[13];
lean_object* v___y_6841_ = _args[14];
lean_object* v___y_6842_ = _args[15];
lean_object* v___y_6843_ = _args[16];
lean_object* v___y_6844_ = _args[17];
lean_object* v___y_6845_ = _args[18];
lean_object* v___y_6846_ = _args[19];
_start:
{
uint8_t v___x_6009__boxed_6847_; lean_object* v_res_6848_; 
v___x_6009__boxed_6847_ = lean_unbox(v___x_6836_);
v_res_6848_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6827_, v_snd_6828_, v___x_6829_, v_prefixArgs_6830_, v_value_6831_, v___f_6832_, v_funNames_6833_, v_argsPacker_6834_, v_decrTactics_6835_, v___x_6009__boxed_6847_, v_fst_6837_, v_xs_6838_, v_x_6839_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_);
lean_dec(v___y_6845_);
lean_dec_ref(v___y_6844_);
lean_dec(v___y_6843_);
lean_dec_ref(v___y_6842_);
lean_dec(v___y_6841_);
lean_dec_ref(v___y_6840_);
lean_dec_ref(v_x_6839_);
lean_dec_ref(v_xs_6838_);
lean_dec(v___x_6829_);
lean_dec_ref(v___x_6827_);
return v_res_6848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6853_, lean_object* v_prefixArgs_6854_, lean_object* v_argsPacker_6855_, lean_object* v_wfRel_6856_, lean_object* v_funNames_6857_, lean_object* v_decrTactics_6858_, lean_object* v_a_6859_, lean_object* v_a_6860_, lean_object* v_a_6861_, lean_object* v_a_6862_, lean_object* v_a_6863_, lean_object* v_a_6864_){
_start:
{
lean_object* v_declName_6866_; lean_object* v_type_6867_; lean_object* v_value_6868_; lean_object* v___f_6869_; lean_object* v___x_6870_; lean_object* v___x_6871_; 
v_declName_6866_ = lean_ctor_get(v_preDef_6853_, 3);
lean_inc(v_declName_6866_);
v_type_6867_ = lean_ctor_get(v_preDef_6853_, 6);
lean_inc_ref(v_type_6867_);
v_value_6868_ = lean_ctor_get(v_preDef_6853_, 7);
lean_inc_ref(v_value_6868_);
lean_dec_ref(v_preDef_6853_);
lean_inc_ref(v_prefixArgs_6854_);
v___f_6869_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 2);
lean_closure_set(v___f_6869_, 0, v_prefixArgs_6854_);
lean_closure_set(v___f_6869_, 1, v_declName_6866_);
v___x_6870_ = l_Lean_instInhabitedExpr;
v___x_6871_ = l_Lean_Meta_instantiateForall(v_type_6867_, v_prefixArgs_6854_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
if (lean_obj_tag(v___x_6871_) == 0)
{
lean_object* v_a_6872_; lean_object* v___x_6873_; lean_object* v___f_6874_; lean_object* v___x_6875_; uint8_t v___x_6876_; lean_object* v___x_6877_; 
v_a_6872_ = lean_ctor_get(v___x_6871_, 0);
lean_inc(v_a_6872_);
lean_dec_ref_known(v___x_6871_, 1);
v___x_6873_ = lean_unsigned_to_nat(1u);
v___f_6874_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6874_, 0, v___x_6870_);
lean_closure_set(v___f_6874_, 1, v___x_6873_);
lean_closure_set(v___f_6874_, 2, v_wfRel_6856_);
v___x_6875_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6876_ = 0;
v___x_6877_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6872_, v___x_6875_, v___f_6874_, v___x_6876_, v___x_6876_, v_a_6859_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
if (lean_obj_tag(v___x_6877_) == 0)
{
lean_object* v_a_6878_; lean_object* v_fst_6879_; lean_object* v_snd_6880_; lean_object* v___x_6881_; lean_object* v___f_6882_; lean_object* v___x_6883_; 
v_a_6878_ = lean_ctor_get(v___x_6877_, 0);
lean_inc(v_a_6878_);
lean_dec_ref_known(v___x_6877_, 1);
v_fst_6879_ = lean_ctor_get(v_a_6878_, 0);
lean_inc_n(v_fst_6879_, 2);
v_snd_6880_ = lean_ctor_get(v_a_6878_, 1);
lean_inc(v_snd_6880_);
lean_dec(v_a_6878_);
v___x_6881_ = lean_box(v___x_6876_);
v___f_6882_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6882_, 0, v___x_6870_);
lean_closure_set(v___f_6882_, 1, v_snd_6880_);
lean_closure_set(v___f_6882_, 2, v___x_6873_);
lean_closure_set(v___f_6882_, 3, v_prefixArgs_6854_);
lean_closure_set(v___f_6882_, 4, v_value_6868_);
lean_closure_set(v___f_6882_, 5, v___f_6869_);
lean_closure_set(v___f_6882_, 6, v_funNames_6857_);
lean_closure_set(v___f_6882_, 7, v_argsPacker_6855_);
lean_closure_set(v___f_6882_, 8, v_decrTactics_6858_);
lean_closure_set(v___f_6882_, 9, v___x_6881_);
lean_closure_set(v___f_6882_, 10, v_fst_6879_);
lean_inc(v_a_6864_);
lean_inc_ref(v_a_6863_);
lean_inc(v_a_6862_);
lean_inc_ref(v_a_6861_);
v___x_6883_ = lean_infer_type(v_fst_6879_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
if (lean_obj_tag(v___x_6883_) == 0)
{
lean_object* v_a_6884_; lean_object* v___x_6885_; 
v_a_6884_ = lean_ctor_get(v___x_6883_, 0);
lean_inc(v_a_6884_);
lean_dec_ref_known(v___x_6883_, 1);
lean_inc(v_a_6864_);
lean_inc_ref(v_a_6863_);
lean_inc(v_a_6862_);
lean_inc_ref(v_a_6861_);
v___x_6885_ = lean_whnf(v_a_6884_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
if (lean_obj_tag(v___x_6885_) == 0)
{
lean_object* v_a_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; 
v_a_6886_ = lean_ctor_get(v___x_6885_, 0);
lean_inc(v_a_6886_);
lean_dec_ref_known(v___x_6885_, 1);
v___x_6887_ = l_Lean_Expr_bindingDomain_x21(v_a_6886_);
lean_dec(v_a_6886_);
v___x_6888_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6889_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6887_, v___x_6888_, v___f_6882_, v___x_6876_, v___x_6876_, v_a_6859_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
return v___x_6889_;
}
else
{
lean_dec_ref(v___f_6882_);
return v___x_6885_;
}
}
else
{
lean_dec_ref(v___f_6882_);
return v___x_6883_;
}
}
else
{
lean_object* v_a_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6897_; 
lean_dec_ref(v___f_6869_);
lean_dec_ref(v_value_6868_);
lean_dec_ref(v_decrTactics_6858_);
lean_dec_ref(v_funNames_6857_);
lean_dec_ref(v_argsPacker_6855_);
lean_dec_ref(v_prefixArgs_6854_);
v_a_6890_ = lean_ctor_get(v___x_6877_, 0);
v_isSharedCheck_6897_ = !lean_is_exclusive(v___x_6877_);
if (v_isSharedCheck_6897_ == 0)
{
v___x_6892_ = v___x_6877_;
v_isShared_6893_ = v_isSharedCheck_6897_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_a_6890_);
lean_dec(v___x_6877_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6897_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___x_6895_; 
if (v_isShared_6893_ == 0)
{
v___x_6895_ = v___x_6892_;
goto v_reusejp_6894_;
}
else
{
lean_object* v_reuseFailAlloc_6896_; 
v_reuseFailAlloc_6896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6890_);
v___x_6895_ = v_reuseFailAlloc_6896_;
goto v_reusejp_6894_;
}
v_reusejp_6894_:
{
return v___x_6895_;
}
}
}
}
else
{
lean_dec_ref(v___f_6869_);
lean_dec_ref(v_value_6868_);
lean_dec_ref(v_decrTactics_6858_);
lean_dec_ref(v_funNames_6857_);
lean_dec_ref(v_wfRel_6856_);
lean_dec_ref(v_argsPacker_6855_);
lean_dec_ref(v_prefixArgs_6854_);
return v___x_6871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6898_, lean_object* v_prefixArgs_6899_, lean_object* v_argsPacker_6900_, lean_object* v_wfRel_6901_, lean_object* v_funNames_6902_, lean_object* v_decrTactics_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_){
_start:
{
lean_object* v_res_6911_; 
v_res_6911_ = l_Lean_Elab_WF_mkFix(v_preDef_6898_, v_prefixArgs_6899_, v_argsPacker_6900_, v_wfRel_6901_, v_funNames_6902_, v_decrTactics_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_, v_a_6909_);
lean_dec(v_a_6909_);
lean_dec_ref(v_a_6908_);
lean_dec(v_a_6907_);
lean_dec_ref(v_a_6906_);
lean_dec(v_a_6905_);
lean_dec_ref(v_a_6904_);
return v_res_6911_;
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
