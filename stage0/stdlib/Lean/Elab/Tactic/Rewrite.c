// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: public import Lean.Meta.Tactic.Rewrite public import Lean.Meta.Tactic.Replace public import Lean.Elab.Tactic.Location import Lean.Elab.ConfigEval import Lean.Meta.Eqns
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 311, .m_capacity = 311, .m_length = 310, .m_data = "The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.\nFull error:"};
static const lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabRewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Occurs check failed: Expression"};
static const lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewrite___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewrite___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabRewrite___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\ncontains the goal "};
static const lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewrite___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewrite___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewrite___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to rewrite using equation theorems for `"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Try rewriting with `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Rewrite"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ApplyNewGoals"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 184, 156, 67, 64, 216, 140, 26)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Occurrences"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 174, 204, 146, 85, 200, 104, 141)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "TransparencyMode"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 50, 227, 172, 92, 117, 235, 109)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "newGoals"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "occs"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "offsetCnstrs"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transparency"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 107, 61, 219, 24, 145, 46, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 84, 11, 37, 124, 73, 156, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 125, 72, 83, 103, 118, 157, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 238, 52, 164, 167, 101, 229, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 67, 55, 19, 78, 216, 184, 166)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Did not find an occurrence of the pattern in the current goal"};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalRewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(131, 252, 0, 80, 225, 242, 251, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object*);
lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT void l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed(lean_object* v_x_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(v_x_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_23_;
}
}
static lean_object* _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0));
v___x_26_ = l_Lean_stringToMessageData(v___x_25_);
return v___x_26_;
}
}
lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(lean_object* v_e_27_, uint8_t v___x_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_check(v_e_27_, v___x_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_34_, 0);
lean_dec(v_unused_43_);
v___x_36_ = v___x_34_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_dec(v___x_34_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = l_Lean_MessageData_nil;
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_63_; 
v_a_44_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_63_ == 0)
{
v___x_46_ = v___x_34_;
v_isShared_47_ = v_isSharedCheck_63_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_34_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_63_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint8_t v___y_49_; uint8_t v___x_61_; 
v___x_61_ = l_Lean_Exception_isInterrupt(v_a_44_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; 
lean_inc(v_a_44_);
v___x_62_ = l_Lean_Exception_isRuntime(v_a_44_);
v___y_49_ = v___x_62_;
goto v___jp_48_;
}
else
{
v___y_49_ = v___x_61_;
goto v___jp_48_;
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1, &l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1);
v___x_51_ = l_Lean_Exception_toMessageData(v_a_44_);
v___x_52_ = l_Lean_indentD(v___x_51_);
v___x_53_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = l_Lean_MessageData_note(v___x_53_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 0);
lean_ctor_set(v___x_46_, 0, v___x_54_);
v___x_56_ = v___x_46_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
else
{
lean_object* v___x_59_; 
if (v_isShared_47_ == 0)
{
v___x_59_ = v___x_46_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_44_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_27_ = stack[0].m_obj;
uint8_t v___x_28_ = stack[1].m_num;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v___y_32_ = stack[5].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_27_, v___x_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed(lean_object* v_e_65_, lean_object* v___x_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
uint8_t v___x_12402__boxed_72_; lean_object* v_res_73_; 
v___x_12402__boxed_72_ = lean_unbox(v___x_66_);
v_res_73_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_65_, v___x_12402__boxed_72_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2(lean_object* v_typeCheckNote_74_, lean_object* v_x_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_76_, 0, v_x_75_);
lean_ctor_set(v___x_76_, 1, v_typeCheckNote_74_);
return v___x_76_;
}
}
lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(lean_object* v_e_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___f_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_typeCheckNote_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
v___f_88_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_88_, 0, v_x_78_);
lean_closure_set(v___f_88_, 1, v___y_79_);
lean_closure_set(v___f_88_, 2, v___y_80_);
lean_closure_set(v___f_88_, 3, v___y_81_);
lean_closure_set(v___f_88_, 4, v___y_82_);
v___x_89_ = 5;
v___x_90_ = lean_box(v___x_89_);
lean_inc_ref(v_e_77_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed), 7, 2);
lean_closure_set(v___f_91_, 0, v_e_77_);
lean_closure_set(v___f_91_, 1, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_array_push(v___x_93_, v_e_77_);
v_typeCheckNote_95_ = l_Lean_MessageData_ofLazyM(v___f_91_, v___x_94_);
v___f_96_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2), 2, 1);
lean_closure_set(v___f_96_, 0, v_typeCheckNote_95_);
v___x_97_ = l_Lean_Meta_mapErrorImp___redArg(v___f_88_, v___f_96_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
if (lean_obj_tag(v___x_97_) == 0)
{
return v___x_97_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_77_ = stack[0].m_obj;
lean_object* v_x_78_ = stack[1].m_obj;
lean_object* v___y_79_ = stack[2].m_obj;
lean_object* v___y_80_ = stack[3].m_obj;
lean_object* v___y_81_ = stack[4].m_obj;
lean_object* v___y_82_ = stack[5].m_obj;
lean_object* v___y_83_ = stack[6].m_obj;
lean_object* v___y_84_ = stack[7].m_obj;
lean_object* v___y_85_ = stack[8].m_obj;
lean_object* v___y_86_ = stack[9].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___boxed(lean_object* v_e_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_107_, v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_118_;
}
}
lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object* v_00_u03b1_119_, lean_object* v_e_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_120_, v_x_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT void l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_120_ = stack[1].m_obj;
lean_object* v_x_121_ = stack[2].m_obj;
lean_object* v___y_122_ = stack[3].m_obj;
lean_object* v___y_123_ = stack[4].m_obj;
lean_object* v___y_124_ = stack[5].m_obj;
lean_object* v___y_125_ = stack[6].m_obj;
lean_object* v___y_126_ = stack[7].m_obj;
lean_object* v___y_127_ = stack[8].m_obj;
lean_object* v___y_128_ = stack[9].m_obj;
lean_object* v___y_129_ = stack[10].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_box(0), v_e_120_, v_x_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object* v_00_u03b1_133_, lean_object* v_e_134_, lean_object* v_x_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v_00_u03b1_133_, v_e_134_, v_x_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_box(0);
v___x_147_ = l_Lean_Elab_abortTacticExceptionId;
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
return v___x_148_;
}
}
lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_152_;
v_res_152_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___boxed(lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v_res_154_;
}
}
lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(lean_object* v_00_u03b1_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v___x_165_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_156_ = stack[1].m_obj;
lean_object* v___y_157_ = stack[2].m_obj;
lean_object* v___y_158_ = stack[3].m_obj;
lean_object* v___y_159_ = stack[4].m_obj;
lean_object* v___y_160_ = stack[5].m_obj;
lean_object* v___y_161_ = stack[6].m_obj;
lean_object* v___y_162_ = stack[7].m_obj;
lean_object* v___y_163_ = stack[8].m_obj;
lean_object* v_res_166_;
v_res_166_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(lean_box(0), v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___boxed(lean_object* v_00_u03b1_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(v_00_u03b1_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_177_;
}
}
lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0(lean_object* v_mvarId_178_, lean_object* v_e_179_, lean_object* v_a_180_, uint8_t v_symm_181_, lean_object* v_config_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_MVarId_rewrite(v_mvarId_178_, v_e_179_, v_a_180_, v_symm_181_, v_config_182_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
return v___x_192_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabRewrite___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_178_ = stack[0].m_obj;
lean_object* v_e_179_ = stack[1].m_obj;
lean_object* v_a_180_ = stack[2].m_obj;
uint8_t v_symm_181_ = stack[3].m_num;
lean_object* v_config_182_ = stack[4].m_obj;
lean_object* v___y_183_ = stack[5].m_obj;
lean_object* v___y_184_ = stack[6].m_obj;
lean_object* v___y_185_ = stack[7].m_obj;
lean_object* v___y_186_ = stack[8].m_obj;
lean_object* v___y_187_ = stack[9].m_obj;
lean_object* v___y_188_ = stack[10].m_obj;
lean_object* v___y_189_ = stack[11].m_obj;
lean_object* v___y_190_ = stack[12].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Lean_Elab_Tactic_elabRewrite___lam__0(v_mvarId_178_, v_e_179_, v_a_180_, v_symm_181_, v_config_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed(lean_object* v_mvarId_194_, lean_object* v_e_195_, lean_object* v_a_196_, lean_object* v_symm_197_, lean_object* v_config_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v_symm_boxed_208_; lean_object* v_res_209_; 
v_symm_boxed_208_ = lean_unbox(v_symm_197_);
v_res_209_ = l_Lean_Elab_Tactic_elabRewrite___lam__0(v_mvarId_194_, v_e_195_, v_a_196_, v_symm_boxed_208_, v_config_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_209_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(lean_object* v_a_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
else
{
lean_object* v_key_213_; lean_object* v_tail_214_; uint8_t v___x_215_; 
v_key_213_ = lean_ctor_get(v_x_211_, 0);
v_tail_214_ = lean_ctor_get(v_x_211_, 2);
v___x_215_ = lean_expr_eqv(v_key_213_, v_a_210_);
if (v___x_215_ == 0)
{
v_x_211_ = v_tail_214_;
goto _start;
}
else
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_210_ = stack[0].m_obj;
lean_object* v_x_211_ = stack[1].m_obj;
uint8_t v_res_217_;
v_res_217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_210_, v_x_211_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_218_, lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_218_, v_x_219_);
lean_dec(v_x_219_);
lean_dec_ref(v_a_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_buckets_224_; lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v_fold_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_buckets_224_ = lean_ctor_get(v_m_222_, 1);
v___x_225_ = lean_array_get_size(v_buckets_224_);
v___x_226_ = l_Lean_Expr_hash(v_a_223_);
v___x_227_ = 32ULL;
v___x_228_ = lean_uint64_shift_right(v___x_226_, v___x_227_);
v_fold_229_ = lean_uint64_xor(v___x_226_, v___x_228_);
v___x_230_ = 16ULL;
v___x_231_ = lean_uint64_shift_right(v_fold_229_, v___x_230_);
v___x_232_ = lean_uint64_xor(v_fold_229_, v___x_231_);
v___x_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = lean_usize_of_nat(v___x_225_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_sub(v___x_234_, v___x_235_);
v___x_237_ = lean_usize_land(v___x_233_, v___x_236_);
v___x_238_ = lean_array_uget_borrowed(v_buckets_224_, v___x_237_);
v___x_239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_223_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_222_ = stack[0].m_obj;
lean_object* v_a_223_ = stack[1].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_222_, v_a_223_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_241_, v_a_242_);
lean_dec_ref(v_a_242_);
lean_dec_ref(v_m_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(lean_object* v_mvarId_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_mctx_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_mctx_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_mctx_250_);
lean_dec(v___x_249_);
v___x_251_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_250_, v_mvarId_245_);
lean_dec_ref(v_mctx_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___y_246_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_245_ = stack[0].m_obj;
lean_object* v___y_246_ = stack[1].m_obj;
lean_object* v___y_247_ = stack[2].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_245_, v___y_246_, v___y_247_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_mvarId_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec(v_mvarId_256_);
return v_res_260_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(lean_object* v_mvarId_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = lean_st_ref_get(v___y_263_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_ref(v_mctx_266_);
lean_dec(v___x_265_);
v___x_267_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_266_, v_mvarId_261_);
lean_dec_ref(v_mctx_266_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___y_262_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_261_ = stack[0].m_obj;
lean_object* v___y_262_ = stack[1].m_obj;
lean_object* v___y_263_ = stack[2].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_261_, v___y_262_, v___y_263_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg___boxed(lean_object* v_mvarId_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec(v_mvarId_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
return v_x_277_;
}
else
{
lean_object* v_key_279_; lean_object* v_value_280_; lean_object* v_tail_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_304_; 
v_key_279_ = lean_ctor_get(v_x_278_, 0);
v_value_280_ = lean_ctor_get(v_x_278_, 1);
v_tail_281_ = lean_ctor_get(v_x_278_, 2);
v_isSharedCheck_304_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_304_ == 0)
{
v___x_283_ = v_x_278_;
v_isShared_284_ = v_isSharedCheck_304_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_tail_281_);
lean_inc(v_value_280_);
lean_inc(v_key_279_);
lean_dec(v_x_278_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_304_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v_fold_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_285_ = lean_array_get_size(v_x_277_);
v___x_286_ = l_Lean_Expr_hash(v_key_279_);
v___x_287_ = 32ULL;
v___x_288_ = lean_uint64_shift_right(v___x_286_, v___x_287_);
v_fold_289_ = lean_uint64_xor(v___x_286_, v___x_288_);
v___x_290_ = 16ULL;
v___x_291_ = lean_uint64_shift_right(v_fold_289_, v___x_290_);
v___x_292_ = lean_uint64_xor(v_fold_289_, v___x_291_);
v___x_293_ = lean_uint64_to_usize(v___x_292_);
v___x_294_ = lean_usize_of_nat(v___x_285_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_sub(v___x_294_, v___x_295_);
v___x_297_ = lean_usize_land(v___x_293_, v___x_296_);
v___x_298_ = lean_array_uget_borrowed(v_x_277_, v___x_297_);
lean_inc(v___x_298_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 2, v___x_298_);
v___x_300_ = v___x_283_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_key_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_value_280_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v___x_298_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_array_uset(v_x_277_, v___x_297_, v___x_300_);
v_x_277_ = v___x_301_;
v_x_278_ = v_tail_281_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(lean_object* v_i_305_, lean_object* v_source_306_, lean_object* v_target_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_array_get_size(v_source_306_);
v___x_309_ = lean_nat_dec_lt(v_i_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v_source_306_);
lean_dec(v_i_305_);
return v_target_307_;
}
else
{
lean_object* v_es_310_; lean_object* v___x_311_; lean_object* v_source_312_; lean_object* v_target_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_es_310_ = lean_array_fget(v_source_306_, v_i_305_);
v___x_311_ = lean_box(0);
v_source_312_ = lean_array_fset(v_source_306_, v_i_305_, v___x_311_);
v_target_313_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_target_307_, v_es_310_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_i_305_, v___x_314_);
lean_dec(v_i_305_);
v_i_305_ = v___x_315_;
v_source_306_ = v_source_312_;
v_target_307_ = v_target_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object* v_data_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_nbuckets_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_318_ = lean_array_get_size(v_data_317_);
v___x_319_ = lean_unsigned_to_nat(2u);
v_nbuckets_320_ = lean_nat_mul(v___x_318_, v___x_319_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_box(0);
v___x_323_ = lean_mk_array(v_nbuckets_320_, v___x_322_);
v___x_324_ = lean_array_propagate_mark(v_data_317_, v___x_323_);
v___x_325_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v___x_321_, v_data_317_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_m_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_size_329_; lean_object* v_buckets_330_; lean_object* v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v_fold_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v_bkt_344_; uint8_t v___x_345_; 
v_size_329_ = lean_ctor_get(v_m_326_, 0);
v_buckets_330_ = lean_ctor_get(v_m_326_, 1);
v___x_331_ = lean_array_get_size(v_buckets_330_);
v___x_332_ = l_Lean_Expr_hash(v_a_327_);
v___x_333_ = 32ULL;
v___x_334_ = lean_uint64_shift_right(v___x_332_, v___x_333_);
v_fold_335_ = lean_uint64_xor(v___x_332_, v___x_334_);
v___x_336_ = 16ULL;
v___x_337_ = lean_uint64_shift_right(v_fold_335_, v___x_336_);
v___x_338_ = lean_uint64_xor(v_fold_335_, v___x_337_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = lean_usize_of_nat(v___x_331_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_sub(v___x_340_, v___x_341_);
v___x_343_ = lean_usize_land(v___x_339_, v___x_342_);
v_bkt_344_ = lean_array_uget_borrowed(v_buckets_330_, v___x_343_);
v___x_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_327_, v_bkt_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_buckets_330_);
lean_inc(v_size_329_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_m_326_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; 
v_unused_367_ = lean_ctor_get(v_m_326_, 1);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_m_326_, 0);
lean_dec(v_unused_368_);
v___x_347_ = v_m_326_;
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_m_326_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v_size_x27_350_; lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v_size_x27_350_ = lean_nat_add(v_size_329_, v___x_349_);
lean_dec(v_size_329_);
lean_inc(v_bkt_344_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_327_);
lean_ctor_set(v___x_351_, 1, v_b_328_);
lean_ctor_set(v___x_351_, 2, v_bkt_344_);
v_buckets_x27_352_ = lean_array_uset(v_buckets_330_, v___x_343_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_358_ == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; 
v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_buckets_x27_352_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_val_359_);
lean_ctor_set(v___x_347_, 0, v_size_x27_350_);
v___x_361_ = v___x_347_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_buckets_x27_352_);
lean_ctor_set(v___x_347_, 0, v_size_x27_350_);
v___x_364_ = v___x_347_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_buckets_x27_352_);
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
else
{
lean_dec(v_b_328_);
lean_dec_ref(v_a_327_);
return v_m_326_;
}
}
}
lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(lean_object* v_mvarId_373_, lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_d_386_; lean_object* v_b_387_; lean_object* v___y_388_; uint8_t v___x_394_; 
v___x_394_ = l_Lean_Expr_hasExprMVar(v_e_374_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_e_374_);
v___x_395_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_375_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_375_, v_e_374_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_box(0);
lean_inc_ref(v_e_374_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_375_, v_e_374_, v___x_399_);
switch(lean_obj_tag(v_e_374_))
{
case 11:
{
lean_object* v_struct_401_; 
v_struct_401_ = lean_ctor_get(v_e_374_, 2);
lean_inc_ref(v_struct_401_);
lean_dec_ref_known(v_e_374_, 3);
v_e_374_ = v_struct_401_;
v_a_375_ = v___x_400_;
goto _start;
}
case 7:
{
lean_object* v_binderType_403_; lean_object* v_body_404_; 
v_binderType_403_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_binderType_403_);
v_body_404_ = lean_ctor_get(v_e_374_, 2);
lean_inc_ref(v_body_404_);
lean_dec_ref_known(v_e_374_, 3);
v_d_386_ = v_binderType_403_;
v_b_387_ = v_body_404_;
v___y_388_ = v___x_400_;
goto v___jp_385_;
}
case 6:
{
lean_object* v_binderType_405_; lean_object* v_body_406_; 
v_binderType_405_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_binderType_405_);
v_body_406_ = lean_ctor_get(v_e_374_, 2);
lean_inc_ref(v_body_406_);
lean_dec_ref_known(v_e_374_, 3);
v_d_386_ = v_binderType_405_;
v_b_387_ = v_body_406_;
v___y_388_ = v___x_400_;
goto v___jp_385_;
}
case 8:
{
lean_object* v_type_407_; lean_object* v_value_408_; lean_object* v_body_409_; lean_object* v___x_410_; 
v_type_407_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_type_407_);
v_value_408_ = lean_ctor_get(v_e_374_, 2);
lean_inc_ref(v_value_408_);
v_body_409_ = lean_ctor_get(v_e_374_, 3);
lean_inc_ref(v_body_409_);
lean_dec_ref_known(v_e_374_, 4);
v___x_410_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_373_, v_type_407_, v___x_400_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_fst_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_fst_412_ = lean_ctor_get(v_a_411_, 0);
if (lean_obj_tag(v_fst_412_) == 0)
{
lean_dec_ref(v_body_409_);
lean_dec_ref(v_value_408_);
return v___x_410_;
}
else
{
lean_object* v_snd_413_; lean_object* v___x_414_; 
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v_snd_413_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_snd_413_);
lean_dec(v_a_411_);
v___x_414_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_373_, v_value_408_, v_snd_413_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v_fst_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_fst_416_ = lean_ctor_get(v_a_415_, 0);
if (lean_obj_tag(v_fst_416_) == 0)
{
lean_dec_ref(v_body_409_);
return v___x_414_;
}
else
{
lean_object* v_snd_417_; 
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v_snd_417_ = lean_ctor_get(v_a_415_, 1);
lean_inc(v_snd_417_);
lean_dec(v_a_415_);
v_e_374_ = v_body_409_;
v_a_375_ = v_snd_417_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_409_);
return v___x_414_;
}
}
}
else
{
lean_dec_ref(v_body_409_);
lean_dec_ref(v_value_408_);
return v___x_410_;
}
}
case 10:
{
lean_object* v_expr_419_; 
v_expr_419_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_expr_419_);
lean_dec_ref_known(v_e_374_, 2);
v_e_374_ = v_expr_419_;
v_a_375_ = v___x_400_;
goto _start;
}
case 5:
{
lean_object* v_fn_421_; lean_object* v_arg_422_; lean_object* v___x_423_; 
v_fn_421_ = lean_ctor_get(v_e_374_, 0);
lean_inc_ref(v_fn_421_);
v_arg_422_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_arg_422_);
lean_dec_ref_known(v_e_374_, 2);
v___x_423_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_373_, v_fn_421_, v___x_400_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_fst_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_fst_425_ = lean_ctor_get(v_a_424_, 0);
if (lean_obj_tag(v_fst_425_) == 0)
{
lean_dec_ref(v_arg_422_);
return v___x_423_;
}
else
{
lean_object* v_snd_426_; 
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v_snd_426_ = lean_ctor_get(v_a_424_, 1);
lean_inc(v_snd_426_);
lean_dec(v_a_424_);
v_e_374_ = v_arg_422_;
v_a_375_ = v_snd_426_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_422_);
return v___x_423_;
}
}
case 2:
{
lean_object* v_mvarId_428_; lean_object* v___x_429_; 
v_mvarId_428_ = lean_ctor_get(v_e_374_, 0);
lean_inc(v_mvarId_428_);
lean_dec_ref_known(v_e_374_, 1);
v___x_429_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_373_, v_mvarId_428_, v___x_400_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_429_;
}
default: 
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v_e_374_);
v___x_430_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_400_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_e_374_);
v___x_433_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_a_375_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
v___jp_385_:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_373_, v_d_386_, v___y_388_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_fst_391_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_fst_391_ = lean_ctor_get(v_a_390_, 0);
if (lean_obj_tag(v_fst_391_) == 0)
{
lean_dec_ref(v_b_387_);
return v___x_389_;
}
else
{
lean_object* v_snd_392_; 
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_snd_392_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_snd_392_);
lean_dec(v_a_390_);
v_e_374_ = v_b_387_;
v_a_375_ = v_snd_392_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_387_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_373_ = stack[0].m_obj;
lean_object* v_e_374_ = stack[1].m_obj;
lean_object* v_a_375_ = stack[2].m_obj;
lean_object* v___y_376_ = stack[3].m_obj;
lean_object* v___y_377_ = stack[4].m_obj;
lean_object* v___y_378_ = stack[5].m_obj;
lean_object* v___y_379_ = stack[6].m_obj;
lean_object* v___y_380_ = stack[7].m_obj;
lean_object* v___y_381_ = stack[8].m_obj;
lean_object* v___y_382_ = stack[9].m_obj;
lean_object* v___y_383_ = stack[10].m_obj;
lean_object* v_res_436_;
v_res_436_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_373_, v_e_374_, v_a_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_436_;
}
lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(lean_object* v_mvarId_437_, lean_object* v_mvarId_x27_438_, lean_object* v_a_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_instBEqMVarId_beq(v_mvarId_437_, v_mvarId_x27_438_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_x27_438_, v_a_439_, v___y_445_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_534_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_534_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_534_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_534_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_fst_455_; 
v_fst_455_ = lean_ctor_get(v_a_451_, 0);
lean_inc(v_fst_455_);
if (lean_obj_tag(v_fst_455_) == 0)
{
lean_object* v_snd_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_mvarId_x27_438_);
v_snd_456_ = lean_ctor_get(v_a_451_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_a_451_, 0);
lean_dec(v_unused_475_);
v___x_458_ = v_a_451_;
v_isShared_459_ = v_isSharedCheck_474_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snd_456_);
lean_dec(v_a_451_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_474_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_473_; 
v_a_460_ = lean_ctor_get(v_fst_455_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_fst_455_);
if (v_isSharedCheck_473_ == 0)
{
v___x_462_ = v_fst_455_;
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v_fst_455_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_472_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_465_);
v___x_467_ = v___x_458_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_456_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_467_);
v___x_469_ = v___x_453_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
else
{
lean_object* v_a_476_; 
lean_del_object(v___x_453_);
v_a_476_ = lean_ctor_get(v_fst_455_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_fst_455_, 1);
if (lean_obj_tag(v_a_476_) == 0)
{
lean_object* v_snd_477_; lean_object* v___x_478_; 
v_snd_477_ = lean_ctor_get(v_a_451_, 1);
lean_inc(v_snd_477_);
lean_dec(v_a_451_);
v___x_478_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_x27_438_, v_snd_477_, v___y_445_);
lean_dec(v_mvarId_x27_438_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_522_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_522_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_522_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_522_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_fst_483_; 
v_fst_483_ = lean_ctor_get(v_a_479_, 0);
lean_inc(v_fst_483_);
if (lean_obj_tag(v_fst_483_) == 0)
{
lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_502_; 
v_snd_484_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_a_479_, 0);
lean_dec(v_unused_503_);
v___x_486_ = v_a_479_;
v_isShared_487_ = v_isSharedCheck_502_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_dec(v_a_479_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_502_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_501_; 
v_a_488_ = lean_ctor_get(v_fst_483_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_fst_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_490_ = v_fst_483_;
v_isShared_491_ = v_isSharedCheck_501_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v_fst_483_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_501_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_500_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_493_);
v___x_495_ = v___x_486_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_snd_484_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_495_);
v___x_497_ = v___x_481_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
else
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v_fst_483_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v_fst_483_, 1);
if (lean_obj_tag(v_a_504_) == 0)
{
lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_516_; 
v_snd_505_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_a_479_, 0);
lean_dec(v_unused_517_);
v___x_507_ = v_a_479_;
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_dec(v_a_479_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_505_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_511_);
v___x_513_ = v___x_481_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
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
lean_object* v_val_518_; lean_object* v_snd_519_; lean_object* v_mvarIdPending_520_; 
lean_del_object(v___x_481_);
v_val_518_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_a_504_, 1);
v_snd_519_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_snd_519_);
lean_dec(v_a_479_);
v_mvarIdPending_520_ = lean_ctor_get(v_val_518_, 1);
lean_inc(v_mvarIdPending_520_);
lean_dec(v_val_518_);
v_mvarId_x27_438_ = v_mvarIdPending_520_;
v_a_439_ = v_snd_519_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_478_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_478_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_snd_531_; lean_object* v_val_532_; lean_object* v___x_533_; 
lean_dec(v_mvarId_x27_438_);
v_snd_531_ = lean_ctor_get(v_a_451_, 1);
lean_inc(v_snd_531_);
lean_dec(v_a_451_);
v_val_532_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v_a_476_, 1);
v___x_533_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_437_, v_val_532_, v_snd_531_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_mvarId_x27_438_);
v_a_535_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_450_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_450_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_mvarId_x27_438_);
v___x_543_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1));
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_a_439_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_437_ = stack[0].m_obj;
lean_object* v_mvarId_x27_438_ = stack[1].m_obj;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v___y_440_ = stack[3].m_obj;
lean_object* v___y_441_ = stack[4].m_obj;
lean_object* v___y_442_ = stack[5].m_obj;
lean_object* v___y_443_ = stack[6].m_obj;
lean_object* v___y_444_ = stack[7].m_obj;
lean_object* v___y_445_ = stack[8].m_obj;
lean_object* v___y_446_ = stack[9].m_obj;
lean_object* v___y_447_ = stack[10].m_obj;
lean_object* v_res_546_;
v_res_546_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_437_, v_mvarId_x27_438_, v_a_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(lean_object* v_mvarId_547_, lean_object* v_mvarId_x27_548_, lean_object* v_a_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_547_, v_mvarId_x27_548_, v_a_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v_mvarId_547_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(lean_object* v_mvarId_560_, lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_560_, v_e_561_, v_a_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v_mvarId_560_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_unsigned_to_nat(16u);
v___x_575_ = lean_mk_array(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
return v___x_578_;
}
}
lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_mvarId_579_, lean_object* v_e_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_Expr_hasExprMVar(v_e_580_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref(v_e_580_);
v___x_591_ = 1;
v___x_592_ = lean_box(v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 0;
v___x_595_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
v___x_596_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_579_, v_e_580_, v___x_595_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_610_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_fst_601_; 
v_fst_601_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_fst_601_);
lean_dec(v_a_597_);
if (lean_obj_tag(v_fst_601_) == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref_known(v_fst_601_, 1);
v___x_602_ = lean_box(v___x_594_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref_known(v_fst_601_, 1);
v___x_606_ = lean_box(v___x_590_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_606_);
v___x_608_ = v___x_599_;
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
v_a_611_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_596_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_596_);
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
}
}
LEAN_EXPORT void l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_579_ = stack[0].m_obj;
lean_object* v_e_580_ = stack[1].m_obj;
lean_object* v___y_581_ = stack[2].m_obj;
lean_object* v___y_582_ = stack[3].m_obj;
lean_object* v___y_583_ = stack[4].m_obj;
lean_object* v___y_584_ = stack[5].m_obj;
lean_object* v___y_585_ = stack[6].m_obj;
lean_object* v___y_586_ = stack[7].m_obj;
lean_object* v___y_587_ = stack[8].m_obj;
lean_object* v___y_588_ = stack[9].m_obj;
lean_object* v_res_619_;
v_res_619_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_579_, v_e_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_mvarId_620_, lean_object* v_e_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_620_, v_e_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v_mvarId_620_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
if (lean_obj_tag(v_a_634_) == 0)
{
lean_object* v___x_636_; 
v___x_636_ = l_List_reverse___redArg(v_a_635_);
return v___x_636_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
v_head_637_ = lean_ctor_get(v_a_634_, 0);
v_tail_638_ = lean_ctor_get(v_a_634_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_640_ = v_a_634_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_head_637_);
lean_dec(v_a_634_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v_index_643_; uint8_t v___x_644_; 
lean_inc(v_head_637_);
v___x_642_ = l_Lean_MetavarContext_getDecl(v___x_632_, v_head_637_);
v_index_643_ = lean_ctor_get(v___x_642_, 6);
lean_inc(v_index_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = lean_nat_dec_le(v___x_633_, v_index_643_);
lean_dec(v_index_643_);
if (v___x_644_ == 0)
{
lean_del_object(v___x_640_);
lean_dec(v_head_637_);
v_a_634_ = v_tail_638_;
goto _start;
}
else
{
lean_object* v___x_647_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_a_635_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_head_637_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_635_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v_a_634_ = v_tail_638_;
v_a_635_ = v___x_647_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v___x_651_, v___x_652_, v_a_653_, v_a_654_);
lean_dec(v___x_652_);
lean_dec_ref(v___x_651_);
return v_res_655_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(lean_object* v_msgData_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_env_663_; uint8_t v___x_664_; lean_object* v_env_665_; lean_object* v___x_666_; lean_object* v_toCold_667_; lean_object* v_mctx_668_; lean_object* v_lctx_669_; lean_object* v_options_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_662_ = lean_st_ref_get(v___y_660_);
v_env_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_env_663_);
lean_dec(v___x_662_);
v___x_664_ = 0;
v_env_665_ = l_Lean_Environment_setRecordingDeps(v_env_663_, v___x_664_);
v___x_666_ = lean_st_ref_get(v___y_658_);
v_toCold_667_ = lean_ctor_get(v___y_659_, 0);
v_mctx_668_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref(v_mctx_668_);
lean_dec(v___x_666_);
v_lctx_669_ = lean_ctor_get(v___y_657_, 2);
v_options_670_ = lean_ctor_get(v_toCold_667_, 2);
lean_inc_ref(v_options_670_);
lean_inc_ref(v_lctx_669_);
v___x_671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_671_, 0, v_env_665_);
lean_ctor_set(v___x_671_, 1, v_mctx_668_);
lean_ctor_set(v___x_671_, 2, v_lctx_669_);
lean_ctor_set(v___x_671_, 3, v_options_670_);
v___x_672_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_msgData_656_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_656_ = stack[0].m_obj;
lean_object* v___y_657_ = stack[1].m_obj;
lean_object* v___y_658_ = stack[2].m_obj;
lean_object* v___y_659_ = stack[3].m_obj;
lean_object* v___y_660_ = stack[4].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object* v_msgData_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_ref_688_; lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_ref_688_ = lean_ctor_get(v___y_685_, 2);
v___x_689_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_inc(v_ref_688_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_ref_688_);
lean_ctor_set(v___x_694_, 1, v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_682_ = stack[0].m_obj;
lean_object* v___y_683_ = stack[1].m_obj;
lean_object* v___y_684_ = stack[2].m_obj;
lean_object* v___y_685_ = stack[3].m_obj;
lean_object* v___y_686_ = stack[4].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object* v_ref_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_toCold_718_; lean_object* v_currRecDepth_719_; lean_object* v_ref_720_; uint16_t v_optionFlags_721_; uint8_t v_suppressElabErrors_722_; uint8_t v_isRecordingDeps_723_; lean_object* v_ref_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_toCold_718_ = lean_ctor_get(v___y_715_, 0);
v_currRecDepth_719_ = lean_ctor_get(v___y_715_, 1);
v_ref_720_ = lean_ctor_get(v___y_715_, 2);
v_optionFlags_721_ = lean_ctor_get_uint16(v___y_715_, sizeof(void*)*3);
v_suppressElabErrors_722_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*3 + 2);
v_isRecordingDeps_723_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*3 + 3);
v_ref_724_ = l_Lean_replaceRef(v_ref_707_, v_ref_720_);
lean_inc(v_currRecDepth_719_);
lean_inc_ref(v_toCold_718_);
v___x_725_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_725_, 0, v_toCold_718_);
lean_ctor_set(v___x_725_, 1, v_currRecDepth_719_);
lean_ctor_set(v___x_725_, 2, v_ref_724_);
lean_ctor_set_uint16(v___x_725_, sizeof(void*)*3, v_optionFlags_721_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*3 + 2, v_suppressElabErrors_722_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*3 + 3, v_isRecordingDeps_723_);
v___x_726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_708_, v___y_713_, v___y_714_, v___x_725_, v___y_716_);
lean_dec_ref_known(v___x_725_, 3);
return v___x_726_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_707_ = stack[0].m_obj;
lean_object* v_msg_708_ = stack[1].m_obj;
lean_object* v___y_709_ = stack[2].m_obj;
lean_object* v___y_710_ = stack[3].m_obj;
lean_object* v___y_711_ = stack[4].m_obj;
lean_object* v___y_712_ = stack[5].m_obj;
lean_object* v___y_713_ = stack[6].m_obj;
lean_object* v___y_714_ = stack[7].m_obj;
lean_object* v___y_715_ = stack[8].m_obj;
lean_object* v___y_716_ = stack[9].m_obj;
lean_object* v_res_727_;
v_res_727_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_707_, v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_728_, v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_ref_728_);
return v_res_739_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_746_, lean_object* v_e_747_, lean_object* v_stx_748_, uint8_t v_symm_749_, lean_object* v_config_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_mctx_761_; lean_object* v_mvarCounter_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; 
v___x_760_ = lean_st_ref_get(v_a_756_);
v_mctx_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_mctx_761_);
lean_dec(v___x_760_);
v_mvarCounter_762_ = lean_ctor_get(v_mctx_761_, 3);
lean_inc(v_mvarCounter_762_);
lean_dec_ref(v_mctx_761_);
v___x_763_ = lean_box(0);
v___x_764_ = 1;
lean_inc(v_stx_748_);
v___x_765_ = l_Lean_Elab_Tactic_elabTerm(v_stx_748_, v___x_763_, v___x_764_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; uint8_t v___x_838_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc_n(v_a_766_, 2);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_box(v_symm_749_);
lean_inc_ref(v_e_747_);
lean_inc(v_mvarId_746_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_768_, 0, v_mvarId_746_);
lean_closure_set(v___f_768_, 1, v_e_747_);
lean_closure_set(v___f_768_, 2, v_a_766_);
lean_closure_set(v___f_768_, 3, v___x_767_);
lean_closure_set(v___f_768_, 4, v_config_750_);
v___x_838_ = l_Lean_Expr_hasSyntheticSorry(v_a_766_);
if (v___x_838_ == 0)
{
v___y_802_ = v_a_751_;
v___y_803_ = v_a_752_;
v___y_804_ = v_a_753_;
v___y_805_ = v_a_754_;
v___y_806_ = v_a_755_;
v___y_807_ = v_a_756_;
v___y_808_ = v_a_757_;
v___y_809_ = v_a_758_;
goto v___jp_801_;
}
else
{
lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v___f_768_);
lean_dec(v_a_766_);
lean_dec(v_mvarCounter_762_);
lean_dec(v_stx_748_);
lean_dec_ref(v_e_747_);
lean_dec(v_mvarId_746_);
v___x_839_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
v___jp_769_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_747_, v___f_768_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_800_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_800_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_mctx_784_; lean_object* v_eNew_785_; lean_object* v_eqProof_786_; lean_object* v_mvarIds_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_799_; 
v___x_783_ = lean_st_ref_get(v___y_775_);
v_mctx_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc_ref(v_mctx_784_);
lean_dec(v___x_783_);
v_eNew_785_ = lean_ctor_get(v_a_779_, 0);
v_eqProof_786_ = lean_ctor_get(v_a_779_, 1);
v_mvarIds_787_ = lean_ctor_get(v_a_779_, 2);
v_isSharedCheck_799_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_799_ == 0)
{
v___x_789_ = v_a_779_;
v_isShared_790_ = v_isSharedCheck_799_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_mvarIds_787_);
lean_inc(v_eqProof_786_);
lean_inc(v_eNew_785_);
lean_dec(v_a_779_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_799_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_box(0);
v___x_792_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_784_, v_mvarCounter_762_, v_mvarIds_787_, v___x_791_);
lean_dec(v_mvarCounter_762_);
lean_dec_ref(v_mctx_784_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_eNew_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_eqProof_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v___x_792_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_794_);
v___x_796_ = v___x_781_;
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
}
else
{
lean_dec(v_mvarCounter_762_);
return v___x_778_;
}
}
v___jp_801_:
{
lean_object* v___x_810_; 
lean_inc(v_a_766_);
v___x_810_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_746_, v_a_766_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; uint8_t v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v___f_768_);
lean_dec(v_mvarCounter_762_);
lean_dec_ref(v_e_747_);
v___x_813_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_814_ = l_Lean_indentExpr(v_a_766_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Expr_mvar___override(v_mvarId_746_);
v___x_819_ = l_Lean_MessageData_ofExpr(v___x_818_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_817_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_748_, v___x_820_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v_stx_748_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_dec(v_a_766_);
lean_dec(v_stx_748_);
lean_dec(v_mvarId_746_);
v___y_770_ = v___y_802_;
v___y_771_ = v___y_803_;
v___y_772_ = v___y_804_;
v___y_773_ = v___y_805_;
v___y_774_ = v___y_806_;
v___y_775_ = v___y_807_;
v___y_776_ = v___y_808_;
v___y_777_ = v___y_809_;
goto v___jp_769_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___f_768_);
lean_dec(v_a_766_);
lean_dec(v_mvarCounter_762_);
lean_dec(v_stx_748_);
lean_dec_ref(v_e_747_);
lean_dec(v_mvarId_746_);
v_a_830_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_810_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_810_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_mvarCounter_762_);
lean_dec_ref(v_config_750_);
lean_dec(v_stx_748_);
lean_dec_ref(v_e_747_);
lean_dec(v_mvarId_746_);
v_a_848_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_765_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_765_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabRewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_746_ = stack[0].m_obj;
lean_object* v_e_747_ = stack[1].m_obj;
lean_object* v_stx_748_ = stack[2].m_obj;
uint8_t v_symm_749_ = stack[3].m_num;
lean_object* v_config_750_ = stack[4].m_obj;
lean_object* v_a_751_ = stack[5].m_obj;
lean_object* v_a_752_ = stack[6].m_obj;
lean_object* v_a_753_ = stack[7].m_obj;
lean_object* v_a_754_ = stack[8].m_obj;
lean_object* v_a_755_ = stack[9].m_obj;
lean_object* v_a_756_ = stack[10].m_obj;
lean_object* v_a_757_ = stack[11].m_obj;
lean_object* v_a_758_ = stack[12].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_746_, v_e_747_, v_stx_748_, v_symm_749_, v_config_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_857_, lean_object* v_e_858_, lean_object* v_stx_859_, lean_object* v_symm_860_, lean_object* v_config_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_symm_boxed_871_; lean_object* v_res_872_; 
v_symm_boxed_871_ = lean_unbox(v_symm_860_);
v_res_872_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_857_, v_e_858_, v_stx_859_, v_symm_boxed_871_, v_config_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_872_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_873_, lean_object* v_ref_874_, lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_874_, v_msg_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_885_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_874_ = stack[1].m_obj;
lean_object* v_msg_875_ = stack[2].m_obj;
lean_object* v___y_876_ = stack[3].m_obj;
lean_object* v___y_877_ = stack[4].m_obj;
lean_object* v___y_878_ = stack[5].m_obj;
lean_object* v___y_879_ = stack[6].m_obj;
lean_object* v___y_880_ = stack[7].m_obj;
lean_object* v___y_881_ = stack[8].m_obj;
lean_object* v___y_882_ = stack[9].m_obj;
lean_object* v___y_883_ = stack[10].m_obj;
lean_object* v_res_886_;
v_res_886_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_box(0), v_ref_874_, v_msg_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_887_, lean_object* v_ref_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_887_, v_ref_888_, v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v_ref_888_);
return v_res_899_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_901_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_901_ = stack[1].m_obj;
lean_object* v___y_902_ = stack[2].m_obj;
lean_object* v___y_903_ = stack[3].m_obj;
lean_object* v___y_904_ = stack[4].m_obj;
lean_object* v___y_905_ = stack[5].m_obj;
lean_object* v___y_906_ = stack[6].m_obj;
lean_object* v___y_907_ = stack[7].m_obj;
lean_object* v___y_908_ = stack[8].m_obj;
lean_object* v___y_909_ = stack[9].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_box(0), v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_913_, v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_924_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_a_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_926_, v_a_927_);
return v___x_928_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_926_ = stack[1].m_obj;
lean_object* v_a_927_ = stack[2].m_obj;
uint8_t v_res_929_;
v_res_929_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_box(0), v_m_926_, v_a_927_);
stack->m_num = v_res_929_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_930_, v_m_931_, v_a_932_);
lean_dec_ref(v_a_932_);
lean_dec_ref(v_m_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_935_, lean_object* v_m_936_, lean_object* v_a_937_, lean_object* v_b_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_936_, v_a_937_, v_b_938_);
return v___x_939_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_940_, v___y_941_, v___y_947_);
return v___x_951_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_940_ = stack[0].m_obj;
lean_object* v___y_941_ = stack[1].m_obj;
lean_object* v___y_942_ = stack[2].m_obj;
lean_object* v___y_943_ = stack[3].m_obj;
lean_object* v___y_944_ = stack[4].m_obj;
lean_object* v___y_945_ = stack[5].m_obj;
lean_object* v___y_946_ = stack[6].m_obj;
lean_object* v___y_947_ = stack[7].m_obj;
lean_object* v___y_948_ = stack[8].m_obj;
lean_object* v___y_949_ = stack[9].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_mvarId_953_);
return v_res_964_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_965_, v___y_966_, v___y_972_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_965_ = stack[0].m_obj;
lean_object* v___y_966_ = stack[1].m_obj;
lean_object* v___y_967_ = stack[2].m_obj;
lean_object* v___y_968_ = stack[3].m_obj;
lean_object* v___y_969_ = stack[4].m_obj;
lean_object* v___y_970_ = stack[5].m_obj;
lean_object* v___y_971_ = stack[6].m_obj;
lean_object* v___y_972_ = stack[7].m_obj;
lean_object* v___y_973_ = stack[8].m_obj;
lean_object* v___y_974_ = stack[9].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v_mvarId_978_);
return v_res_989_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_990_, lean_object* v_a_991_, lean_object* v_x_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_991_ = stack[1].m_obj;
lean_object* v_x_992_ = stack[2].m_obj;
uint8_t v_res_994_;
v_res_994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_box(0), v_a_991_, v_x_992_);
stack->m_num = v_res_994_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_995_, lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_995_, v_a_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec_ref(v_a_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1000_, lean_object* v_data_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1003_, lean_object* v_i_1004_, lean_object* v_source_1005_, lean_object* v_target_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_1004_, v_source_1005_, v_target_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_1009_, v_x_1010_);
return v___x_1011_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1012_, v_x_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1019_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1019_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1012_ = stack[0].m_obj;
lean_object* v_x_1013_ = stack[1].m_obj;
lean_object* v___y_1014_ = stack[2].m_obj;
lean_object* v___y_1015_ = stack[3].m_obj;
lean_object* v___y_1016_ = stack[4].m_obj;
lean_object* v___y_1017_ = stack[5].m_obj;
lean_object* v_res_1036_;
v_res_1036_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1012_, v_x_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1036_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1037_, v_x_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1045_, lean_object* v_mvarId_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1046_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1046_ = stack[1].m_obj;
lean_object* v_x_1047_ = stack[2].m_obj;
lean_object* v___y_1048_ = stack[3].m_obj;
lean_object* v___y_1049_ = stack[4].m_obj;
lean_object* v___y_1050_ = stack[5].m_obj;
lean_object* v___y_1051_ = stack[6].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_box(0), v_mvarId_1046_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_mvarId_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1055_, v_mvarId_1056_, v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1063_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_array_get_size(v_keys_1064_);
v___x_1068_ = lean_nat_dec_lt(v_i_1065_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec(v_i_1065_);
return v___x_1068_;
}
else
{
lean_object* v_k_x27_1069_; uint8_t v___x_1070_; 
v_k_x27_1069_ = lean_array_fget_borrowed(v_keys_1064_, v_i_1065_);
v___x_1070_ = l_Lean_instBEqMVarId_beq(v_k_1066_, v_k_x27_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_add(v_i_1065_, v___x_1071_);
lean_dec(v_i_1065_);
v_i_1065_ = v___x_1072_;
goto _start;
}
else
{
lean_dec(v_i_1065_);
return v___x_1068_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1064_ = stack[0].m_obj;
lean_object* v_i_1065_ = stack[1].m_obj;
lean_object* v_k_1066_ = stack[2].m_obj;
uint8_t v_res_1074_;
v_res_1074_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1064_, v_i_1065_, v_k_1066_);
stack->m_num = v_res_1074_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1075_, lean_object* v_i_1076_, lean_object* v_k_1077_){
_start:
{
uint8_t v_res_1078_; lean_object* v_r_1079_; 
v_res_1078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1075_, v_i_1076_, v_k_1077_);
lean_dec(v_k_1077_);
lean_dec_ref(v_keys_1075_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1080_, size_t v_x_1081_, lean_object* v_x_1082_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v_es_1083_; lean_object* v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; lean_object* v_j_1087_; lean_object* v___x_1088_; 
v_es_1083_ = lean_ctor_get(v_x_1080_, 0);
v___x_1084_ = lean_box(2);
v___x_1085_ = ((size_t)31ULL);
v___x_1086_ = lean_usize_land(v_x_1081_, v___x_1085_);
v_j_1087_ = lean_usize_to_nat(v___x_1086_);
v___x_1088_ = lean_array_get_borrowed(v___x_1084_, v_es_1083_, v_j_1087_);
lean_dec(v_j_1087_);
switch(lean_obj_tag(v___x_1088_))
{
case 0:
{
lean_object* v_key_1089_; uint8_t v___x_1090_; 
v_key_1089_ = lean_ctor_get(v___x_1088_, 0);
v___x_1090_ = l_Lean_instBEqMVarId_beq(v_x_1082_, v_key_1089_);
return v___x_1090_;
}
case 1:
{
lean_object* v_node_1091_; size_t v___x_1092_; size_t v___x_1093_; 
v_node_1091_ = lean_ctor_get(v___x_1088_, 0);
v___x_1092_ = ((size_t)5ULL);
v___x_1093_ = lean_usize_shift_right(v_x_1081_, v___x_1092_);
v_x_1080_ = v_node_1091_;
v_x_1081_ = v___x_1093_;
goto _start;
}
default: 
{
uint8_t v___x_1095_; 
v___x_1095_ = 0;
return v___x_1095_;
}
}
}
else
{
lean_object* v_ks_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_ks_1096_ = lean_ctor_get(v_x_1080_, 0);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1096_, v___x_1097_, v_x_1082_);
return v___x_1098_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1080_ = stack[0].m_obj;
size_t v_x_1081_ = stack[1].m_num;
lean_object* v_x_1082_ = stack[2].m_obj;
uint8_t v_res_1099_;
v_res_1099_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1080_, v_x_1081_, v_x_1082_);
stack->m_num = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
size_t v_x_1954__boxed_1103_; uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_x_1954__boxed_1103_ = lean_unbox_usize(v_x_1101_);
lean_dec(v_x_1101_);
v_res_1104_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1100_, v_x_1954__boxed_1103_, v_x_1102_);
lean_dec(v_x_1102_);
lean_dec_ref(v_x_1100_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint64_t v___x_1108_; size_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = l_Lean_instHashableMVarId_hash(v_x_1107_);
v___x_1109_ = lean_uint64_to_usize(v___x_1108_);
v___x_1110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1106_, v___x_1109_, v_x_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1106_ = stack[0].m_obj;
lean_object* v_x_1107_ = stack[1].m_obj;
uint8_t v_res_1111_;
v_res_1111_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1106_, v_x_1107_);
stack->m_num = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1112_, v_x_1113_);
lean_dec(v_x_1113_);
lean_dec_ref(v_x_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_mctx_1120_; lean_object* v_eAssignment_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1119_ = lean_st_ref_get(v___y_1117_);
v_mctx_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_mctx_1120_);
lean_dec(v___x_1119_);
v_eAssignment_1121_ = lean_ctor_get(v_mctx_1120_, 8);
lean_inc_ref(v_eAssignment_1121_);
lean_dec_ref(v_mctx_1120_);
v___x_1122_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1121_, v_mvarId_1116_);
lean_dec_ref(v_eAssignment_1121_);
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1116_ = stack[0].m_obj;
lean_object* v___y_1117_ = stack[1].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1116_, v___y_1117_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec(v_mvarId_1126_);
return v_res_1129_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_x_1131_);
return v___x_1137_;
}
else
{
lean_object* v_head_1138_; lean_object* v_tail_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1152_; 
v_head_1138_ = lean_ctor_get(v_x_1130_, 0);
v_tail_1139_ = lean_ctor_get(v_x_1130_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1141_ = v_x_1130_;
v_isShared_1142_ = v_isSharedCheck_1152_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_tail_1139_);
lean_inc(v_head_1138_);
lean_dec(v_x_1130_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1152_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1148_; lean_object* v_a_1149_; uint8_t v___x_1150_; 
v___x_1148_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1138_, v___y_1133_);
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1150_ == 0)
{
goto v___jp_1143_;
}
else
{
lean_del_object(v___x_1141_);
lean_dec(v_head_1138_);
v_x_1130_ = v_tail_1139_;
goto _start;
}
v___jp_1143_:
{
lean_object* v___x_1145_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_x_1131_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_head_1138_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_x_1131_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v_x_1130_ = v_tail_1139_;
v_x_1131_ = v___x_1145_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1130_ = stack[0].m_obj;
lean_object* v_x_1131_ = stack[1].m_obj;
lean_object* v___y_1132_ = stack[2].m_obj;
lean_object* v___y_1133_ = stack[3].m_obj;
lean_object* v___y_1134_ = stack[4].m_obj;
lean_object* v___y_1135_ = stack[5].m_obj;
lean_object* v_res_1153_;
v_res_1153_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1130_, v_x_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
stack->m_obj
 = v_res_1153_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
lean_inc(v_head_1162_);
v___x_1168_ = l_Lean_MVarId_getType(v_head_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = l_Lean_Meta_isProp(v_a_1169_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1182_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec(v_head_1162_);
v___x_1176_ = lean_box(0);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
uint8_t v___x_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1173_);
v___x_1180_ = 2;
v___x_1181_ = l_Lean_MVarId_setKind___redArg(v_head_1162_, v___x_1180_, v___y_1164_);
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_head_1162_);
v_a_1183_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1170_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1170_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_head_1162_);
v_a_1191_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1168_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1168_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_1162_ = stack[0].m_obj;
lean_object* v___y_1163_ = stack[1].m_obj;
lean_object* v___y_1164_ = stack[2].m_obj;
lean_object* v___y_1165_ = stack[3].m_obj;
lean_object* v___y_1166_ = stack[4].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
if (lean_obj_tag(v_as_1207_) == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
else
{
lean_object* v_head_1215_; lean_object* v_tail_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_head_1215_ = lean_ctor_get(v_as_1207_, 0);
lean_inc_n(v_head_1215_, 2);
v_tail_1216_ = lean_ctor_get(v_as_1207_, 1);
lean_inc(v_tail_1216_);
lean_dec_ref_known(v_as_1207_, 2);
v___f_1217_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1217_, 0, v_head_1215_);
v___x_1218_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1215_, v___f_1217_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_dec_ref_known(v___x_1218_, 1);
v_as_1207_ = v_tail_1216_;
goto _start;
}
else
{
lean_dec(v_tail_1216_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1207_ = stack[0].m_obj;
lean_object* v___y_1208_ = stack[1].m_obj;
lean_object* v___y_1209_ = stack[2].m_obj;
lean_object* v___y_1210_ = stack[3].m_obj;
lean_object* v___y_1211_ = stack[4].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1227_;
}
}
lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_eNew_1234_; lean_object* v_eqProof_1235_; lean_object* v_mvarIds_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1275_; 
v_eNew_1234_ = lean_ctor_get(v_r_1228_, 0);
v_eqProof_1235_ = lean_ctor_get(v_r_1228_, 1);
v_mvarIds_1236_ = lean_ctor_get(v_r_1228_, 2);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_r_1228_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1238_ = v_r_1228_;
v_isShared_1239_ = v_isSharedCheck_1275_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_mvarIds_1236_);
lean_inc(v_eqProof_1235_);
lean_inc(v_eNew_1234_);
lean_dec(v_r_1228_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1275_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_a_1241_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1236_, v___x_1262_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_List_reverse___redArg(v_a_1264_);
v_a_1241_ = v___x_1265_;
goto v___jp_1240_;
}
else
{
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1263_, 1);
v_a_1241_ = v_a_1266_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_del_object(v___x_1238_);
lean_dec_ref(v_eqProof_1235_);
lean_dec_ref(v_eNew_1234_);
v_a_1267_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1263_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; 
lean_inc(v_a_1241_);
v___x_1242_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1241_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1253_);
v___x_1244_ = v___x_1242_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v___x_1242_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 2, v_a_1241_);
v___x_1247_ = v___x_1238_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_eNew_1234_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_eqProof_1235_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_a_1241_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1247_);
v___x_1249_ = v___x_1244_;
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
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1241_);
lean_del_object(v___x_1238_);
lean_dec_ref(v_eqProof_1235_);
lean_dec_ref(v_eNew_1234_);
v_a_1254_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1242_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1242_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_finishElabRewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1228_ = stack[0].m_obj;
lean_object* v_a_1229_ = stack[1].m_obj;
lean_object* v_a_1230_ = stack[2].m_obj;
lean_object* v_a_1231_ = stack[3].m_obj;
lean_object* v_a_1232_ = stack[4].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1283_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1284_, v___y_1286_);
return v___x_1290_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1284_ = stack[0].m_obj;
lean_object* v___y_1285_ = stack[1].m_obj;
lean_object* v___y_1286_ = stack[2].m_obj;
lean_object* v___y_1287_ = stack[3].m_obj;
lean_object* v___y_1288_ = stack[4].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v_mvarId_1292_);
return v_res_1298_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1300_, v_x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1300_ = stack[1].m_obj;
lean_object* v_x_1301_ = stack[2].m_obj;
uint8_t v_res_1303_;
v_res_1303_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_box(0), v_x_1300_, v_x_1301_);
stack->m_num = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_res_1307_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1304_, v_x_1305_, v_x_1306_);
lean_dec(v_x_1306_);
lean_dec_ref(v_x_1305_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1309_, lean_object* v_x_1310_, size_t v_x_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1310_, v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1310_ = stack[1].m_obj;
size_t v_x_1311_ = stack[2].m_num;
lean_object* v_x_1312_ = stack[3].m_obj;
uint8_t v_res_1314_;
v_res_1314_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_box(0), v_x_1310_, v_x_1311_, v_x_1312_);
stack->m_num = v_res_1314_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
size_t v_x_2476__boxed_1319_; uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_x_2476__boxed_1319_ = lean_unbox_usize(v_x_1317_);
lean_dec(v_x_1317_);
v_res_1320_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1315_, v_x_1316_, v_x_2476__boxed_1319_, v_x_1318_);
lean_dec(v_x_1318_);
lean_dec_ref(v_x_1316_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1322_, lean_object* v_keys_1323_, lean_object* v_vals_1324_, lean_object* v_heq_1325_, lean_object* v_i_1326_, lean_object* v_k_1327_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1323_, v_i_1326_, v_k_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1323_ = stack[1].m_obj;
lean_object* v_vals_1324_ = stack[2].m_obj;
lean_object* v_i_1326_ = stack[4].m_obj;
lean_object* v_k_1327_ = stack[5].m_obj;
uint8_t v_res_1329_;
v_res_1329_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_box(0), v_keys_1323_, v_vals_1324_, lean_box(0), v_i_1326_, v_k_1327_);
stack->m_num = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_keys_1331_, lean_object* v_vals_1332_, lean_object* v_heq_1333_, lean_object* v_i_1334_, lean_object* v_k_1335_){
_start:
{
uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_res_1336_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1330_, v_keys_1331_, v_vals_1332_, v_heq_1333_, v_i_1334_, v_k_1335_);
lean_dec(v_k_1335_);
lean_dec_ref(v_vals_1332_);
lean_dec_ref(v_keys_1331_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1338_, uint8_t v_symm_1339_, lean_object* v_config_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1342_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1351_, v_a_1353_, v_stx_1338_, v_symm_1339_, v_config_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1354_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1351_);
lean_dec_ref(v_config_1340_);
lean_dec(v_stx_1338_);
v_a_1355_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1352_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v_config_1340_);
lean_dec(v_stx_1338_);
v_a_1363_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1350_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1350_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1338_ = stack[0].m_obj;
uint8_t v_symm_1339_ = stack[1].m_num;
lean_object* v_config_1340_ = stack[2].m_obj;
lean_object* v___y_1341_ = stack[3].m_obj;
lean_object* v___y_1342_ = stack[4].m_obj;
lean_object* v___y_1343_ = stack[5].m_obj;
lean_object* v___y_1344_ = stack[6].m_obj;
lean_object* v___y_1345_ = stack[7].m_obj;
lean_object* v___y_1346_ = stack[8].m_obj;
lean_object* v___y_1347_ = stack[9].m_obj;
lean_object* v___y_1348_ = stack[10].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1338_, v_symm_1339_, v_config_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1372_, lean_object* v_symm_1373_, lean_object* v_config_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_symm_boxed_1384_; lean_object* v_res_1385_; 
v_symm_boxed_1384_ = lean_unbox(v_symm_1373_);
v_res_1385_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1372_, v_symm_boxed_1384_, v_config_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1385_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1386_, uint8_t v_symm_1387_, lean_object* v_config_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___f_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = lean_box(v_symm_1387_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1399_, 0, v_stx_1386_);
lean_closure_set(v___f_1399_, 1, v___x_1398_);
lean_closure_set(v___f_1399_, 2, v_config_1388_);
v___x_1400_ = 1;
lean_inc(v_a_1390_);
lean_inc_ref(v_a_1389_);
v___x_1401_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1401_, 0, lean_box(0));
lean_closure_set(v___x_1401_, 1, v___f_1399_);
lean_closure_set(v___x_1401_, 2, v_a_1389_);
lean_closure_set(v___x_1401_, 3, v_a_1390_);
v___x_1402_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1401_, v___x_1400_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1403_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1390_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_eNew_1408_; lean_object* v_eqProof_1409_; lean_object* v_mvarIds_1410_; lean_object* v___x_1411_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v_eNew_1408_ = lean_ctor_get(v_a_1405_, 0);
lean_inc_ref(v_eNew_1408_);
v_eqProof_1409_ = lean_ctor_get(v_a_1405_, 1);
lean_inc_ref(v_eqProof_1409_);
v_mvarIds_1410_ = lean_ctor_get(v_a_1405_, 2);
lean_inc(v_mvarIds_1410_);
lean_dec(v_a_1405_);
v___x_1411_ = l_Lean_MVarId_replaceTargetEq(v_a_1407_, v_eNew_1408_, v_eqProof_1409_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_a_1412_);
lean_ctor_set(v___x_1413_, 1, v_mvarIds_1410_);
v___x_1414_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1413_, v_a_1390_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1414_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_mvarIds_1410_);
v_a_1415_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1411_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1411_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_a_1405_);
v_a_1423_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1406_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1406_);
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
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1404_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1404_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1402_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1402_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1386_ = stack[0].m_obj;
uint8_t v_symm_1387_ = stack[1].m_num;
lean_object* v_config_1388_ = stack[2].m_obj;
lean_object* v_a_1389_ = stack[3].m_obj;
lean_object* v_a_1390_ = stack[4].m_obj;
lean_object* v_a_1391_ = stack[5].m_obj;
lean_object* v_a_1392_ = stack[6].m_obj;
lean_object* v_a_1393_ = stack[7].m_obj;
lean_object* v_a_1394_ = stack[8].m_obj;
lean_object* v_a_1395_ = stack[9].m_obj;
lean_object* v_a_1396_ = stack[10].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1386_, v_symm_1387_, v_config_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1448_, lean_object* v_symm_1449_, lean_object* v_config_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
uint8_t v_symm_boxed_1460_; lean_object* v_res_1461_; 
v_symm_boxed_1460_ = lean_unbox(v_symm_1449_);
v_res_1461_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1448_, v_symm_boxed_1460_, v_config_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1461_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(lean_object* v_fvarId_1462_, lean_object* v_stx_1463_, uint8_t v_symm_1464_, lean_object* v_config_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1462_, v___y_1470_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1467_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_LocalDecl_type(v_a_1476_);
lean_dec(v_a_1476_);
v___x_1480_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1478_, v___x_1479_, v_stx_1463_, v_symm_1464_, v_config_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1476_);
lean_dec_ref(v_config_1465_);
lean_dec(v_stx_1463_);
v_a_1481_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1477_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1477_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_config_1465_);
lean_dec(v_stx_1463_);
v_a_1489_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1475_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1475_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1462_ = stack[0].m_obj;
lean_object* v_stx_1463_ = stack[1].m_obj;
uint8_t v_symm_1464_ = stack[2].m_num;
lean_object* v_config_1465_ = stack[3].m_obj;
lean_object* v___y_1466_ = stack[4].m_obj;
lean_object* v___y_1467_ = stack[5].m_obj;
lean_object* v___y_1468_ = stack[6].m_obj;
lean_object* v___y_1469_ = stack[7].m_obj;
lean_object* v___y_1470_ = stack[8].m_obj;
lean_object* v___y_1471_ = stack[9].m_obj;
lean_object* v___y_1472_ = stack[10].m_obj;
lean_object* v___y_1473_ = stack[11].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(v_fvarId_1462_, v_stx_1463_, v_symm_1464_, v_config_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed(lean_object* v_fvarId_1498_, lean_object* v_stx_1499_, lean_object* v_symm_1500_, lean_object* v_config_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v_symm_boxed_1511_; lean_object* v_res_1512_; 
v_symm_boxed_1511_ = lean_unbox(v_symm_1500_);
v_res_1512_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(v_fvarId_1498_, v_stx_1499_, v_symm_boxed_1511_, v_config_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1512_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(lean_object* v_eqProof_1513_, lean_object* v___x_1514_, lean_object* v_eNew_1515_, lean_object* v_a_1516_, lean_object* v_fvarId_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_mkEqMP(v_eqProof_1513_, v___x_1514_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_eNew_1515_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Lean_MVarId_replace(v_a_1516_, v_fvarId_1517_, v_a_1524_, v___x_1525_, v___x_1526_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1527_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_fvarId_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_eNew_1515_);
v_a_1528_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1523_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1523_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqProof_1513_ = stack[0].m_obj;
lean_object* v___x_1514_ = stack[1].m_obj;
lean_object* v_eNew_1515_ = stack[2].m_obj;
lean_object* v_a_1516_ = stack[3].m_obj;
lean_object* v_fvarId_1517_ = stack[4].m_obj;
lean_object* v___y_1518_ = stack[5].m_obj;
lean_object* v___y_1519_ = stack[6].m_obj;
lean_object* v___y_1520_ = stack[7].m_obj;
lean_object* v___y_1521_ = stack[8].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(v_eqProof_1513_, v___x_1514_, v_eNew_1515_, v_a_1516_, v_fvarId_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed(lean_object* v_eqProof_1537_, lean_object* v___x_1538_, lean_object* v_eNew_1539_, lean_object* v_a_1540_, lean_object* v_fvarId_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(v_eqProof_1537_, v___x_1538_, v_eNew_1539_, v_a_1540_, v_fvarId_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(lean_object* v___f_1548_, uint8_t v___x_1549_, lean_object* v_fvarId_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_inc(v___y_1552_);
v___x_1560_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1560_, 0, lean_box(0));
lean_closure_set(v___x_1560_, 1, v___f_1548_);
lean_closure_set(v___x_1560_, 2, v___y_1551_);
lean_closure_set(v___x_1560_, 3, v___y_1552_);
v___x_1561_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1560_, v___x_1549_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1562_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1552_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_eNew_1567_; lean_object* v_eqProof_1568_; lean_object* v_mvarIds_1569_; lean_object* v___x_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc_n(v_a_1566_, 2);
lean_dec_ref_known(v___x_1565_, 1);
v_eNew_1567_ = lean_ctor_get(v_a_1564_, 0);
lean_inc_ref(v_eNew_1567_);
v_eqProof_1568_ = lean_ctor_get(v_a_1564_, 1);
lean_inc_ref(v_eqProof_1568_);
v_mvarIds_1569_ = lean_ctor_get(v_a_1564_, 2);
lean_inc(v_mvarIds_1569_);
lean_dec(v_a_1564_);
lean_inc(v_fvarId_1550_);
v___x_1570_ = l_Lean_mkFVar(v_fvarId_1550_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1571_, 0, v_eqProof_1568_);
lean_closure_set(v___f_1571_, 1, v___x_1570_);
lean_closure_set(v___f_1571_, 2, v_eNew_1567_);
lean_closure_set(v___f_1571_, 3, v_a_1566_);
lean_closure_set(v___f_1571_, 4, v_fvarId_1550_);
v___x_1572_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1566_, v___f_1571_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_fvarId_1574_; lean_object* v_mvarId_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_fvarId_1574_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_fvarId_1574_);
v_mvarId_1575_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_mvarId_1575_);
lean_dec(v_a_1573_);
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_mvarId_1575_);
lean_ctor_set(v___x_1576_, 1, v_mvarIds_1569_);
v___x_1577_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1576_, v___y_1552_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1552_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v___x_1577_, 0);
lean_dec(v_unused_1585_);
v___x_1579_ = v___x_1577_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v___x_1577_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_fvarId_1574_);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_fvarId_1574_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_fvarId_1574_);
v_a_1586_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1577_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1577_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_mvarIds_1569_);
lean_dec(v___y_1552_);
v_a_1594_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1572_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1572_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1564_);
lean_dec(v___y_1552_);
lean_dec(v_fvarId_1550_);
v_a_1602_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1565_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1565_);
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
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___y_1552_);
lean_dec(v_fvarId_1550_);
v_a_1610_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1563_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1563_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v___y_1552_);
lean_dec(v_fvarId_1550_);
v_a_1618_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1561_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1561_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1548_ = stack[0].m_obj;
uint8_t v___x_1549_ = stack[1].m_num;
lean_object* v_fvarId_1550_ = stack[2].m_obj;
lean_object* v___y_1551_ = stack[3].m_obj;
lean_object* v___y_1552_ = stack[4].m_obj;
lean_object* v___y_1553_ = stack[5].m_obj;
lean_object* v___y_1554_ = stack[6].m_obj;
lean_object* v___y_1555_ = stack[7].m_obj;
lean_object* v___y_1556_ = stack[8].m_obj;
lean_object* v___y_1557_ = stack[9].m_obj;
lean_object* v___y_1558_ = stack[10].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(v___f_1548_, v___x_1549_, v_fvarId_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed(lean_object* v___f_1627_, lean_object* v___x_1628_, lean_object* v_fvarId_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v___x_1687__boxed_1639_; lean_object* v_res_1640_; 
v___x_1687__boxed_1639_ = lean_unbox(v___x_1628_);
v_res_1640_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(v___f_1627_, v___x_1687__boxed_1639_, v_fvarId_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1640_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore(lean_object* v_stx_1641_, uint8_t v_symm_1642_, lean_object* v_fvarId_1643_, lean_object* v_config_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v___f_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; 
v___x_1654_ = lean_box(v_symm_1642_);
lean_inc(v_fvarId_1643_);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1655_, 0, v_fvarId_1643_);
lean_closure_set(v___f_1655_, 1, v_stx_1641_);
lean_closure_set(v___f_1655_, 2, v___x_1654_);
lean_closure_set(v___f_1655_, 3, v_config_1644_);
v___x_1656_ = 1;
v___x_1657_ = lean_box(v___x_1656_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1658_, 0, v___f_1655_);
lean_closure_set(v___f_1658_, 1, v___x_1657_);
lean_closure_set(v___f_1658_, 2, v_fvarId_1643_);
v___x_1659_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1658_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1659_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteLocalDeclCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1641_ = stack[0].m_obj;
uint8_t v_symm_1642_ = stack[1].m_num;
lean_object* v_fvarId_1643_ = stack[2].m_obj;
lean_object* v_config_1644_ = stack[3].m_obj;
lean_object* v_a_1645_ = stack[4].m_obj;
lean_object* v_a_1646_ = stack[5].m_obj;
lean_object* v_a_1647_ = stack[6].m_obj;
lean_object* v_a_1648_ = stack[7].m_obj;
lean_object* v_a_1649_ = stack[8].m_obj;
lean_object* v_a_1650_ = stack[9].m_obj;
lean_object* v_a_1651_ = stack[10].m_obj;
lean_object* v_a_1652_ = stack[11].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1641_, v_symm_1642_, v_fvarId_1643_, v_config_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___boxed(lean_object* v_stx_1661_, lean_object* v_symm_1662_, lean_object* v_fvarId_1663_, lean_object* v_config_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
uint8_t v_symm_boxed_1674_; lean_object* v_res_1675_; 
v_symm_boxed_1674_ = lean_unbox(v_symm_1662_);
v_res_1675_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1661_, v_symm_boxed_1674_, v_fvarId_1663_, v_config_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1675_;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1676_, uint8_t v_symm_1677_, lean_object* v_fvarId_1678_, lean_object* v_config_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1676_, v_symm_1677_, v_fvarId_1678_, v_config_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v___x_1690_, 0);
lean_dec(v_unused_1698_);
v___x_1692_ = v___x_1690_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v___x_1690_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1689_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1690_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1690_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_rewriteLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1676_ = stack[0].m_obj;
uint8_t v_symm_1677_ = stack[1].m_num;
lean_object* v_fvarId_1678_ = stack[2].m_obj;
lean_object* v_config_1679_ = stack[3].m_obj;
lean_object* v_a_1680_ = stack[4].m_obj;
lean_object* v_a_1681_ = stack[5].m_obj;
lean_object* v_a_1682_ = stack[6].m_obj;
lean_object* v_a_1683_ = stack[7].m_obj;
lean_object* v_a_1684_ = stack[8].m_obj;
lean_object* v_a_1685_ = stack[9].m_obj;
lean_object* v_a_1686_ = stack[10].m_obj;
lean_object* v_a_1687_ = stack[11].m_obj;
lean_object* v_res_1707_;
v_res_1707_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1676_, v_symm_1677_, v_fvarId_1678_, v_config_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1708_, lean_object* v_symm_1709_, lean_object* v_fvarId_1710_, lean_object* v_config_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
uint8_t v_symm_boxed_1721_; lean_object* v_res_1722_; 
v_symm_boxed_1721_ = lean_unbox(v_symm_1709_);
v_res_1722_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1708_, v_symm_boxed_1721_, v_fvarId_1710_, v_config_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1722_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(lean_object* v_x_1729_, lean_object* v_acc_1730_, uint8_t v_symm_1731_, lean_object* v_id_1732_, lean_object* v_declName_1733_, lean_object* v_hint_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
if (lean_obj_tag(v_a_1735_) == 0)
{
lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_acc_1730_);
lean_dec_ref(v_x_1729_);
v___x_1745_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_MessageData_ofConstName(v_declName_1733_, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1745_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_hint_1734_);
v___x_1752_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1751_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1752_;
}
else
{
lean_object* v_head_1753_; lean_object* v_tail_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_head_1753_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_head_1753_);
v_tail_1754_ = lean_ctor_get(v_a_1735_, 1);
lean_inc(v_tail_1754_);
lean_dec_ref_known(v_a_1735_, 2);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_mkCIdentFrom(v_id_1732_, v_head_1753_, v___x_1755_);
v___x_1757_ = lean_box(v_symm_1731_);
lean_inc_ref(v_x_1729_);
lean_inc(v_acc_1730_);
v___x_1758_ = lean_apply_3(v_x_1729_, v_acc_1730_, v___x_1757_, v___x_1756_);
v___x_1759_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1737_, v_a_1739_, v_a_1741_, v_a_1743_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1758_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_dec(v_a_1760_);
lean_dec(v_tail_1754_);
lean_dec_ref(v_hint_1734_);
lean_dec(v_declName_1733_);
lean_dec(v_acc_1730_);
lean_dec_ref(v_x_1729_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; uint8_t v___y_1764_; uint8_t v___x_1775_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v___x_1775_ = l_Lean_Exception_isInterrupt(v_a_1762_);
if (v___x_1775_ == 0)
{
uint8_t v___x_1776_; 
lean_inc(v_a_1762_);
v___x_1776_ = l_Lean_Exception_isRuntime(v_a_1762_);
v___y_1764_ = v___x_1776_;
goto v___jp_1763_;
}
else
{
v___y_1764_ = v___x_1775_;
goto v___jp_1763_;
}
v___jp_1763_:
{
if (v___y_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec_ref_known(v___x_1761_, 1);
v___x_1765_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1760_, v___y_1764_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_dec_ref_known(v___x_1765_, 1);
v_a_1735_ = v_tail_1754_;
goto _start;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_tail_1754_);
lean_dec_ref(v_hint_1734_);
lean_dec(v_declName_1733_);
lean_dec(v_acc_1730_);
lean_dec_ref(v_x_1729_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1765_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_dec(v_a_1760_);
lean_dec(v_tail_1754_);
lean_dec_ref(v_hint_1734_);
lean_dec(v_declName_1733_);
lean_dec(v_acc_1730_);
lean_dec_ref(v_x_1729_);
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___x_1758_);
lean_dec(v_tail_1754_);
lean_dec_ref(v_hint_1734_);
lean_dec(v_declName_1733_);
lean_dec(v_acc_1730_);
lean_dec_ref(v_x_1729_);
v_a_1777_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1759_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1759_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1729_ = stack[0].m_obj;
lean_object* v_acc_1730_ = stack[1].m_obj;
uint8_t v_symm_1731_ = stack[2].m_num;
lean_object* v_id_1732_ = stack[3].m_obj;
lean_object* v_declName_1733_ = stack[4].m_obj;
lean_object* v_hint_1734_ = stack[5].m_obj;
lean_object* v_a_1735_ = stack[6].m_obj;
lean_object* v_a_1736_ = stack[7].m_obj;
lean_object* v_a_1737_ = stack[8].m_obj;
lean_object* v_a_1738_ = stack[9].m_obj;
lean_object* v_a_1739_ = stack[10].m_obj;
lean_object* v_a_1740_ = stack[11].m_obj;
lean_object* v_a_1741_ = stack[12].m_obj;
lean_object* v_a_1742_ = stack[13].m_obj;
lean_object* v_a_1743_ = stack[14].m_obj;
lean_object* v_res_1785_;
v_res_1785_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1729_, v_acc_1730_, v_symm_1731_, v_id_1732_, v_declName_1733_, v_hint_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
stack->m_obj
 = v_res_1785_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___boxed(lean_object* v_x_1786_, lean_object* v_acc_1787_, lean_object* v_symm_1788_, lean_object* v_id_1789_, lean_object* v_declName_1790_, lean_object* v_hint_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
uint8_t v_symm_boxed_1802_; lean_object* v_res_1803_; 
v_symm_boxed_1802_ = lean_unbox(v_symm_1788_);
v_res_1803_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1786_, v_acc_1787_, v_symm_boxed_1802_, v_id_1789_, v_declName_1790_, v_hint_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_id_1789_);
return v_res_1803_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(lean_object* v_00_u03b1_1804_, lean_object* v_x_1805_, lean_object* v_acc_1806_, uint8_t v_symm_1807_, lean_object* v_id_1808_, lean_object* v_declName_1809_, lean_object* v_hint_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1805_, v_acc_1806_, v_symm_1807_, v_id_1808_, v_declName_1809_, v_hint_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1805_ = stack[1].m_obj;
lean_object* v_acc_1806_ = stack[2].m_obj;
uint8_t v_symm_1807_ = stack[3].m_num;
lean_object* v_id_1808_ = stack[4].m_obj;
lean_object* v_declName_1809_ = stack[5].m_obj;
lean_object* v_hint_1810_ = stack[6].m_obj;
lean_object* v_a_1811_ = stack[7].m_obj;
lean_object* v_a_1812_ = stack[8].m_obj;
lean_object* v_a_1813_ = stack[9].m_obj;
lean_object* v_a_1814_ = stack[10].m_obj;
lean_object* v_a_1815_ = stack[11].m_obj;
lean_object* v_a_1816_ = stack[12].m_obj;
lean_object* v_a_1817_ = stack[13].m_obj;
lean_object* v_a_1818_ = stack[14].m_obj;
lean_object* v_a_1819_ = stack[15].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(lean_box(0), v_x_1805_, v_acc_1806_, v_symm_1807_, v_id_1808_, v_declName_1809_, v_hint_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___boxed(lean_object** _args){
lean_object* v_00_u03b1_1823_ = _args[0];
lean_object* v_x_1824_ = _args[1];
lean_object* v_acc_1825_ = _args[2];
lean_object* v_symm_1826_ = _args[3];
lean_object* v_id_1827_ = _args[4];
lean_object* v_declName_1828_ = _args[5];
lean_object* v_hint_1829_ = _args[6];
lean_object* v_a_1830_ = _args[7];
lean_object* v_a_1831_ = _args[8];
lean_object* v_a_1832_ = _args[9];
lean_object* v_a_1833_ = _args[10];
lean_object* v_a_1834_ = _args[11];
lean_object* v_a_1835_ = _args[12];
lean_object* v_a_1836_ = _args[13];
lean_object* v_a_1837_ = _args[14];
lean_object* v_a_1838_ = _args[15];
lean_object* v_a_1839_ = _args[16];
_start:
{
uint8_t v_symm_boxed_1840_; lean_object* v_res_1841_; 
v_symm_boxed_1840_ = lean_unbox(v_symm_1826_);
v_res_1841_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(v_00_u03b1_1823_, v_x_1824_, v_acc_1825_, v_symm_boxed_1840_, v_id_1827_, v_declName_1828_, v_hint_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_id_1827_);
return v_res_1841_;
}
}
lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(lean_object* v___x_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1842_);
return v___x_1852_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1842_ = stack[0].m_obj;
lean_object* v___y_1843_ = stack[1].m_obj;
lean_object* v___y_1844_ = stack[2].m_obj;
lean_object* v___y_1845_ = stack[3].m_obj;
lean_object* v___y_1846_ = stack[4].m_obj;
lean_object* v___y_1847_ = stack[5].m_obj;
lean_object* v___y_1848_ = stack[6].m_obj;
lean_object* v___y_1849_ = stack[7].m_obj;
lean_object* v___y_1850_ = stack[8].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(v___x_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed(lean_object* v___x_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(v___x_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1864_;
}
}
lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(lean_object* v_a_1865_, lean_object* v_trees_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
lean_inc(v___y_1874_);
lean_inc_ref(v___y_1873_);
lean_inc(v___y_1872_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1869_);
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
v___x_1876_ = lean_apply_9(v_a_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, lean_box(0));
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1877_);
lean_ctor_set(v___x_1881_, 1, v_trees_1866_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v_trees_1866_);
v_a_1886_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1876_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1876_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1865_ = stack[0].m_obj;
lean_object* v_trees_1866_ = stack[1].m_obj;
lean_object* v___y_1867_ = stack[2].m_obj;
lean_object* v___y_1868_ = stack[3].m_obj;
lean_object* v___y_1869_ = stack[4].m_obj;
lean_object* v___y_1870_ = stack[5].m_obj;
lean_object* v___y_1871_ = stack[6].m_obj;
lean_object* v___y_1872_ = stack[7].m_obj;
lean_object* v___y_1873_ = stack[8].m_obj;
lean_object* v___y_1874_ = stack[9].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(v_a_1865_, v_trees_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed(lean_object* v_a_1895_, lean_object* v_trees_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(v_a_1895_, v_trees_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1906_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(32u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1910_ = ((size_t)5ULL);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_unsigned_to_nat(32u);
v___x_1913_ = lean_mk_empty_array_with_capacity(v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1915_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1913_);
lean_ctor_set(v___x_1915_, 2, v___x_1911_);
lean_ctor_set(v___x_1915_, 3, v___x_1911_);
lean_ctor_set_usize(v___x_1915_, 4, v___x_1910_);
return v___x_1915_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v_infoState_1919_; lean_object* v_trees_1920_; lean_object* v___x_1921_; lean_object* v_infoState_1922_; lean_object* v_env_1923_; lean_object* v_nextMacroScope_1924_; lean_object* v_ngen_1925_; lean_object* v_auxDeclNGen_1926_; lean_object* v_traceState_1927_; lean_object* v_cache_1928_; lean_object* v_recordedDeps_1929_; lean_object* v_messages_1930_; lean_object* v_snapshotTasks_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1952_; 
v___x_1918_ = lean_st_ref_get(v___y_1916_);
v_infoState_1919_ = lean_ctor_get(v___x_1918_, 8);
lean_inc_ref(v_infoState_1919_);
lean_dec(v___x_1918_);
v_trees_1920_ = lean_ctor_get(v_infoState_1919_, 2);
lean_inc_ref(v_trees_1920_);
lean_dec_ref(v_infoState_1919_);
v___x_1921_ = lean_st_ref_take(v___y_1916_);
v_infoState_1922_ = lean_ctor_get(v___x_1921_, 8);
v_env_1923_ = lean_ctor_get(v___x_1921_, 0);
v_nextMacroScope_1924_ = lean_ctor_get(v___x_1921_, 1);
v_ngen_1925_ = lean_ctor_get(v___x_1921_, 2);
v_auxDeclNGen_1926_ = lean_ctor_get(v___x_1921_, 3);
v_traceState_1927_ = lean_ctor_get(v___x_1921_, 4);
v_cache_1928_ = lean_ctor_get(v___x_1921_, 5);
v_recordedDeps_1929_ = lean_ctor_get(v___x_1921_, 6);
v_messages_1930_ = lean_ctor_get(v___x_1921_, 7);
v_snapshotTasks_1931_ = lean_ctor_get(v___x_1921_, 9);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1933_ = v___x_1921_;
v_isShared_1934_ = v_isSharedCheck_1952_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snapshotTasks_1931_);
lean_inc(v_infoState_1922_);
lean_inc(v_messages_1930_);
lean_inc(v_recordedDeps_1929_);
lean_inc(v_cache_1928_);
lean_inc(v_traceState_1927_);
lean_inc(v_auxDeclNGen_1926_);
lean_inc(v_ngen_1925_);
lean_inc(v_nextMacroScope_1924_);
lean_inc(v_env_1923_);
lean_dec(v___x_1921_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1952_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
uint8_t v_enabled_1935_; lean_object* v_assignment_1936_; lean_object* v_lazyAssignment_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1950_; 
v_enabled_1935_ = lean_ctor_get_uint8(v_infoState_1922_, sizeof(void*)*3);
v_assignment_1936_ = lean_ctor_get(v_infoState_1922_, 0);
v_lazyAssignment_1937_ = lean_ctor_get(v_infoState_1922_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_infoState_1922_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_infoState_1922_, 2);
lean_dec(v_unused_1951_);
v___x_1939_ = v_infoState_1922_;
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_lazyAssignment_1937_);
lean_inc(v_assignment_1936_);
lean_dec(v_infoState_1922_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 2, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_assignment_1936_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_lazyAssignment_1937_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v___x_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1949_, sizeof(void*)*3, v_enabled_1935_);
v___x_1943_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1945_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 8, v___x_1943_);
v___x_1945_ = v___x_1933_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_env_1923_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_nextMacroScope_1924_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_ngen_1925_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_auxDeclNGen_1926_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_traceState_1927_);
lean_ctor_set(v_reuseFailAlloc_1948_, 5, v_cache_1928_);
lean_ctor_set(v_reuseFailAlloc_1948_, 6, v_recordedDeps_1929_);
lean_ctor_set(v_reuseFailAlloc_1948_, 7, v_messages_1930_);
lean_ctor_set(v_reuseFailAlloc_1948_, 8, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1948_, 9, v_snapshotTasks_1931_);
v___x_1945_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_st_ref_put(v___y_1916_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_trees_1920_);
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1916_ = stack[0].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1916_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1954_);
lean_dec(v___y_1954_);
return v_res_1956_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1957_, lean_object* v_mkInfoTree_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v_a_1966_, lean_object* v_a_x3f_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v_infoState_1970_; lean_object* v_trees_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_st_ref_get(v___y_1957_);
v_infoState_1970_ = lean_ctor_get(v___x_1969_, 8);
lean_inc_ref(v_infoState_1970_);
lean_dec(v___x_1969_);
v_trees_1971_ = lean_ctor_get(v_infoState_1970_, 2);
lean_inc_ref(v_trees_1971_);
lean_dec_ref(v_infoState_1970_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
v___x_1972_ = lean_apply_10(v_mkInfoTree_1958_, v_trees_1971_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1957_, lean_box(0));
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2012_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2012_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2012_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v_infoState_1978_; lean_object* v_env_1979_; lean_object* v_nextMacroScope_1980_; lean_object* v_ngen_1981_; lean_object* v_auxDeclNGen_1982_; lean_object* v_traceState_1983_; lean_object* v_cache_1984_; lean_object* v_recordedDeps_1985_; lean_object* v_messages_1986_; lean_object* v_snapshotTasks_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2011_; 
v___x_1977_ = lean_st_ref_take(v___y_1957_);
v_infoState_1978_ = lean_ctor_get(v___x_1977_, 8);
v_env_1979_ = lean_ctor_get(v___x_1977_, 0);
v_nextMacroScope_1980_ = lean_ctor_get(v___x_1977_, 1);
v_ngen_1981_ = lean_ctor_get(v___x_1977_, 2);
v_auxDeclNGen_1982_ = lean_ctor_get(v___x_1977_, 3);
v_traceState_1983_ = lean_ctor_get(v___x_1977_, 4);
v_cache_1984_ = lean_ctor_get(v___x_1977_, 5);
v_recordedDeps_1985_ = lean_ctor_get(v___x_1977_, 6);
v_messages_1986_ = lean_ctor_get(v___x_1977_, 7);
v_snapshotTasks_1987_ = lean_ctor_get(v___x_1977_, 9);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1989_ = v___x_1977_;
v_isShared_1990_ = v_isSharedCheck_2011_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snapshotTasks_1987_);
lean_inc(v_infoState_1978_);
lean_inc(v_messages_1986_);
lean_inc(v_recordedDeps_1985_);
lean_inc(v_cache_1984_);
lean_inc(v_traceState_1983_);
lean_inc(v_auxDeclNGen_1982_);
lean_inc(v_ngen_1981_);
lean_inc(v_nextMacroScope_1980_);
lean_inc(v_env_1979_);
lean_dec(v___x_1977_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2011_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint8_t v_enabled_1991_; lean_object* v_assignment_1992_; lean_object* v_lazyAssignment_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2009_; 
v_enabled_1991_ = lean_ctor_get_uint8(v_infoState_1978_, sizeof(void*)*3);
v_assignment_1992_ = lean_ctor_get(v_infoState_1978_, 0);
v_lazyAssignment_1993_ = lean_ctor_get(v_infoState_1978_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_infoState_1978_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_infoState_1978_, 2);
lean_dec(v_unused_2010_);
v___x_1995_ = v_infoState_1978_;
v_isShared_1996_ = v_isSharedCheck_2009_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_lazyAssignment_1993_);
lean_inc(v_assignment_1992_);
lean_dec(v_infoState_1978_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2009_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_PersistentArray_push___redArg(v_a_1966_, v_a_1973_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 2, v___x_1998_);
v___x_2000_ = v___x_1995_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_assignment_1992_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_lazyAssignment_1993_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v___x_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3, v_enabled_1991_);
v___x_2000_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 8, v___x_2000_);
v___x_2002_ = v___x_1989_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_env_1979_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_nextMacroScope_1980_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_ngen_1981_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_auxDeclNGen_1982_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_traceState_1983_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v_cache_1984_);
lean_ctor_set(v_reuseFailAlloc_2007_, 6, v_recordedDeps_1985_);
lean_ctor_set(v_reuseFailAlloc_2007_, 7, v_messages_1986_);
lean_ctor_set(v_reuseFailAlloc_2007_, 8, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2007_, 9, v_snapshotTasks_1987_);
v___x_2002_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_st_ref_put(v___y_1957_, v___x_2002_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1997_);
v___x_2005_ = v___x_1975_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1997_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_a_1966_);
v_a_2013_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1972_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1972_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1957_ = stack[0].m_obj;
lean_object* v_mkInfoTree_1958_ = stack[1].m_obj;
lean_object* v___y_1959_ = stack[2].m_obj;
lean_object* v___y_1960_ = stack[3].m_obj;
lean_object* v___y_1961_ = stack[4].m_obj;
lean_object* v___y_1962_ = stack[5].m_obj;
lean_object* v___y_1963_ = stack[6].m_obj;
lean_object* v___y_1964_ = stack[7].m_obj;
lean_object* v___y_1965_ = stack[8].m_obj;
lean_object* v_a_1966_ = stack[9].m_obj;
lean_object* v_a_x3f_1967_ = stack[10].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1957_, v_mkInfoTree_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v_a_1966_, v_a_x3f_1967_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_2022_, lean_object* v_mkInfoTree_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v_a_2031_, lean_object* v_a_x3f_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_2022_, v_mkInfoTree_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v_a_2031_, v_a_x3f_2032_);
lean_dec(v_a_x3f_2032_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2022_);
return v_res_2034_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(lean_object* v_x_2035_, lean_object* v_mkInfoTree_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_infoState_2047_; uint8_t v_enabled_2048_; 
v___x_2046_ = lean_st_ref_get(v___y_2044_);
v_infoState_2047_ = lean_ctor_get(v___x_2046_, 8);
lean_inc_ref(v_infoState_2047_);
lean_dec(v___x_2046_);
v_enabled_2048_ = lean_ctor_get_uint8(v_infoState_2047_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2047_);
if (v_enabled_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec_ref(v_mkInfoTree_2036_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v___x_2049_ = lean_apply_9(v_x_2035_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v_r_2052_; 
v___x_2050_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_2044_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v_r_2052_ = lean_apply_9(v_x_2035_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
if (lean_obj_tag(v_r_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2077_; 
v_a_2053_ = lean_ctor_get(v_r_2052_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_r_2052_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2055_ = v_r_2052_;
v_isShared_2056_ = v_isSharedCheck_2077_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v_r_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2077_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
lean_inc(v_a_2053_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set_tag(v___x_2055_, 1);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_2044_, v_mkInfoTree_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v_a_2051_, v___x_2058_);
lean_dec_ref(v___x_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_2059_, 0);
lean_dec(v_unused_2067_);
v___x_2061_ = v___x_2059_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v___x_2059_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_a_2053_);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2053_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2053_);
v_a_2068_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2059_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2059_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_a_2078_ = lean_ctor_get(v_r_2052_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v_r_2052_, 1);
v___x_2079_ = lean_box(0);
v___x_2080_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_2044_, v_mkInfoTree_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v_a_2051_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2088_);
v___x_2082_ = v___x_2080_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v___x_2080_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 0, v_a_2078_);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2078_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_2078_);
v_a_2089_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2080_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2035_ = stack[0].m_obj;
lean_object* v_mkInfoTree_2036_ = stack[1].m_obj;
lean_object* v___y_2037_ = stack[2].m_obj;
lean_object* v___y_2038_ = stack[3].m_obj;
lean_object* v___y_2039_ = stack[4].m_obj;
lean_object* v___y_2040_ = stack[5].m_obj;
lean_object* v___y_2041_ = stack[6].m_obj;
lean_object* v___y_2042_ = stack[7].m_obj;
lean_object* v___y_2043_ = stack[8].m_obj;
lean_object* v___y_2044_ = stack[9].m_obj;
lean_object* v_res_2097_;
v_res_2097_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2035_, v_mkInfoTree_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
stack->m_obj
 = v_res_2097_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_2098_, lean_object* v_mkInfoTree_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2098_, v_mkInfoTree_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2109_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_id_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2110_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2110_ = stack[0].m_obj;
lean_object* v___y_2111_ = stack[1].m_obj;
lean_object* v___y_2112_ = stack[2].m_obj;
lean_object* v___y_2113_ = stack[3].m_obj;
lean_object* v___y_2114_ = stack[4].m_obj;
lean_object* v___y_2115_ = stack[5].m_obj;
lean_object* v___y_2116_ = stack[6].m_obj;
lean_object* v___y_2117_ = stack[7].m_obj;
lean_object* v___y_2118_ = stack[8].m_obj;
lean_object* v_res_2121_;
v_res_2121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(v_id_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
stack->m_obj
 = v_res_2121_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_id_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(v_id_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2132_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__0));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__2));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_x_2139_, lean_object* v_b_2140_, uint8_t v___y_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_id_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___f_2154_; lean_object* v___x_2155_; 
lean_inc(v_id_2144_);
v___f_2154_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2154_, 0, v_id_2144_);
v___x_2155_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2154_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
if (lean_obj_tag(v_a_2156_) == 0)
{
uint8_t v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = 0;
v___x_2158_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2146_, v___y_2148_, v___y_2150_, v___y_2152_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
lean_inc(v_id_2144_);
v___x_2160_ = l_Lean_realizeGlobalConstNoOverload(v_id_2144_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
lean_dec(v_a_2159_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_n(v_a_2161_, 2);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2161_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
if (lean_obj_tag(v_a_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v___x_2143_);
v_val_2164_ = lean_ctor_get(v_a_2163_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_a_2163_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2166_ = v_a_2163_;
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v_a_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___y_2169_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = lean_array_get_size(v_val_2164_);
v___x_2197_ = lean_nat_dec_eq(v___x_2196_, v___x_2142_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2198_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__1);
v___x_2199_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2161_);
v___x_2200_ = l_Lean_Name_str___override(v_a_2161_, v___x_2199_);
v___x_2201_ = l_Lean_MessageData_ofName(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2198_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_hint_x27(v___x_2204_);
v___y_2169_ = v___x_2205_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___closed__3);
v___y_2169_ = v___x_2206_;
goto v___jp_2168_;
}
v___jp_2168_:
{
lean_object* v___x_2170_; 
lean_inc(v_a_2161_);
v___x_2170_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2161_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_lctx_2172_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_lctx_2172_ = lean_ctor_get(v___y_2149_, 2);
lean_inc_ref(v_lctx_2172_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v_lctx_2172_);
v___x_2174_ = v___x_2166_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_lctx_2172_);
v___x_2174_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_box(0);
lean_inc(v_id_2144_);
v___x_2176_ = l_Lean_Elab_Term_addTermInfo(v_id_2144_, v_a_2171_, v_a_2156_, v___x_2174_, v___x_2175_, v___x_2157_, v___x_2157_, v___x_2157_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2176_, 1);
v___x_2177_ = lean_array_to_list(v_val_2164_);
v___x_2178_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_2139_, v_b_2140_, v___y_2141_, v_id_2144_, v_a_2161_, v___y_2169_, v___x_2177_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v_id_2144_);
return v___x_2178_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v___y_2169_);
lean_dec(v_val_2164_);
lean_dec(v_a_2161_);
lean_dec(v_id_2144_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2179_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2176_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2176_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v___y_2169_);
lean_del_object(v___x_2166_);
lean_dec(v_val_2164_);
lean_dec(v_a_2161_);
lean_dec(v_id_2144_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2188_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2170_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2170_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_a_2163_);
lean_dec(v_a_2161_);
lean_dec(v_id_2144_);
v___x_2208_ = lean_box(v___y_2141_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
v___x_2209_ = lean_apply_12(v_x_2139_, v_b_2140_, v___x_2208_, v___x_2143_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, lean_box(0));
return v___x_2209_;
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2161_);
lean_dec(v_id_2144_);
lean_dec(v___x_2143_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2210_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2162_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2162_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_id_2144_);
v_a_2218_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2220_ = v___x_2160_;
v_isShared_2221_ = v_isSharedCheck_2240_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2160_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2240_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v___y_2223_; uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_Exception_isInterrupt(v_a_2218_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; 
lean_inc(v_a_2218_);
v___x_2239_ = l_Lean_Exception_isRuntime(v_a_2218_);
v___y_2223_ = v___x_2239_;
goto v___jp_2222_;
}
else
{
v___y_2223_ = v___x_2238_;
goto v___jp_2222_;
}
v___jp_2222_:
{
if (v___y_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_del_object(v___x_2220_);
lean_dec(v_a_2218_);
v___x_2224_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2159_, v___y_2223_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2225_ = lean_box(v___y_2141_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
v___x_2226_ = lean_apply_12(v_x_2139_, v_b_2140_, v___x_2225_, v___x_2143_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, lean_box(0));
return v___x_2226_;
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v___x_2143_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2227_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2224_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v___x_2236_; 
lean_dec(v_a_2159_);
lean_dec(v___x_2143_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
if (v_isShared_2221_ == 0)
{
v___x_2236_ = v___x_2220_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2218_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_id_2144_);
lean_dec(v___x_2143_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2241_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2158_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2158_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec_ref_known(v_a_2156_, 1);
lean_dec(v_id_2144_);
v___x_2249_ = lean_box(v___y_2141_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
v___x_2250_ = lean_apply_12(v_x_2139_, v_b_2140_, v___x_2249_, v___x_2143_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, lean_box(0));
return v___x_2250_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_id_2144_);
lean_dec(v___x_2143_);
lean_dec(v_b_2140_);
lean_dec_ref(v_x_2139_);
v_a_2251_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2155_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2155_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2139_ = stack[0].m_obj;
lean_object* v_b_2140_ = stack[1].m_obj;
uint8_t v___y_2141_ = stack[2].m_num;
lean_object* v___x_2142_ = stack[3].m_obj;
lean_object* v___x_2143_ = stack[4].m_obj;
lean_object* v_id_2144_ = stack[5].m_obj;
lean_object* v___y_2145_ = stack[6].m_obj;
lean_object* v___y_2146_ = stack[7].m_obj;
lean_object* v___y_2147_ = stack[8].m_obj;
lean_object* v___y_2148_ = stack[9].m_obj;
lean_object* v___y_2149_ = stack[10].m_obj;
lean_object* v___y_2150_ = stack[11].m_obj;
lean_object* v___y_2151_ = stack[12].m_obj;
lean_object* v___y_2152_ = stack[13].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(v_x_2139_, v_b_2140_, v___y_2141_, v___x_2142_, v___x_2143_, v_id_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_x_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___x_2263_, lean_object* v___x_2264_, lean_object* v_id_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v___y_16210__boxed_2275_; lean_object* v_res_2276_; 
v___y_16210__boxed_2275_ = lean_unbox(v___y_2262_);
v_res_2276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(v_x_2260_, v_b_2261_, v___y_16210__boxed_2275_, v___x_2263_, v___x_2264_, v_id_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___x_2263_);
return v_res_2276_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(lean_object* v_a_2277_, lean_object* v_trees_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
lean_inc(v___y_2286_);
lean_inc_ref(v___y_2285_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
lean_inc(v___y_2280_);
lean_inc_ref(v___y_2279_);
v___x_2288_ = lean_apply_9(v_a_2277_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, lean_box(0));
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_a_2289_);
lean_ctor_set(v___x_2293_, 1, v_trees_2278_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_trees_2278_);
v_a_2298_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2288_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2288_);
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
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2277_ = stack[0].m_obj;
lean_object* v_trees_2278_ = stack[1].m_obj;
lean_object* v___y_2279_ = stack[2].m_obj;
lean_object* v___y_2280_ = stack[3].m_obj;
lean_object* v___y_2281_ = stack[4].m_obj;
lean_object* v___y_2282_ = stack[5].m_obj;
lean_object* v___y_2283_ = stack[6].m_obj;
lean_object* v___y_2284_ = stack[7].m_obj;
lean_object* v___y_2285_ = stack[8].m_obj;
lean_object* v___y_2286_ = stack[9].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(v_a_2277_, v_trees_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object* v_a_2307_, lean_object* v_trees_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(v_a_2307_, v_trees_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2318_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(lean_object* v___x_2328_, uint8_t v___x_2329_, lean_object* v___x_2330_, lean_object* v_x_2331_, lean_object* v_b_2332_, uint8_t v___y_2333_, lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___f_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_toCold_2346_; lean_object* v_currRecDepth_2347_; lean_object* v_ref_2348_; uint16_t v_optionFlags_2349_; uint8_t v_suppressElabErrors_2350_; uint8_t v_isRecordingDeps_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2369_; 
v_toCold_2346_ = lean_ctor_get(v___y_2343_, 0);
v_currRecDepth_2347_ = lean_ctor_get(v___y_2343_, 1);
v_ref_2348_ = lean_ctor_get(v___y_2343_, 2);
v_optionFlags_2349_ = lean_ctor_get_uint16(v___y_2343_, sizeof(void*)*3);
v_suppressElabErrors_2350_ = lean_ctor_get_uint8(v___y_2343_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2351_ = lean_ctor_get_uint8(v___y_2343_, sizeof(void*)*3 + 3);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___y_2343_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2353_ = v___y_2343_;
v_isShared_2354_ = v_isSharedCheck_2369_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_ref_2348_);
lean_inc(v_currRecDepth_2347_);
lean_inc(v_toCold_2346_);
lean_dec(v___y_2343_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2369_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_ref_2355_; lean_object* v___x_2357_; 
v_ref_2355_ = l_Lean_replaceRef(v___x_2328_, v_ref_2348_);
lean_dec(v_ref_2348_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 2, v_ref_2355_);
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_toCold_2346_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_currRecDepth_2347_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_ref_2355_);
lean_ctor_set_uint16(v_reuseFailAlloc_2368_, sizeof(void*)*3, v_optionFlags_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*3 + 2, v_suppressElabErrors_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*3 + 3, v_isRecordingDeps_2351_);
v___x_2357_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
if (v___x_2329_ == 0)
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__4));
lean_inc(v___x_2330_);
v___x_2359_ = l_Lean_Syntax_isOfKind(v___x_2330_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec_ref(v___f_2336_);
v___x_2360_ = lean_box(v___y_2333_);
v___x_2361_ = lean_apply_12(v_x_2331_, v_b_2332_, v___x_2360_, v___x_2330_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___x_2357_, v___y_2344_, lean_box(0));
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = l_Lean_Syntax_getArg(v___x_2330_, v___x_2334_);
lean_inc(v___x_2362_);
v___x_2363_ = l_Lean_Syntax_isOfKind(v___x_2362_, v___x_2335_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec(v___x_2362_);
lean_dec_ref(v___f_2336_);
v___x_2364_ = lean_box(v___y_2333_);
v___x_2365_ = lean_apply_12(v_x_2331_, v_b_2332_, v___x_2364_, v___x_2330_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___x_2357_, v___y_2344_, lean_box(0));
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; 
lean_dec(v_b_2332_);
lean_dec_ref(v_x_2331_);
lean_dec(v___x_2330_);
v___x_2366_ = lean_apply_10(v___f_2336_, v___x_2362_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___x_2357_, v___y_2344_, lean_box(0));
return v___x_2366_;
}
}
}
else
{
lean_object* v___x_2367_; 
lean_dec(v_b_2332_);
lean_dec_ref(v_x_2331_);
v___x_2367_ = lean_apply_10(v___f_2336_, v___x_2330_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___x_2357_, v___y_2344_, lean_box(0));
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2328_ = stack[0].m_obj;
uint8_t v___x_2329_ = stack[1].m_num;
lean_object* v___x_2330_ = stack[2].m_obj;
lean_object* v_x_2331_ = stack[3].m_obj;
lean_object* v_b_2332_ = stack[4].m_obj;
uint8_t v___y_2333_ = stack[5].m_num;
lean_object* v___x_2334_ = stack[6].m_obj;
lean_object* v___x_2335_ = stack[7].m_obj;
lean_object* v___f_2336_ = stack[8].m_obj;
lean_object* v___y_2337_ = stack[9].m_obj;
lean_object* v___y_2338_ = stack[10].m_obj;
lean_object* v___y_2339_ = stack[11].m_obj;
lean_object* v___y_2340_ = stack[12].m_obj;
lean_object* v___y_2341_ = stack[13].m_obj;
lean_object* v___y_2342_ = stack[14].m_obj;
lean_object* v___y_2343_ = stack[15].m_obj;
lean_object* v___y_2344_ = stack[16].m_obj;
lean_object* v_res_2370_;
v_res_2370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(v___x_2328_, v___x_2329_, v___x_2330_, v_x_2331_, v_b_2332_, v___y_2333_, v___x_2334_, v___x_2335_, v___f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
stack->m_obj
 = v_res_2370_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2371_ = _args[0];
lean_object* v___x_2372_ = _args[1];
lean_object* v___x_2373_ = _args[2];
lean_object* v_x_2374_ = _args[3];
lean_object* v_b_2375_ = _args[4];
lean_object* v___y_2376_ = _args[5];
lean_object* v___x_2377_ = _args[6];
lean_object* v___x_2378_ = _args[7];
lean_object* v___f_2379_ = _args[8];
lean_object* v___y_2380_ = _args[9];
lean_object* v___y_2381_ = _args[10];
lean_object* v___y_2382_ = _args[11];
lean_object* v___y_2383_ = _args[12];
lean_object* v___y_2384_ = _args[13];
lean_object* v___y_2385_ = _args[14];
lean_object* v___y_2386_ = _args[15];
lean_object* v___y_2387_ = _args[16];
lean_object* v___y_2388_ = _args[17];
_start:
{
uint8_t v___x_16720__boxed_2389_; uint8_t v___y_16722__boxed_2390_; lean_object* v_res_2391_; 
v___x_16720__boxed_2389_ = lean_unbox(v___x_2372_);
v___y_16722__boxed_2390_ = lean_unbox(v___y_2376_);
v_res_2391_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(v___x_2371_, v___x_16720__boxed_2389_, v___x_2373_, v_x_2374_, v_b_2375_, v___y_16722__boxed_2390_, v___x_2377_, v___x_2378_, v___f_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___x_2378_);
lean_dec(v___x_2377_);
lean_dec(v___x_2371_);
return v_res_2391_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2398_, lean_object* v_rules_2399_, lean_object* v_x_2400_, lean_object* v_a_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_nat_dec_lt(v_a_2401_, v_upperBound_2398_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_a_2401_);
lean_dec_ref(v_x_2400_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2402_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___y_2421_; uint8_t v___y_2422_; lean_object* v___y_2447_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2414_ = lean_unsigned_to_nat(2u);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = lean_nat_mul(v_a_2401_, v___x_2414_);
v___x_2419_ = lean_array_get_borrowed(v___x_2415_, v_rules_2399_, v___x_2418_);
v___x_2457_ = lean_nat_add(v___x_2418_, v___x_2416_);
lean_dec(v___x_2418_);
v___x_2458_ = lean_array_get_size(v_rules_2399_);
v___x_2459_ = lean_nat_dec_lt(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec(v___x_2457_);
v___y_2447_ = v___x_2415_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_array_fget_borrowed(v_rules_2399_, v___x_2457_);
lean_dec(v___x_2457_);
lean_inc(v___x_2460_);
v___y_2447_ = v___x_2460_;
goto v___jp_2446_;
}
v___jp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; 
v___x_2423_ = l_Lean_Syntax_getArg(v___x_2419_, v___x_2416_);
v___x_2424_ = lean_box(v___y_2422_);
lean_inc_n(v___x_2423_, 2);
lean_inc(v_b_2402_);
lean_inc_ref_n(v_x_2400_, 2);
v___f_2425_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_2425_, 0, v_x_2400_);
lean_closure_set(v___f_2425_, 1, v_b_2402_);
lean_closure_set(v___f_2425_, 2, v___x_2424_);
lean_closure_set(v___f_2425_, 3, v___x_2416_);
lean_closure_set(v___f_2425_, 4, v___x_2423_);
v___x_2426_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1));
v___x_2427_ = l_Lean_Syntax_isOfKind(v___x_2423_, v___x_2426_);
v___x_2428_ = lean_box(v___x_2427_);
v___x_2429_ = lean_box(v___y_2422_);
lean_inc(v___x_2419_);
v___f_2430_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed), 18, 9);
lean_closure_set(v___f_2430_, 0, v___x_2419_);
lean_closure_set(v___f_2430_, 1, v___x_2428_);
lean_closure_set(v___f_2430_, 2, v___x_2423_);
lean_closure_set(v___f_2430_, 3, v_x_2400_);
lean_closure_set(v___f_2430_, 4, v_b_2402_);
lean_closure_set(v___f_2430_, 5, v___x_2429_);
lean_closure_set(v___f_2430_, 6, v___x_2416_);
lean_closure_set(v___f_2430_, 7, v___x_2426_);
lean_closure_set(v___f_2430_, 8, v___f_2425_);
v___x_2431_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2421_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___f_2433_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed), 11, 1);
lean_closure_set(v___f_2433_, 0, v_a_2432_);
v___x_2434_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2430_, v___f_2433_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = lean_nat_add(v_a_2401_, v___x_2416_);
lean_dec(v_a_2401_);
v_a_2401_ = v___x_2436_;
v_b_2402_ = v_a_2435_;
goto _start;
}
else
{
lean_dec(v_a_2401_);
lean_dec_ref(v_x_2400_);
return v___x_2434_;
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec_ref(v___f_2430_);
lean_dec(v_a_2401_);
lean_dec_ref(v_x_2400_);
v_a_2438_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2431_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2431_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2448_ = lean_mk_empty_array_with_capacity(v___x_2414_);
lean_inc(v___x_2419_);
v___x_2449_ = lean_array_push(v___x_2448_, v___x_2419_);
v___x_2450_ = lean_array_push(v___x_2449_, v___y_2447_);
v___x_2451_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2452_ = lean_box(2);
v___x_2453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v___x_2451_);
lean_ctor_set(v___x_2453_, 2, v___x_2450_);
v___x_2454_ = l_Lean_Syntax_getArg(v___x_2419_, v___x_2417_);
v___x_2455_ = l_Lean_Syntax_isNone(v___x_2454_);
lean_dec(v___x_2454_);
if (v___x_2455_ == 0)
{
v___y_2421_ = v___x_2453_;
v___y_2422_ = v___x_2412_;
goto v___jp_2420_;
}
else
{
uint8_t v___x_2456_; 
v___x_2456_ = 0;
v___y_2421_ = v___x_2453_;
v___y_2422_ = v___x_2456_;
goto v___jp_2420_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2398_ = stack[0].m_obj;
lean_object* v_rules_2399_ = stack[1].m_obj;
lean_object* v_x_2400_ = stack[2].m_obj;
lean_object* v_a_2401_ = stack[3].m_obj;
lean_object* v_b_2402_ = stack[4].m_obj;
lean_object* v___y_2403_ = stack[5].m_obj;
lean_object* v___y_2404_ = stack[6].m_obj;
lean_object* v___y_2405_ = stack[7].m_obj;
lean_object* v___y_2406_ = stack[8].m_obj;
lean_object* v___y_2407_ = stack[9].m_obj;
lean_object* v___y_2408_ = stack[10].m_obj;
lean_object* v___y_2409_ = stack[11].m_obj;
lean_object* v___y_2410_ = stack[12].m_obj;
lean_object* v_res_2461_;
v_res_2461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2398_, v_rules_2399_, v_x_2400_, v_a_2401_, v_b_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2462_, lean_object* v_rules_2463_, lean_object* v_x_2464_, lean_object* v_a_2465_, lean_object* v_b_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2462_, v_rules_2463_, v_x_2464_, v_a_2465_, v_b_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_rules_2463_);
lean_dec(v_upperBound_2462_);
return v_res_2476_;
}
}
lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(lean_object* v_token_2479_, lean_object* v_rwRulesSeqStx_2480_, lean_object* v_init_2481_, lean_object* v_x_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; lean_object* v_lbrak_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_rules_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; 
v___x_2492_ = lean_unsigned_to_nat(0u);
v_lbrak_2493_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2480_, v___x_2492_);
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2480_, v___x_2494_);
v_rules_2496_ = l_Lean_Syntax_getArgs(v___x_2495_);
lean_dec(v___x_2495_);
v___x_2497_ = lean_unsigned_to_nat(2u);
v___x_2498_ = lean_mk_empty_array_with_capacity(v___x_2497_);
v___x_2499_ = lean_array_push(v___x_2498_, v_token_2479_);
v___x_2500_ = lean_array_push(v___x_2499_, v_lbrak_2493_);
v___x_2501_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2502_ = lean_box(2);
v___x_2503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2501_);
lean_ctor_set(v___x_2503_, 2, v___x_2500_);
v___f_2504_ = ((lean_object*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0));
v___x_2505_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2503_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2507_, 0, v_a_2506_);
v___x_2508_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2504_, v___f_2507_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref_known(v___x_2508_, 1);
v___x_2509_ = lean_array_get_size(v_rules_2496_);
v___x_2510_ = lean_nat_add(v___x_2509_, v___x_2494_);
v___x_2511_ = lean_nat_shiftr(v___x_2510_, v___x_2494_);
lean_dec(v___x_2510_);
v___x_2512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v___x_2511_, v_rules_2496_, v_x_2482_, v___x_2492_, v_init_2481_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
lean_dec_ref(v_rules_2496_);
lean_dec(v___x_2511_);
return v___x_2512_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_rules_2496_);
lean_dec_ref(v_x_2482_);
lean_dec(v_init_2481_);
v_a_2513_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2508_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2508_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_rules_2496_);
lean_dec_ref(v_x_2482_);
lean_dec(v_init_2481_);
v_a_2521_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2505_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2505_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_foldRWRulesSeq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_2479_ = stack[0].m_obj;
lean_object* v_rwRulesSeqStx_2480_ = stack[1].m_obj;
lean_object* v_init_2481_ = stack[2].m_obj;
lean_object* v_x_2482_ = stack[3].m_obj;
lean_object* v_a_2483_ = stack[4].m_obj;
lean_object* v_a_2484_ = stack[5].m_obj;
lean_object* v_a_2485_ = stack[6].m_obj;
lean_object* v_a_2486_ = stack[7].m_obj;
lean_object* v_a_2487_ = stack[8].m_obj;
lean_object* v_a_2488_ = stack[9].m_obj;
lean_object* v_a_2489_ = stack[10].m_obj;
lean_object* v_a_2490_ = stack[11].m_obj;
lean_object* v_res_2529_;
v_res_2529_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2479_, v_rwRulesSeqStx_2480_, v_init_2481_, v_x_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
stack->m_obj
 = v_res_2529_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___boxed(lean_object* v_token_2530_, lean_object* v_rwRulesSeqStx_2531_, lean_object* v_init_2532_, lean_object* v_x_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2530_, v_rwRulesSeqStx_2531_, v_init_2532_, v_x_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_rwRulesSeqStx_2531_);
return v_res_2543_;
}
}
lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq(lean_object* v_00_u03b1_2544_, lean_object* v_token_2545_, lean_object* v_rwRulesSeqStx_2546_, lean_object* v_init_2547_, lean_object* v_x_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2545_, v_rwRulesSeqStx_2546_, v_init_2547_, v_x_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_foldRWRulesSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_2545_ = stack[1].m_obj;
lean_object* v_rwRulesSeqStx_2546_ = stack[2].m_obj;
lean_object* v_init_2547_ = stack[3].m_obj;
lean_object* v_x_2548_ = stack[4].m_obj;
lean_object* v_a_2549_ = stack[5].m_obj;
lean_object* v_a_2550_ = stack[6].m_obj;
lean_object* v_a_2551_ = stack[7].m_obj;
lean_object* v_a_2552_ = stack[8].m_obj;
lean_object* v_a_2553_ = stack[9].m_obj;
lean_object* v_a_2554_ = stack[10].m_obj;
lean_object* v_a_2555_ = stack[11].m_obj;
lean_object* v_a_2556_ = stack[12].m_obj;
lean_object* v_res_2559_;
v_res_2559_ = l_Lean_Elab_Tactic_foldRWRulesSeq(lean_box(0), v_token_2545_, v_rwRulesSeqStx_2546_, v_init_2547_, v_x_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
stack->m_obj
 = v_res_2559_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___boxed(lean_object* v_00_u03b1_2560_, lean_object* v_token_2561_, lean_object* v_rwRulesSeqStx_2562_, lean_object* v_init_2563_, lean_object* v_x_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Elab_Tactic_foldRWRulesSeq(v_00_u03b1_2560_, v_token_2561_, v_rwRulesSeqStx_2562_, v_init_2563_, v_x_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_rwRulesSeqStx_2562_);
return v_res_2574_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2575_ = stack[0].m_obj;
lean_object* v___y_2576_ = stack[1].m_obj;
lean_object* v___y_2577_ = stack[2].m_obj;
lean_object* v___y_2578_ = stack[3].m_obj;
lean_object* v___y_2579_ = stack[4].m_obj;
lean_object* v___y_2580_ = stack[5].m_obj;
lean_object* v___y_2581_ = stack[6].m_obj;
lean_object* v___y_2582_ = stack[7].m_obj;
lean_object* v_res_2585_;
v_res_2585_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
stack->m_obj
 = v_res_2585_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2595_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(lean_object* v_00_u03b1_2596_, lean_object* v_x_2597_, lean_object* v_mkInfoTree_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2597_, v_mkInfoTree_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2597_ = stack[1].m_obj;
lean_object* v_mkInfoTree_2598_ = stack[2].m_obj;
lean_object* v___y_2599_ = stack[3].m_obj;
lean_object* v___y_2600_ = stack[4].m_obj;
lean_object* v___y_2601_ = stack[5].m_obj;
lean_object* v___y_2602_ = stack[6].m_obj;
lean_object* v___y_2603_ = stack[7].m_obj;
lean_object* v___y_2604_ = stack[8].m_obj;
lean_object* v___y_2605_ = stack[9].m_obj;
lean_object* v___y_2606_ = stack[10].m_obj;
lean_object* v_res_2609_;
v_res_2609_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(lean_box(0), v_x_2597_, v_mkInfoTree_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
stack->m_obj
 = v_res_2609_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_x_2611_, lean_object* v_mkInfoTree_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(v_00_u03b1_2610_, v_x_2611_, v_mkInfoTree_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2622_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(lean_object* v_00_u03b1_2623_, lean_object* v_upperBound_2624_, lean_object* v_rules_2625_, lean_object* v_x_2626_, lean_object* v_inst_2627_, lean_object* v_R_2628_, lean_object* v_a_2629_, lean_object* v_b_2630_, lean_object* v_c_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2624_, v_rules_2625_, v_x_2626_, v_a_2629_, v_b_2630_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2624_ = stack[1].m_obj;
lean_object* v_rules_2625_ = stack[2].m_obj;
lean_object* v_x_2626_ = stack[3].m_obj;
lean_object* v_a_2629_ = stack[6].m_obj;
lean_object* v_b_2630_ = stack[7].m_obj;
lean_object* v___y_2632_ = stack[9].m_obj;
lean_object* v___y_2633_ = stack[10].m_obj;
lean_object* v___y_2634_ = stack[11].m_obj;
lean_object* v___y_2635_ = stack[12].m_obj;
lean_object* v___y_2636_ = stack[13].m_obj;
lean_object* v___y_2637_ = stack[14].m_obj;
lean_object* v___y_2638_ = stack[15].m_obj;
lean_object* v___y_2639_ = stack[16].m_obj;
lean_object* v_res_2642_;
v_res_2642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(lean_box(0), v_upperBound_2624_, v_rules_2625_, v_x_2626_, lean_box(0), lean_box(0), v_a_2629_, v_b_2630_, lean_box(0), v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
stack->m_obj
 = v_res_2642_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_2643_ = _args[0];
lean_object* v_upperBound_2644_ = _args[1];
lean_object* v_rules_2645_ = _args[2];
lean_object* v_x_2646_ = _args[3];
lean_object* v_inst_2647_ = _args[4];
lean_object* v_R_2648_ = _args[5];
lean_object* v_a_2649_ = _args[6];
lean_object* v_b_2650_ = _args[7];
lean_object* v_c_2651_ = _args[8];
lean_object* v___y_2652_ = _args[9];
lean_object* v___y_2653_ = _args[10];
lean_object* v___y_2654_ = _args[11];
lean_object* v___y_2655_ = _args[12];
lean_object* v___y_2656_ = _args[13];
lean_object* v___y_2657_ = _args[14];
lean_object* v___y_2658_ = _args[15];
lean_object* v___y_2659_ = _args[16];
lean_object* v___y_2660_ = _args[17];
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(v_00_u03b1_2643_, v_upperBound_2644_, v_rules_2645_, v_x_2646_, v_inst_2647_, v_R_2648_, v_a_2649_, v_b_2650_, v_c_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_rules_2645_);
lean_dec(v_upperBound_2644_);
return v_res_2661_;
}
}
lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_x_2662_, lean_object* v_x_2663_, uint8_t v_symm_2664_, lean_object* v_term_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_box(v_symm_2664_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v___y_2667_);
lean_inc_ref(v___y_2666_);
v___x_2676_ = lean_apply_11(v_x_2662_, v___x_2675_, v_term_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, lean_box(0));
return v___x_2676_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_withRWRulesSeq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2662_ = stack[0].m_obj;
lean_object* v_x_2663_ = stack[1].m_obj;
uint8_t v_symm_2664_ = stack[2].m_num;
lean_object* v_term_2665_ = stack[3].m_obj;
lean_object* v___y_2666_ = stack[4].m_obj;
lean_object* v___y_2667_ = stack[5].m_obj;
lean_object* v___y_2668_ = stack[6].m_obj;
lean_object* v___y_2669_ = stack[7].m_obj;
lean_object* v___y_2670_ = stack[8].m_obj;
lean_object* v___y_2671_ = stack[9].m_obj;
lean_object* v___y_2672_ = stack[10].m_obj;
lean_object* v___y_2673_ = stack[11].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_x_2662_, v_x_2663_, v_symm_2664_, v_term_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
stack->m_obj
 = v_res_2677_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_x_2678_, lean_object* v_x_2679_, lean_object* v_symm_2680_, lean_object* v_term_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_symm_boxed_2691_; lean_object* v_res_2692_; 
v_symm_boxed_2691_ = lean_unbox(v_symm_2680_);
v_res_2692_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_x_2678_, v_x_2679_, v_symm_boxed_2691_, v_term_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2692_;
}
}
lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2693_, lean_object* v_rwRulesSeqStx_2694_, lean_object* v_x_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___f_2705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2705_, 0, v_x_2695_);
v___x_2706_ = lean_box(0);
v___x_2707_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2693_, v_rwRulesSeqStx_2694_, v___x_2706_, v___f_2705_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v___x_2707_, 0);
lean_dec(v_unused_2715_);
v___x_2709_ = v___x_2707_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v___x_2707_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2706_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
return v___x_2707_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_withRWRulesSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_2693_ = stack[0].m_obj;
lean_object* v_rwRulesSeqStx_2694_ = stack[1].m_obj;
lean_object* v_x_2695_ = stack[2].m_obj;
lean_object* v_a_2696_ = stack[3].m_obj;
lean_object* v_a_2697_ = stack[4].m_obj;
lean_object* v_a_2698_ = stack[5].m_obj;
lean_object* v_a_2699_ = stack[6].m_obj;
lean_object* v_a_2700_ = stack[7].m_obj;
lean_object* v_a_2701_ = stack[8].m_obj;
lean_object* v_a_2702_ = stack[9].m_obj;
lean_object* v_a_2703_ = stack[10].m_obj;
lean_object* v_res_2716_;
v_res_2716_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2693_, v_rwRulesSeqStx_2694_, v_x_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
stack->m_obj
 = v_res_2716_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2717_, lean_object* v_rwRulesSeqStx_2718_, lean_object* v_x_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2717_, v_rwRulesSeqStx_2718_, v_x_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_rwRulesSeqStx_2718_);
return v_res_2729_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
return v___x_2732_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2738_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2745_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2740_ = stack[1].m_obj;
lean_object* v___y_2741_ = stack[2].m_obj;
lean_object* v___y_2742_ = stack[3].m_obj;
lean_object* v___y_2743_ = stack[4].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_box(0), v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2753_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_ref_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v_ref_2760_ = lean_ctor_get(v___y_2757_, 2);
v___x_2761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_inc(v_ref_2760_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_ref_2760_);
lean_ctor_set(v___x_2766_, 1, v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 1);
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2754_ = stack[0].m_obj;
lean_object* v___y_2755_ = stack[1].m_obj;
lean_object* v___y_2756_ = stack[2].m_obj;
lean_object* v___y_2757_ = stack[3].m_obj;
lean_object* v___y_2758_ = stack[4].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2782_ = l_Lean_stringToMessageData(v___x_2781_);
return v___x_2782_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_2783_, lean_object* v_ctor_2784_, lean_object* v_args_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2852_ = lean_string_dec_eq(v_ctor_2784_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = lean_array_get_size(v_args_2785_);
v___x_2855_ = lean_unsigned_to_nat(4u);
v___x_2856_ = lean_nat_dec_eq(v___x_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
v___x_2857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2858_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2857_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
goto v___jp_2791_;
}
}
v___jp_2791_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_array_get_borrowed(v___x_2783_, v_args_2785_, v___x_2792_);
lean_inc(v___x_2793_);
v___x_2794_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2793_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_array_get_borrowed(v___x_2783_, v_args_2785_, v___x_2796_);
lean_inc(v___x_2797_);
v___x_2798_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2797_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = lean_unsigned_to_nat(2u);
v___x_2801_ = lean_array_get_borrowed(v___x_2783_, v_args_2785_, v___x_2800_);
lean_inc(v___x_2801_);
v___x_2802_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2801_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = lean_unsigned_to_nat(3u);
v___x_2805_ = lean_array_get_borrowed(v___x_2783_, v_args_2785_, v___x_2804_);
lean_inc(v___x_2805_);
v___x_2806_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2805_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2818_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; uint8_t v___x_2813_; uint8_t v___x_2814_; lean_object* v___x_2816_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2811_, 0, v_a_2803_);
v___x_2812_ = lean_unbox(v_a_2795_);
lean_dec(v_a_2795_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1, v___x_2812_);
v___x_2813_ = lean_unbox(v_a_2799_);
lean_dec(v_a_2799_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1 + 1, v___x_2813_);
v___x_2814_ = lean_unbox(v_a_2807_);
lean_dec(v_a_2807_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1 + 2, v___x_2814_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2811_);
v___x_2816_ = v___x_2809_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2799_);
lean_dec(v_a_2795_);
v_a_2819_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2806_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2806_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2799_);
lean_dec(v_a_2795_);
v_a_2827_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2802_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2802_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2795_);
v_a_2835_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2798_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2798_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2794_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2794_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2783_ = stack[0].m_obj;
lean_object* v_ctor_2784_ = stack[1].m_obj;
lean_object* v_args_2785_ = stack[2].m_obj;
lean_object* v___y_2786_ = stack[3].m_obj;
lean_object* v___y_2787_ = stack[4].m_obj;
lean_object* v___y_2788_ = stack[5].m_obj;
lean_object* v___y_2789_ = stack[6].m_obj;
lean_object* v_res_2867_;
v_res_2867_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v___x_2783_, v_ctor_2784_, v_args_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
stack->m_obj
 = v_res_2867_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_2868_, lean_object* v_ctor_2869_, lean_object* v_args_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v___x_2868_, v_ctor_2869_, v_args_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_args_2870_);
lean_dec_ref(v_ctor_2869_);
lean_dec_ref(v___x_2868_);
return v_res_2876_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___f_2878_; 
v___x_2877_ = l_Lean_instInhabitedExpr;
v___f_2878_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2878_, 0, v___x_2877_);
return v___f_2878_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___f_2893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0);
v___x_2894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2895_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2894_, v___f_2893_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2895_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2887_ = stack[0].m_obj;
lean_object* v_a_2888_ = stack[1].m_obj;
lean_object* v_a_2889_ = stack[2].m_obj;
lean_object* v_a_2890_ = stack[3].m_obj;
lean_object* v_a_2891_ = stack[4].m_obj;
lean_object* v_res_2896_;
v_res_2896_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
stack->m_obj
 = v_res_2896_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
return v_res_2903_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2904_, lean_object* v_msg_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2905_ = stack[1].m_obj;
lean_object* v___y_2906_ = stack[2].m_obj;
lean_object* v___y_2907_ = stack[3].m_obj;
lean_object* v___y_2908_ = stack[4].m_obj;
lean_object* v___y_2909_ = stack[5].m_obj;
lean_object* v_res_2912_;
v_res_2912_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_box(0), v_msg_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_msg_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2913_, v_msg_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_box(0);
v___x_2923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2924_ = l_Lean_Expr_const___override(v___x_2923_, v___x_2922_);
return v___x_2924_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___x_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2930_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_box(1);
v___x_2932_ = l_Lean_MessageData_ofFormat(v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2937_ = l_Lean_MessageData_ofFormat(v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
return v_x_2938_;
}
else
{
lean_object* v_head_2940_; lean_object* v_tail_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2963_; 
v_head_2940_ = lean_ctor_get(v_x_2939_, 0);
v_tail_2941_ = lean_ctor_get(v_x_2939_, 1);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2943_ = v_x_2939_;
v_isShared_2944_ = v_isSharedCheck_2963_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_tail_2941_);
lean_inc(v_head_2940_);
lean_dec(v_x_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2963_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_before_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2961_; 
v_before_2945_ = lean_ctor_get(v_head_2940_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_head_2940_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; 
v_unused_2962_ = lean_ctor_get(v_head_2940_, 1);
lean_dec(v_unused_2962_);
v___x_2947_ = v_head_2940_;
v_isShared_2948_ = v_isSharedCheck_2961_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_before_2945_);
lean_dec(v_head_2940_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2961_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 7);
lean_ctor_set(v___x_2947_, 1, v___x_2949_);
lean_ctor_set(v___x_2947_, 0, v_x_2938_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_x_2938_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 7);
lean_ctor_set(v___x_2943_, 1, v___x_2952_);
lean_ctor_set(v___x_2943_, 0, v___x_2951_);
v___x_2954_ = v___x_2943_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = l_Lean_MessageData_ofSyntax(v_before_2945_);
v___x_2956_ = l_Lean_indentD(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2954_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v_x_2938_ = v___x_2957_;
v_x_2939_ = v_tail_2941_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2964_, lean_object* v_opt_2965_){
_start:
{
lean_object* v_name_2966_; lean_object* v_defValue_2967_; lean_object* v_map_2968_; lean_object* v___x_2969_; 
v_name_2966_ = lean_ctor_get(v_opt_2965_, 0);
v_defValue_2967_ = lean_ctor_get(v_opt_2965_, 1);
v_map_2968_ = lean_ctor_get(v_opts_2964_, 0);
v___x_2969_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2968_, v_name_2966_);
if (lean_obj_tag(v___x_2969_) == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_unbox(v_defValue_2967_);
return v___x_2970_;
}
else
{
lean_object* v_val_2971_; 
v_val_2971_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___x_2969_, 1);
if (lean_obj_tag(v_val_2971_) == 1)
{
uint8_t v_v_2972_; 
v_v_2972_ = lean_ctor_get_uint8(v_val_2971_, 0);
lean_dec_ref_known(v_val_2971_, 0);
return v_v_2972_;
}
else
{
uint8_t v___x_2973_; 
lean_dec(v_val_2971_);
v___x_2973_ = lean_unbox(v_defValue_2967_);
return v___x_2973_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2964_ = stack[0].m_obj;
lean_object* v_opt_2965_ = stack[1].m_obj;
uint8_t v_res_2974_;
v_res_2974_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2964_, v_opt_2965_);
stack->m_num = v_res_2974_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2975_, lean_object* v_opt_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2975_, v_opt_2976_);
lean_dec_ref(v_opt_2976_);
lean_dec_ref(v_opts_2975_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2983_ = l_Lean_MessageData_ofFormat(v___x_2982_);
return v___x_2983_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2984_, lean_object* v_macroStack_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2986_);
v___x_2989_ = l_Lean_Elab_pp_macroStack;
v___x_2990_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v___x_2988_, v___x_2989_);
lean_dec_ref(v___x_2988_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
lean_dec(v_macroStack_2985_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_msgData_2984_);
return v___x_2991_;
}
else
{
if (lean_obj_tag(v_macroStack_2985_) == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_msgData_2984_);
return v___x_2992_;
}
else
{
lean_object* v_head_2993_; lean_object* v_after_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3009_; 
v_head_2993_ = lean_ctor_get(v_macroStack_2985_, 0);
lean_inc(v_head_2993_);
v_after_2994_ = lean_ctor_get(v_head_2993_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_head_2993_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v_head_2993_, 0);
lean_dec(v_unused_3010_);
v___x_2996_ = v_head_2993_;
v_isShared_2997_ = v_isSharedCheck_3009_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_after_2994_);
lean_dec(v_head_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3009_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 7);
lean_ctor_set(v___x_2996_, 1, v___x_2998_);
lean_ctor_set(v___x_2996_, 0, v_msgData_2984_);
v___x_3000_ = v___x_2996_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_msgData_2984_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_msgData_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3001_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Lean_MessageData_ofSyntax(v_after_2994_);
v___x_3004_ = l_Lean_indentD(v___x_3003_);
v_msgData_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3005_, 0, v___x_3002_);
lean_ctor_set(v_msgData_3005_, 1, v___x_3004_);
v___x_3006_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_3005_, v_macroStack_2985_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2984_ = stack[0].m_obj;
lean_object* v_macroStack_2985_ = stack[1].m_obj;
lean_object* v___y_2986_ = stack[2].m_obj;
lean_object* v_res_3011_;
v_res_3011_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2984_, v_macroStack_2985_, v___y_2986_);
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_3012_, lean_object* v_macroStack_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_3012_, v_macroStack_3013_, v___y_3014_);
lean_dec_ref(v___y_3014_);
return v_res_3016_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_ref_3025_; lean_object* v_macroStack_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3039_; 
v_ref_3025_ = lean_ctor_get(v___y_3022_, 2);
v_macroStack_3026_ = lean_ctor_get(v___y_3018_, 1);
v___x_3027_ = l_Lean_Elab_getBetterRef(v_ref_3025_, v_macroStack_3026_);
v___x_3028_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_3017_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
lean_inc(v_macroStack_3026_);
v___x_3030_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_3029_, v_macroStack_3026_, v___y_3022_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3027_);
lean_ctor_set(v___x_3035_, 1, v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set_tag(v___x_3033_, 1);
lean_ctor_set(v___x_3033_, 0, v___x_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3017_ = stack[0].m_obj;
lean_object* v___y_3018_ = stack[1].m_obj;
lean_object* v___y_3019_ = stack[2].m_obj;
lean_object* v___y_3020_ = stack[3].m_obj;
lean_object* v___y_3021_ = stack[4].m_obj;
lean_object* v___y_3022_ = stack[5].m_obj;
lean_object* v___y_3023_ = stack[6].m_obj;
lean_object* v_res_3040_;
v_res_3040_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
stack->m_obj
 = v_res_3040_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3049_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lean_Expr_hasMVar(v_e_3050_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_e_3050_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v_mctx_3056_; lean_object* v___x_3057_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; lean_object* v___x_3060_; lean_object* v_cache_3061_; lean_object* v_zetaDeltaFVarIds_3062_; lean_object* v_postponed_3063_; lean_object* v_diag_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3073_; 
v___x_3055_ = lean_st_ref_get(v___y_3051_);
v_mctx_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_ref(v_mctx_3056_);
lean_dec(v___x_3055_);
v___x_3057_ = l_Lean_instantiateMVarsCore(v_mctx_3056_, v_e_3050_);
v_fst_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_fst_3058_);
v_snd_3059_ = lean_ctor_get(v___x_3057_, 1);
lean_inc(v_snd_3059_);
lean_dec_ref(v___x_3057_);
v___x_3060_ = lean_st_ref_take(v___y_3051_);
v_cache_3061_ = lean_ctor_get(v___x_3060_, 1);
v_zetaDeltaFVarIds_3062_ = lean_ctor_get(v___x_3060_, 2);
v_postponed_3063_ = lean_ctor_get(v___x_3060_, 3);
v_diag_3064_ = lean_ctor_get(v___x_3060_, 4);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3060_, 0);
lean_dec(v_unused_3074_);
v___x_3066_ = v___x_3060_;
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_diag_3064_);
lean_inc(v_postponed_3063_);
lean_inc(v_zetaDeltaFVarIds_3062_);
lean_inc(v_cache_3061_);
lean_dec(v___x_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_snd_3059_);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_snd_3059_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_cache_3061_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_zetaDeltaFVarIds_3062_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_postponed_3063_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_diag_3064_);
v___x_3069_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_st_ref_put(v___y_3051_, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_fst_3058_);
return v___x_3071_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3050_ = stack[0].m_obj;
lean_object* v___y_3051_ = stack[1].m_obj;
lean_object* v_res_3075_;
v_res_3075_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_3050_, v___y_3051_);
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_3076_, v___y_3077_);
lean_dec(v___y_3077_);
return v_res_3079_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = l_Lean_Elab_abortTermExceptionId;
v___x_3082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
return v___x_3082_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3086_;
v_res_3086_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
stack->m_obj
 = v_res_3086_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_3088_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_box(0);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_3096_ = l_Lean_Expr_const___override(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3097_; lean_object* v_ty_x3f_3098_; 
v___x_3097_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3098_, 0, v___x_3097_);
return v_ty_x3f_3098_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_3101_ = l_Lean_stringToMessageData(v___x_3100_);
return v___x_3101_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_3103_ = l_Lean_MessageData_ofExpr(v___x_3102_);
return v___x_3103_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3108_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_3107_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_3112_ = l_Lean_stringToMessageData(v___x_3111_);
return v___x_3112_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_3115_ = l_Lean_stringToMessageData(v___x_3114_);
return v___x_3115_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_ty_x3f_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v_toCold_3130_; lean_object* v_currRecDepth_3131_; lean_object* v_ref_3132_; uint16_t v_optionFlags_3133_; uint8_t v_suppressElabErrors_3134_; uint8_t v_isRecordingDeps_3135_; uint8_t v___x_3136_; lean_object* v_ref_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_ty_x3f_3124_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_3125_ = 1;
v___x_3126_ = lean_box(0);
v___x_3127_ = lean_box(v___x_3125_);
v___x_3128_ = lean_box(v___x_3125_);
lean_inc(v_stx_3116_);
v___x_3129_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3129_, 0, v_stx_3116_);
lean_closure_set(v___x_3129_, 1, v_ty_x3f_3124_);
lean_closure_set(v___x_3129_, 2, v___x_3127_);
lean_closure_set(v___x_3129_, 3, v___x_3128_);
lean_closure_set(v___x_3129_, 4, v___x_3126_);
v_toCold_3130_ = lean_ctor_get(v_a_3121_, 0);
v_currRecDepth_3131_ = lean_ctor_get(v_a_3121_, 1);
v_ref_3132_ = lean_ctor_get(v_a_3121_, 2);
v_optionFlags_3133_ = lean_ctor_get_uint16(v_a_3121_, sizeof(void*)*3);
v_suppressElabErrors_3134_ = lean_ctor_get_uint8(v_a_3121_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3135_ = lean_ctor_get_uint8(v_a_3121_, sizeof(void*)*3 + 3);
v___x_3136_ = 1;
v_ref_3137_ = l_Lean_replaceRef(v_stx_3116_, v_ref_3132_);
lean_dec(v_stx_3116_);
lean_inc(v_currRecDepth_3131_);
lean_inc_ref(v_toCold_3130_);
v___x_3138_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3138_, 0, v_toCold_3130_);
lean_ctor_set(v___x_3138_, 1, v_currRecDepth_3131_);
lean_ctor_set(v___x_3138_, 2, v_ref_3137_);
lean_ctor_set_uint16(v___x_3138_, sizeof(void*)*3, v_optionFlags_3133_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*3 + 2, v_suppressElabErrors_3134_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*3 + 3, v_isRecordingDeps_3135_);
v___x_3139_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3129_, v___x_3136_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v___x_3138_, v_a_3122_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; lean_object* v_a_3142_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; uint8_t v___y_3153_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___x_3237_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3140_, v_a_3120_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref(v___x_3141_);
v___x_3237_ = l_Lean_Expr_hasSorry(v_a_3142_);
if (v___x_3237_ == 0)
{
v___y_3182_ = v_a_3117_;
v___y_3183_ = v_a_3118_;
v___y_3184_ = v_a_3119_;
v___y_3185_ = v_a_3120_;
v___y_3186_ = v___x_3138_;
v___y_3187_ = v_a_3122_;
goto v___jp_3181_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = l_Lean_Expr_hasSyntheticSorry(v_a_3142_);
if (v___x_3238_ == 0)
{
v___y_3219_ = v_a_3117_;
v___y_3220_ = v_a_3118_;
v___y_3221_ = v_a_3119_;
v___y_3222_ = v_a_3120_;
v___y_3223_ = v___x_3138_;
v___y_3224_ = v_a_3122_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3239_; lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_a_3142_);
lean_dec_ref_known(v___x_3138_, 3);
v___x_3239_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
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
v___jp_3143_:
{
if (v___y_3153_ == 0)
{
if (lean_obj_tag(v___y_3147_) == 0)
{
lean_dec_ref_known(v___y_3147_, 2);
lean_dec_ref(v___y_3145_);
lean_dec(v_a_3142_);
return v___y_3148_;
}
else
{
lean_object* v_id_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3167_; 
v_id_3154_ = lean_ctor_get(v___y_3147_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___y_3147_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___y_3147_, 1);
lean_dec(v_unused_3168_);
v___x_3156_ = v___y_3147_;
v_isShared_3157_ = v_isSharedCheck_3167_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_id_3154_);
lean_dec(v___y_3147_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3167_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
uint8_t v___x_3158_; 
v___x_3158_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3152_, v_id_3154_);
lean_dec(v_id_3154_);
if (v___x_3158_ == 0)
{
lean_del_object(v___x_3156_);
lean_dec_ref(v___y_3145_);
lean_dec(v_a_3142_);
return v___y_3148_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
lean_dec_ref(v___y_3148_);
v___x_3159_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_3160_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3161_ = l_Lean_indentExpr(v_a_3142_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 7);
lean_ctor_set(v___x_3156_, 1, v___x_3161_);
lean_ctor_set(v___x_3156_, 0, v___x_3160_);
v___x_3163_ = v___x_3156_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3159_);
v___x_3165_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3164_, v___y_3149_, v___y_3146_, v___y_3144_, v___y_3151_, v___y_3145_, v___y_3150_);
lean_dec_ref(v___y_3145_);
return v___x_3165_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3147_);
lean_dec_ref(v___y_3145_);
lean_dec(v_a_3142_);
return v___y_3148_;
}
}
v___jp_3169_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3142_);
v___x_3177_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_3142_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref(v___y_3174_);
lean_dec(v_a_3142_);
return v___x_3177_;
}
else
{
lean_object* v_a_3178_; uint8_t v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
v___x_3179_ = l_Lean_Exception_isInterrupt(v_a_3178_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
lean_inc(v_a_3178_);
v___x_3180_ = l_Lean_Exception_isRuntime(v_a_3178_);
v___y_3144_ = v___y_3172_;
v___y_3145_ = v___y_3174_;
v___y_3146_ = v___y_3171_;
v___y_3147_ = v_a_3178_;
v___y_3148_ = v___x_3177_;
v___y_3149_ = v___y_3170_;
v___y_3150_ = v___y_3175_;
v___y_3151_ = v___y_3173_;
v___y_3152_ = v___x_3176_;
v___y_3153_ = v___x_3180_;
goto v___jp_3143_;
}
else
{
v___y_3144_ = v___y_3172_;
v___y_3145_ = v___y_3174_;
v___y_3146_ = v___y_3171_;
v___y_3147_ = v_a_3178_;
v___y_3148_ = v___x_3177_;
v___y_3149_ = v___y_3170_;
v___y_3150_ = v___y_3175_;
v___y_3151_ = v___y_3173_;
v___y_3152_ = v___x_3176_;
v___y_3153_ = v___x_3179_;
goto v___jp_3143_;
}
}
}
v___jp_3181_:
{
lean_object* v___x_3188_; 
lean_inc(v_a_3142_);
v___x_3188_ = l_Lean_Meta_getMVars(v_a_3142_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3189_, v___x_3126_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v_a_3189_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; uint8_t v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = lean_unbox(v_a_3191_);
lean_dec(v_a_3191_);
if (v___x_3192_ == 0)
{
v___y_3170_ = v___y_3182_;
v___y_3171_ = v___y_3183_;
v___y_3172_ = v___y_3184_;
v___y_3173_ = v___y_3185_;
v___y_3174_ = v___y_3186_;
v___y_3175_ = v___y_3187_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3193_; lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___y_3186_);
lean_dec(v_a_3142_);
v___x_3193_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___y_3186_);
lean_dec(v_a_3142_);
v_a_3202_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3190_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3190_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v___y_3186_);
lean_dec(v_a_3142_);
v_a_3210_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3188_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3188_);
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
v___jp_3218_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v___x_3225_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3226_ = l_Lean_indentExpr(v_a_3142_);
v___x_3227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3225_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3227_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec_ref(v___y_3223_);
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
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref_known(v___x_3138_, 3);
v_a_3248_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3139_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3139_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3116_ = stack[0].m_obj;
lean_object* v_a_3117_ = stack[1].m_obj;
lean_object* v_a_3118_ = stack[2].m_obj;
lean_object* v_a_3119_ = stack[3].m_obj;
lean_object* v_a_3120_ = stack[4].m_obj;
lean_object* v_a_3121_ = stack[5].m_obj;
lean_object* v_a_3122_ = stack[6].m_obj;
lean_object* v_res_3256_;
v_res_3256_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
stack->m_obj
 = v_res_3256_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
return v_res_3265_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_toCold_3274_; lean_object* v_currRecDepth_3275_; lean_object* v_ref_3276_; uint16_t v_optionFlags_3277_; uint8_t v_suppressElabErrors_3278_; uint8_t v_isRecordingDeps_3279_; lean_object* v___x_3280_; lean_object* v_ref_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_toCold_3274_ = lean_ctor_get(v_a_3271_, 0);
v_currRecDepth_3275_ = lean_ctor_get(v_a_3271_, 1);
v_ref_3276_ = lean_ctor_get(v_a_3271_, 2);
v_optionFlags_3277_ = lean_ctor_get_uint16(v_a_3271_, sizeof(void*)*3);
v_suppressElabErrors_3278_ = lean_ctor_get_uint8(v_a_3271_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3279_ = lean_ctor_get_uint8(v_a_3271_, sizeof(void*)*3 + 3);
v___x_3280_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_3281_ = l_Lean_replaceRef(v_stx_3266_, v_ref_3276_);
lean_inc(v_currRecDepth_3275_);
lean_inc_ref(v_toCold_3274_);
v___x_3282_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3282_, 0, v_toCold_3274_);
lean_ctor_set(v___x_3282_, 1, v_currRecDepth_3275_);
lean_ctor_set(v___x_3282_, 2, v_ref_3281_);
lean_ctor_set_uint16(v___x_3282_, sizeof(void*)*3, v_optionFlags_3277_);
lean_ctor_set_uint8(v___x_3282_, sizeof(void*)*3 + 2, v_suppressElabErrors_3278_);
lean_ctor_set_uint8(v___x_3282_, sizeof(void*)*3 + 3, v_isRecordingDeps_3279_);
lean_inc(v_stx_3266_);
v___x_3283_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v___x_3282_, v_a_3272_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref_known(v___x_3282_, 3);
lean_dec(v_stx_3266_);
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_fst_3288_; lean_object* v___x_3290_; 
v_fst_3288_ = lean_ctor_get(v_a_3284_, 0);
lean_inc(v_fst_3288_);
lean_dec(v_a_3284_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v_fst_3288_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_fst_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3307_; 
v_a_3293_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3295_ = v___x_3283_;
v_isShared_3296_ = v_isSharedCheck_3307_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3283_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3307_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
lean_inc(v_a_3293_);
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
uint8_t v___y_3300_; uint8_t v___x_3304_; 
v___x_3304_ = l_Lean_Exception_isInterrupt(v_a_3293_);
if (v___x_3304_ == 0)
{
uint8_t v___x_3305_; 
lean_inc(v_a_3293_);
v___x_3305_ = l_Lean_Exception_isRuntime(v_a_3293_);
v___y_3300_ = v___x_3305_;
goto v___jp_3299_;
}
else
{
v___y_3300_ = v___x_3304_;
goto v___jp_3299_;
}
v___jp_3299_:
{
if (v___y_3300_ == 0)
{
if (lean_obj_tag(v_a_3293_) == 0)
{
lean_dec_ref_known(v_a_3293_, 2);
lean_dec_ref_known(v___x_3282_, 3);
lean_dec(v_stx_3266_);
return v___x_3298_;
}
else
{
lean_object* v_id_3301_; uint8_t v___x_3302_; 
v_id_3301_ = lean_ctor_get(v_a_3293_, 0);
lean_inc(v_id_3301_);
lean_dec_ref_known(v_a_3293_, 2);
v___x_3302_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3280_, v_id_3301_);
lean_dec(v_id_3301_);
if (v___x_3302_ == 0)
{
lean_dec_ref_known(v___x_3282_, 3);
lean_dec(v_stx_3266_);
return v___x_3298_;
}
else
{
lean_object* v___x_3303_; 
lean_dec_ref(v___x_3298_);
v___x_3303_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v___x_3282_, v_a_3272_);
lean_dec_ref_known(v___x_3282_, 3);
return v___x_3303_;
}
}
}
else
{
lean_dec(v_a_3293_);
lean_dec_ref_known(v___x_3282_, 3);
lean_dec(v_stx_3266_);
return v___x_3298_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3266_ = stack[0].m_obj;
lean_object* v_a_3267_ = stack[1].m_obj;
lean_object* v_a_3268_ = stack[2].m_obj;
lean_object* v_a_3269_ = stack[3].m_obj;
lean_object* v_a_3270_ = stack[4].m_obj;
lean_object* v_a_3271_ = stack[5].m_obj;
lean_object* v_a_3272_ = stack[6].m_obj;
lean_object* v_res_3308_;
v_res_3308_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
stack->m_obj
 = v_res_3308_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
return v_res_3317_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3325_ = l_Lean_Expr_const___override(v___x_3324_, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3326_; lean_object* v_ty_x3f_3327_; 
v___x_3326_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3327_, 0, v___x_3326_);
return v_ty_x3f_3327_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3329_ = l_Lean_MessageData_ofExpr(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3331_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___x_3330_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3334_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___x_3333_);
return v___x_3335_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_ty_x3f_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v_toCold_3350_; lean_object* v_currRecDepth_3351_; lean_object* v_ref_3352_; uint16_t v_optionFlags_3353_; uint8_t v_suppressElabErrors_3354_; uint8_t v_isRecordingDeps_3355_; uint8_t v___x_3356_; lean_object* v_ref_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_ty_x3f_3344_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3345_ = 1;
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_box(v___x_3345_);
v___x_3348_ = lean_box(v___x_3345_);
lean_inc(v_stx_3336_);
v___x_3349_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3349_, 0, v_stx_3336_);
lean_closure_set(v___x_3349_, 1, v_ty_x3f_3344_);
lean_closure_set(v___x_3349_, 2, v___x_3347_);
lean_closure_set(v___x_3349_, 3, v___x_3348_);
lean_closure_set(v___x_3349_, 4, v___x_3346_);
v_toCold_3350_ = lean_ctor_get(v_a_3341_, 0);
v_currRecDepth_3351_ = lean_ctor_get(v_a_3341_, 1);
v_ref_3352_ = lean_ctor_get(v_a_3341_, 2);
v_optionFlags_3353_ = lean_ctor_get_uint16(v_a_3341_, sizeof(void*)*3);
v_suppressElabErrors_3354_ = lean_ctor_get_uint8(v_a_3341_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3355_ = lean_ctor_get_uint8(v_a_3341_, sizeof(void*)*3 + 3);
v___x_3356_ = 1;
v_ref_3357_ = l_Lean_replaceRef(v_stx_3336_, v_ref_3352_);
lean_dec(v_stx_3336_);
lean_inc(v_currRecDepth_3351_);
lean_inc_ref(v_toCold_3350_);
v___x_3358_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3358_, 0, v_toCold_3350_);
lean_ctor_set(v___x_3358_, 1, v_currRecDepth_3351_);
lean_ctor_set(v___x_3358_, 2, v_ref_3357_);
lean_ctor_set_uint16(v___x_3358_, sizeof(void*)*3, v_optionFlags_3353_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*3 + 2, v_suppressElabErrors_3354_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*3 + 3, v_isRecordingDeps_3355_);
v___x_3359_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3349_, v___x_3356_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v___x_3358_, v_a_3342_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v_a_3362_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___x_3457_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3360_, v_a_3340_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3457_ = l_Lean_Expr_hasSorry(v_a_3362_);
if (v___x_3457_ == 0)
{
v___y_3402_ = v_a_3337_;
v___y_3403_ = v_a_3338_;
v___y_3404_ = v_a_3339_;
v___y_3405_ = v_a_3340_;
v___y_3406_ = v___x_3358_;
v___y_3407_ = v_a_3342_;
goto v___jp_3401_;
}
else
{
uint8_t v___x_3458_; 
v___x_3458_ = l_Lean_Expr_hasSyntheticSorry(v_a_3362_);
if (v___x_3458_ == 0)
{
v___y_3439_ = v_a_3337_;
v___y_3440_ = v_a_3338_;
v___y_3441_ = v_a_3339_;
v___y_3442_ = v_a_3340_;
v___y_3443_ = v___x_3358_;
v___y_3444_ = v_a_3342_;
goto v___jp_3438_;
}
else
{
lean_object* v___x_3459_; lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_a_3362_);
lean_dec_ref_known(v___x_3358_, 3);
v___x_3459_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
v___jp_3363_:
{
if (v___y_3373_ == 0)
{
if (lean_obj_tag(v___y_3372_) == 0)
{
lean_dec_ref_known(v___y_3372_, 2);
lean_dec_ref(v___y_3371_);
lean_dec(v_a_3362_);
return v___y_3364_;
}
else
{
lean_object* v_id_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3387_; 
v_id_3374_ = lean_ctor_get(v___y_3372_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___y_3372_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v___y_3372_, 1);
lean_dec(v_unused_3388_);
v___x_3376_ = v___y_3372_;
v_isShared_3377_ = v_isSharedCheck_3387_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_id_3374_);
lean_dec(v___y_3372_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3387_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
uint8_t v___x_3378_; 
v___x_3378_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3367_, v_id_3374_);
lean_dec(v_id_3374_);
if (v___x_3378_ == 0)
{
lean_del_object(v___x_3376_);
lean_dec_ref(v___y_3371_);
lean_dec(v_a_3362_);
return v___y_3364_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec_ref(v___y_3364_);
v___x_3379_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3380_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3381_ = l_Lean_indentExpr(v_a_3362_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 7);
lean_ctor_set(v___x_3376_, 1, v___x_3381_);
lean_ctor_set(v___x_3376_, 0, v___x_3380_);
v___x_3383_ = v___x_3376_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___x_3379_);
v___x_3385_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3384_, v___y_3366_, v___y_3368_, v___y_3370_, v___y_3365_, v___y_3371_, v___y_3369_);
lean_dec_ref(v___y_3371_);
return v___x_3385_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v_a_3362_);
return v___y_3364_;
}
}
v___jp_3389_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3362_);
v___x_3397_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3362_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_dec_ref(v___y_3394_);
lean_dec(v_a_3362_);
return v___x_3397_;
}
else
{
lean_object* v_a_3398_; uint8_t v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
v___x_3399_ = l_Lean_Exception_isInterrupt(v_a_3398_);
if (v___x_3399_ == 0)
{
uint8_t v___x_3400_; 
lean_inc(v_a_3398_);
v___x_3400_ = l_Lean_Exception_isRuntime(v_a_3398_);
v___y_3364_ = v___x_3397_;
v___y_3365_ = v___y_3393_;
v___y_3366_ = v___y_3390_;
v___y_3367_ = v___x_3396_;
v___y_3368_ = v___y_3391_;
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3392_;
v___y_3371_ = v___y_3394_;
v___y_3372_ = v_a_3398_;
v___y_3373_ = v___x_3400_;
goto v___jp_3363_;
}
else
{
v___y_3364_ = v___x_3397_;
v___y_3365_ = v___y_3393_;
v___y_3366_ = v___y_3390_;
v___y_3367_ = v___x_3396_;
v___y_3368_ = v___y_3391_;
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3392_;
v___y_3371_ = v___y_3394_;
v___y_3372_ = v_a_3398_;
v___y_3373_ = v___x_3399_;
goto v___jp_3363_;
}
}
}
v___jp_3401_:
{
lean_object* v___x_3408_; 
lean_inc(v_a_3362_);
v___x_3408_ = l_Lean_Meta_getMVars(v_a_3362_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3409_, v___x_3346_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v_a_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; uint8_t v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3412_ == 0)
{
v___y_3390_ = v___y_3402_;
v___y_3391_ = v___y_3403_;
v___y_3392_ = v___y_3404_;
v___y_3393_ = v___y_3405_;
v___y_3394_ = v___y_3406_;
v___y_3395_ = v___y_3407_;
goto v___jp_3389_;
}
else
{
lean_object* v___x_3413_; lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v___y_3406_);
lean_dec(v_a_3362_);
v___x_3413_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v___y_3406_);
lean_dec(v_a_3362_);
v_a_3422_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3410_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3410_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v___y_3406_);
lean_dec(v_a_3362_);
v_a_3430_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3408_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3408_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
v___jp_3438_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v___x_3445_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3446_ = l_Lean_indentExpr(v_a_3362_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3447_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec_ref(v___y_3443_);
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
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref_known(v___x_3358_, 3);
v_a_3468_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3359_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3359_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3336_ = stack[0].m_obj;
lean_object* v_a_3337_ = stack[1].m_obj;
lean_object* v_a_3338_ = stack[2].m_obj;
lean_object* v_a_3339_ = stack[3].m_obj;
lean_object* v_a_3340_ = stack[4].m_obj;
lean_object* v_a_3341_ = stack[5].m_obj;
lean_object* v_a_3342_ = stack[6].m_obj;
lean_object* v_res_3476_;
v_res_3476_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
stack->m_obj
 = v_res_3476_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3485_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v_toCold_3494_; lean_object* v_currRecDepth_3495_; lean_object* v_ref_3496_; uint16_t v_optionFlags_3497_; uint8_t v_suppressElabErrors_3498_; uint8_t v_isRecordingDeps_3499_; lean_object* v___x_3500_; lean_object* v_ref_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_toCold_3494_ = lean_ctor_get(v_a_3491_, 0);
v_currRecDepth_3495_ = lean_ctor_get(v_a_3491_, 1);
v_ref_3496_ = lean_ctor_get(v_a_3491_, 2);
v_optionFlags_3497_ = lean_ctor_get_uint16(v_a_3491_, sizeof(void*)*3);
v_suppressElabErrors_3498_ = lean_ctor_get_uint8(v_a_3491_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3499_ = lean_ctor_get_uint8(v_a_3491_, sizeof(void*)*3 + 3);
v___x_3500_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_3501_ = l_Lean_replaceRef(v_stx_3486_, v_ref_3496_);
lean_inc(v_currRecDepth_3495_);
lean_inc_ref(v_toCold_3494_);
v___x_3502_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3502_, 0, v_toCold_3494_);
lean_ctor_set(v___x_3502_, 1, v_currRecDepth_3495_);
lean_ctor_set(v___x_3502_, 2, v_ref_3501_);
lean_ctor_set_uint16(v___x_3502_, sizeof(void*)*3, v_optionFlags_3497_);
lean_ctor_set_uint8(v___x_3502_, sizeof(void*)*3 + 2, v_suppressElabErrors_3498_);
lean_ctor_set_uint8(v___x_3502_, sizeof(void*)*3 + 3, v_isRecordingDeps_3499_);
lean_inc(v_stx_3486_);
v___x_3503_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v___x_3502_, v_a_3492_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref_known(v___x_3502_, 3);
lean_dec(v_stx_3486_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_fst_3508_; lean_object* v___x_3510_; 
v_fst_3508_ = lean_ctor_get(v_a_3504_, 0);
lean_inc(v_fst_3508_);
lean_dec(v_a_3504_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v_fst_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_fst_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3527_; 
v_a_3513_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3515_ = v___x_3503_;
v_isShared_3516_ = v_isSharedCheck_3527_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3503_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3527_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
lean_inc(v_a_3513_);
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
uint8_t v___y_3520_; uint8_t v___x_3524_; 
v___x_3524_ = l_Lean_Exception_isInterrupt(v_a_3513_);
if (v___x_3524_ == 0)
{
uint8_t v___x_3525_; 
lean_inc(v_a_3513_);
v___x_3525_ = l_Lean_Exception_isRuntime(v_a_3513_);
v___y_3520_ = v___x_3525_;
goto v___jp_3519_;
}
else
{
v___y_3520_ = v___x_3524_;
goto v___jp_3519_;
}
v___jp_3519_:
{
if (v___y_3520_ == 0)
{
if (lean_obj_tag(v_a_3513_) == 0)
{
lean_dec_ref_known(v_a_3513_, 2);
lean_dec_ref_known(v___x_3502_, 3);
lean_dec(v_stx_3486_);
return v___x_3518_;
}
else
{
lean_object* v_id_3521_; uint8_t v___x_3522_; 
v_id_3521_ = lean_ctor_get(v_a_3513_, 0);
lean_inc(v_id_3521_);
lean_dec_ref_known(v_a_3513_, 2);
v___x_3522_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3500_, v_id_3521_);
lean_dec(v_id_3521_);
if (v___x_3522_ == 0)
{
lean_dec_ref_known(v___x_3502_, 3);
lean_dec(v_stx_3486_);
return v___x_3518_;
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v___x_3518_);
v___x_3523_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v___x_3502_, v_a_3492_);
lean_dec_ref_known(v___x_3502_, 3);
return v___x_3523_;
}
}
}
else
{
lean_dec(v_a_3513_);
lean_dec_ref_known(v___x_3502_, 3);
lean_dec(v_stx_3486_);
return v___x_3518_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3486_ = stack[0].m_obj;
lean_object* v_a_3487_ = stack[1].m_obj;
lean_object* v_a_3488_ = stack[2].m_obj;
lean_object* v_a_3489_ = stack[3].m_obj;
lean_object* v_a_3490_ = stack[4].m_obj;
lean_object* v_a_3491_ = stack[5].m_obj;
lean_object* v_a_3492_ = stack[6].m_obj;
lean_object* v_res_3528_;
v_res_3528_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
stack->m_obj
 = v_res_3528_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
return v_res_3537_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3539_ = l_Lean_MessageData_ofExpr(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3541_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
lean_ctor_set(v___x_3542_, 1, v___x_3540_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3544_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v___x_3543_);
return v___x_3545_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_ty_x3f_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v_toCold_3560_; lean_object* v_currRecDepth_3561_; lean_object* v_ref_3562_; uint16_t v_optionFlags_3563_; uint8_t v_suppressElabErrors_3564_; uint8_t v_isRecordingDeps_3565_; uint8_t v___x_3566_; lean_object* v_ref_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_ty_x3f_3554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3555_ = 1;
v___x_3556_ = lean_box(0);
v___x_3557_ = lean_box(v___x_3555_);
v___x_3558_ = lean_box(v___x_3555_);
lean_inc(v_stx_3546_);
v___x_3559_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3559_, 0, v_stx_3546_);
lean_closure_set(v___x_3559_, 1, v_ty_x3f_3554_);
lean_closure_set(v___x_3559_, 2, v___x_3557_);
lean_closure_set(v___x_3559_, 3, v___x_3558_);
lean_closure_set(v___x_3559_, 4, v___x_3556_);
v_toCold_3560_ = lean_ctor_get(v_a_3551_, 0);
v_currRecDepth_3561_ = lean_ctor_get(v_a_3551_, 1);
v_ref_3562_ = lean_ctor_get(v_a_3551_, 2);
v_optionFlags_3563_ = lean_ctor_get_uint16(v_a_3551_, sizeof(void*)*3);
v_suppressElabErrors_3564_ = lean_ctor_get_uint8(v_a_3551_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3565_ = lean_ctor_get_uint8(v_a_3551_, sizeof(void*)*3 + 3);
v___x_3566_ = 1;
v_ref_3567_ = l_Lean_replaceRef(v_stx_3546_, v_ref_3562_);
lean_dec(v_stx_3546_);
lean_inc(v_currRecDepth_3561_);
lean_inc_ref(v_toCold_3560_);
v___x_3568_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3568_, 0, v_toCold_3560_);
lean_ctor_set(v___x_3568_, 1, v_currRecDepth_3561_);
lean_ctor_set(v___x_3568_, 2, v_ref_3567_);
lean_ctor_set_uint16(v___x_3568_, sizeof(void*)*3, v_optionFlags_3563_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*3 + 2, v_suppressElabErrors_3564_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*3 + 3, v_isRecordingDeps_3565_);
v___x_3569_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3559_, v___x_3566_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v___x_3568_, v_a_3552_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; lean_object* v_a_3572_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; uint8_t v___x_3667_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
v___x_3571_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3570_, v_a_3550_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref(v___x_3571_);
v___x_3667_ = l_Lean_Expr_hasSorry(v_a_3572_);
if (v___x_3667_ == 0)
{
v___y_3612_ = v_a_3547_;
v___y_3613_ = v_a_3548_;
v___y_3614_ = v_a_3549_;
v___y_3615_ = v_a_3550_;
v___y_3616_ = v___x_3568_;
v___y_3617_ = v_a_3552_;
goto v___jp_3611_;
}
else
{
uint8_t v___x_3668_; 
v___x_3668_ = l_Lean_Expr_hasSyntheticSorry(v_a_3572_);
if (v___x_3668_ == 0)
{
v___y_3649_ = v_a_3547_;
v___y_3650_ = v_a_3548_;
v___y_3651_ = v_a_3549_;
v___y_3652_ = v_a_3550_;
v___y_3653_ = v___x_3568_;
v___y_3654_ = v_a_3552_;
goto v___jp_3648_;
}
else
{
lean_object* v___x_3669_; lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_a_3572_);
lean_dec_ref_known(v___x_3568_, 3);
v___x_3669_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
v___jp_3573_:
{
if (v___y_3583_ == 0)
{
if (lean_obj_tag(v___y_3577_) == 0)
{
lean_dec_ref_known(v___y_3577_, 2);
lean_dec_ref(v___y_3579_);
lean_dec(v_a_3572_);
return v___y_3574_;
}
else
{
lean_object* v_id_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3597_; 
v_id_3584_ = lean_ctor_get(v___y_3577_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___y_3577_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v___y_3577_, 1);
lean_dec(v_unused_3598_);
v___x_3586_ = v___y_3577_;
v_isShared_3587_ = v_isSharedCheck_3597_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_id_3584_);
lean_dec(v___y_3577_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3597_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
uint8_t v___x_3588_; 
v___x_3588_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3578_, v_id_3584_);
lean_dec(v_id_3584_);
if (v___x_3588_ == 0)
{
lean_del_object(v___x_3586_);
lean_dec_ref(v___y_3579_);
lean_dec(v_a_3572_);
return v___y_3574_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
lean_dec_ref(v___y_3574_);
v___x_3589_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3590_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3591_ = l_Lean_indentExpr(v_a_3572_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 7);
lean_ctor_set(v___x_3586_, 1, v___x_3591_);
lean_ctor_set(v___x_3586_, 0, v___x_3590_);
v___x_3593_ = v___x_3586_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v___x_3589_);
v___x_3595_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3594_, v___y_3580_, v___y_3575_, v___y_3581_, v___y_3582_, v___y_3579_, v___y_3576_);
lean_dec_ref(v___y_3579_);
return v___x_3595_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3579_);
lean_dec_ref(v___y_3577_);
lean_dec(v_a_3572_);
return v___y_3574_;
}
}
v___jp_3599_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3572_);
v___x_3607_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3572_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_dec_ref(v___y_3604_);
lean_dec(v_a_3572_);
return v___x_3607_;
}
else
{
lean_object* v_a_3608_; uint8_t v___x_3609_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
v___x_3609_ = l_Lean_Exception_isInterrupt(v_a_3608_);
if (v___x_3609_ == 0)
{
uint8_t v___x_3610_; 
lean_inc(v_a_3608_);
v___x_3610_ = l_Lean_Exception_isRuntime(v_a_3608_);
v___y_3574_ = v___x_3607_;
v___y_3575_ = v___y_3601_;
v___y_3576_ = v___y_3605_;
v___y_3577_ = v_a_3608_;
v___y_3578_ = v___x_3606_;
v___y_3579_ = v___y_3604_;
v___y_3580_ = v___y_3600_;
v___y_3581_ = v___y_3602_;
v___y_3582_ = v___y_3603_;
v___y_3583_ = v___x_3610_;
goto v___jp_3573_;
}
else
{
v___y_3574_ = v___x_3607_;
v___y_3575_ = v___y_3601_;
v___y_3576_ = v___y_3605_;
v___y_3577_ = v_a_3608_;
v___y_3578_ = v___x_3606_;
v___y_3579_ = v___y_3604_;
v___y_3580_ = v___y_3600_;
v___y_3581_ = v___y_3602_;
v___y_3582_ = v___y_3603_;
v___y_3583_ = v___x_3609_;
goto v___jp_3573_;
}
}
}
v___jp_3611_:
{
lean_object* v___x_3618_; 
lean_inc(v_a_3572_);
v___x_3618_ = l_Lean_Meta_getMVars(v_a_3572_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3619_, v___x_3556_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v_a_3619_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; uint8_t v___x_3622_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = lean_unbox(v_a_3621_);
lean_dec(v_a_3621_);
if (v___x_3622_ == 0)
{
v___y_3600_ = v___y_3612_;
v___y_3601_ = v___y_3613_;
v___y_3602_ = v___y_3614_;
v___y_3603_ = v___y_3615_;
v___y_3604_ = v___y_3616_;
v___y_3605_ = v___y_3617_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3623_; lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v___y_3616_);
lean_dec(v_a_3572_);
v___x_3623_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
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
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v___y_3616_);
lean_dec(v_a_3572_);
v_a_3632_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3620_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3620_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v___y_3616_);
lean_dec(v_a_3572_);
v_a_3640_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3618_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3618_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
v___jp_3648_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
v___x_3655_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3656_ = l_Lean_indentExpr(v_a_3572_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3657_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec_ref(v___y_3653_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref_known(v___x_3568_, 3);
v_a_3678_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3569_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3569_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3546_ = stack[0].m_obj;
lean_object* v_a_3547_ = stack[1].m_obj;
lean_object* v_a_3548_ = stack[2].m_obj;
lean_object* v_a_3549_ = stack[3].m_obj;
lean_object* v_a_3550_ = stack[4].m_obj;
lean_object* v_a_3551_ = stack[5].m_obj;
lean_object* v_a_3552_ = stack[6].m_obj;
lean_object* v_res_3686_;
v_res_3686_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
stack->m_obj
 = v_res_3686_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
return v_res_3695_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_box(0);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3703_ = l_Lean_Expr_const___override(v___x_3702_, v___x_3701_);
return v___x_3703_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3704_; lean_object* v_ty_x3f_3705_; 
v___x_3704_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3705_, 0, v___x_3704_);
return v_ty_x3f_3705_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3707_ = l_Lean_MessageData_ofExpr(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3709_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3708_);
return v___x_3710_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3712_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v___x_3711_);
return v___x_3713_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_ty_x3f_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v_toCold_3728_; lean_object* v_currRecDepth_3729_; lean_object* v_ref_3730_; uint16_t v_optionFlags_3731_; uint8_t v_suppressElabErrors_3732_; uint8_t v_isRecordingDeps_3733_; uint8_t v___x_3734_; lean_object* v_ref_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_ty_x3f_3722_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3723_ = 1;
v___x_3724_ = lean_box(0);
v___x_3725_ = lean_box(v___x_3723_);
v___x_3726_ = lean_box(v___x_3723_);
lean_inc(v_stx_3714_);
v___x_3727_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3727_, 0, v_stx_3714_);
lean_closure_set(v___x_3727_, 1, v_ty_x3f_3722_);
lean_closure_set(v___x_3727_, 2, v___x_3725_);
lean_closure_set(v___x_3727_, 3, v___x_3726_);
lean_closure_set(v___x_3727_, 4, v___x_3724_);
v_toCold_3728_ = lean_ctor_get(v_a_3719_, 0);
v_currRecDepth_3729_ = lean_ctor_get(v_a_3719_, 1);
v_ref_3730_ = lean_ctor_get(v_a_3719_, 2);
v_optionFlags_3731_ = lean_ctor_get_uint16(v_a_3719_, sizeof(void*)*3);
v_suppressElabErrors_3732_ = lean_ctor_get_uint8(v_a_3719_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3733_ = lean_ctor_get_uint8(v_a_3719_, sizeof(void*)*3 + 3);
v___x_3734_ = 1;
v_ref_3735_ = l_Lean_replaceRef(v_stx_3714_, v_ref_3730_);
lean_dec(v_stx_3714_);
lean_inc(v_currRecDepth_3729_);
lean_inc_ref(v_toCold_3728_);
v___x_3736_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3736_, 0, v_toCold_3728_);
lean_ctor_set(v___x_3736_, 1, v_currRecDepth_3729_);
lean_ctor_set(v___x_3736_, 2, v_ref_3735_);
lean_ctor_set_uint16(v___x_3736_, sizeof(void*)*3, v_optionFlags_3731_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*3 + 2, v_suppressElabErrors_3732_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*3 + 3, v_isRecordingDeps_3733_);
v___x_3737_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3727_, v___x_3734_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v___x_3736_, v_a_3720_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v_a_3740_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; uint8_t v___y_3751_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; uint8_t v___x_3835_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3738_, v_a_3718_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3739_);
v___x_3835_ = l_Lean_Expr_hasSorry(v_a_3740_);
if (v___x_3835_ == 0)
{
v___y_3780_ = v_a_3715_;
v___y_3781_ = v_a_3716_;
v___y_3782_ = v_a_3717_;
v___y_3783_ = v_a_3718_;
v___y_3784_ = v___x_3736_;
v___y_3785_ = v_a_3720_;
goto v___jp_3779_;
}
else
{
uint8_t v___x_3836_; 
v___x_3836_ = l_Lean_Expr_hasSyntheticSorry(v_a_3740_);
if (v___x_3836_ == 0)
{
v___y_3817_ = v_a_3715_;
v___y_3818_ = v_a_3716_;
v___y_3819_ = v_a_3717_;
v___y_3820_ = v_a_3718_;
v___y_3821_ = v___x_3736_;
v___y_3822_ = v_a_3720_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3837_; lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_a_3740_);
lean_dec_ref_known(v___x_3736_, 3);
v___x_3837_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
v___jp_3741_:
{
if (v___y_3751_ == 0)
{
if (lean_obj_tag(v___y_3746_) == 0)
{
lean_dec_ref_known(v___y_3746_, 2);
lean_dec_ref(v___y_3742_);
lean_dec(v_a_3740_);
return v___y_3749_;
}
else
{
lean_object* v_id_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3765_; 
v_id_3752_ = lean_ctor_get(v___y_3746_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___y_3746_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v___y_3746_, 1);
lean_dec(v_unused_3766_);
v___x_3754_ = v___y_3746_;
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_id_3752_);
lean_dec(v___y_3746_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
uint8_t v___x_3756_; 
v___x_3756_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3744_, v_id_3752_);
lean_dec(v_id_3752_);
if (v___x_3756_ == 0)
{
lean_del_object(v___x_3754_);
lean_dec_ref(v___y_3742_);
lean_dec(v_a_3740_);
return v___y_3749_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_dec_ref(v___y_3749_);
v___x_3757_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3758_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3759_ = l_Lean_indentExpr(v_a_3740_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set_tag(v___x_3754_, 7);
lean_ctor_set(v___x_3754_, 1, v___x_3759_);
lean_ctor_set(v___x_3754_, 0, v___x_3758_);
v___x_3761_ = v___x_3754_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3757_);
v___x_3763_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3762_, v___y_3748_, v___y_3745_, v___y_3747_, v___y_3750_, v___y_3742_, v___y_3743_);
lean_dec_ref(v___y_3742_);
return v___x_3763_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3746_);
lean_dec_ref(v___y_3742_);
lean_dec(v_a_3740_);
return v___y_3749_;
}
}
v___jp_3767_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3740_);
v___x_3775_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3740_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_dec_ref(v___y_3772_);
lean_dec(v_a_3740_);
return v___x_3775_;
}
else
{
lean_object* v_a_3776_; uint8_t v___x_3777_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
v___x_3777_ = l_Lean_Exception_isInterrupt(v_a_3776_);
if (v___x_3777_ == 0)
{
uint8_t v___x_3778_; 
lean_inc(v_a_3776_);
v___x_3778_ = l_Lean_Exception_isRuntime(v_a_3776_);
v___y_3742_ = v___y_3772_;
v___y_3743_ = v___y_3773_;
v___y_3744_ = v___x_3774_;
v___y_3745_ = v___y_3769_;
v___y_3746_ = v_a_3776_;
v___y_3747_ = v___y_3770_;
v___y_3748_ = v___y_3768_;
v___y_3749_ = v___x_3775_;
v___y_3750_ = v___y_3771_;
v___y_3751_ = v___x_3778_;
goto v___jp_3741_;
}
else
{
v___y_3742_ = v___y_3772_;
v___y_3743_ = v___y_3773_;
v___y_3744_ = v___x_3774_;
v___y_3745_ = v___y_3769_;
v___y_3746_ = v_a_3776_;
v___y_3747_ = v___y_3770_;
v___y_3748_ = v___y_3768_;
v___y_3749_ = v___x_3775_;
v___y_3750_ = v___y_3771_;
v___y_3751_ = v___x_3777_;
goto v___jp_3741_;
}
}
}
v___jp_3779_:
{
lean_object* v___x_3786_; 
lean_inc(v_a_3740_);
v___x_3786_ = l_Lean_Meta_getMVars(v_a_3740_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v___x_3788_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3787_, v___x_3724_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v_a_3787_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; uint8_t v___x_3790_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___x_3790_ = lean_unbox(v_a_3789_);
lean_dec(v_a_3789_);
if (v___x_3790_ == 0)
{
v___y_3768_ = v___y_3780_;
v___y_3769_ = v___y_3781_;
v___y_3770_ = v___y_3782_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___y_3784_;
v___y_3773_ = v___y_3785_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3791_; lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v___y_3784_);
lean_dec(v_a_3740_);
v___x_3791_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3791_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v___y_3784_);
lean_dec(v_a_3740_);
v_a_3800_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3788_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3788_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___y_3784_);
lean_dec(v_a_3740_);
v_a_3808_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3786_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3786_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
v___jp_3816_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v___x_3823_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3824_ = l_Lean_indentExpr(v_a_3740_);
v___x_3825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3823_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3825_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec_ref(v___y_3821_);
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3826_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref_known(v___x_3736_, 3);
v_a_3846_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3737_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3737_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3714_ = stack[0].m_obj;
lean_object* v_a_3715_ = stack[1].m_obj;
lean_object* v_a_3716_ = stack[2].m_obj;
lean_object* v_a_3717_ = stack[3].m_obj;
lean_object* v_a_3718_ = stack[4].m_obj;
lean_object* v_a_3719_ = stack[5].m_obj;
lean_object* v_a_3720_ = stack[6].m_obj;
lean_object* v_res_3854_;
v_res_3854_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
stack->m_obj
 = v_res_3854_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
return v_res_3863_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_toCold_3872_; lean_object* v_currRecDepth_3873_; lean_object* v_ref_3874_; uint16_t v_optionFlags_3875_; uint8_t v_suppressElabErrors_3876_; uint8_t v_isRecordingDeps_3877_; lean_object* v___x_3878_; lean_object* v_ref_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_toCold_3872_ = lean_ctor_get(v_a_3869_, 0);
v_currRecDepth_3873_ = lean_ctor_get(v_a_3869_, 1);
v_ref_3874_ = lean_ctor_get(v_a_3869_, 2);
v_optionFlags_3875_ = lean_ctor_get_uint16(v_a_3869_, sizeof(void*)*3);
v_suppressElabErrors_3876_ = lean_ctor_get_uint8(v_a_3869_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3877_ = lean_ctor_get_uint8(v_a_3869_, sizeof(void*)*3 + 3);
v___x_3878_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_3879_ = l_Lean_replaceRef(v_stx_3864_, v_ref_3874_);
lean_inc(v_currRecDepth_3873_);
lean_inc_ref(v_toCold_3872_);
v___x_3880_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3880_, 0, v_toCold_3872_);
lean_ctor_set(v___x_3880_, 1, v_currRecDepth_3873_);
lean_ctor_set(v___x_3880_, 2, v_ref_3879_);
lean_ctor_set_uint16(v___x_3880_, sizeof(void*)*3, v_optionFlags_3875_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*3 + 2, v_suppressElabErrors_3876_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*3 + 3, v_isRecordingDeps_3877_);
lean_inc(v_stx_3864_);
v___x_3881_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v___x_3880_, v_a_3870_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref_known(v___x_3880_, 3);
lean_dec(v_stx_3864_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_fst_3886_; lean_object* v___x_3888_; 
v_fst_3886_ = lean_ctor_get(v_a_3882_, 0);
lean_inc(v_fst_3886_);
lean_dec(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v_fst_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_fst_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3905_; 
v_a_3891_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3893_ = v___x_3881_;
v_isShared_3894_ = v_isSharedCheck_3905_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3881_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3905_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
lean_inc(v_a_3891_);
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
uint8_t v___y_3898_; uint8_t v___x_3902_; 
v___x_3902_ = l_Lean_Exception_isInterrupt(v_a_3891_);
if (v___x_3902_ == 0)
{
uint8_t v___x_3903_; 
lean_inc(v_a_3891_);
v___x_3903_ = l_Lean_Exception_isRuntime(v_a_3891_);
v___y_3898_ = v___x_3903_;
goto v___jp_3897_;
}
else
{
v___y_3898_ = v___x_3902_;
goto v___jp_3897_;
}
v___jp_3897_:
{
if (v___y_3898_ == 0)
{
if (lean_obj_tag(v_a_3891_) == 0)
{
lean_dec_ref_known(v_a_3891_, 2);
lean_dec_ref_known(v___x_3880_, 3);
lean_dec(v_stx_3864_);
return v___x_3896_;
}
else
{
lean_object* v_id_3899_; uint8_t v___x_3900_; 
v_id_3899_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_id_3899_);
lean_dec_ref_known(v_a_3891_, 2);
v___x_3900_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3878_, v_id_3899_);
lean_dec(v_id_3899_);
if (v___x_3900_ == 0)
{
lean_dec_ref_known(v___x_3880_, 3);
lean_dec(v_stx_3864_);
return v___x_3896_;
}
else
{
lean_object* v___x_3901_; 
lean_dec_ref(v___x_3896_);
v___x_3901_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v___x_3880_, v_a_3870_);
lean_dec_ref_known(v___x_3880_, 3);
return v___x_3901_;
}
}
}
else
{
lean_dec(v_a_3891_);
lean_dec_ref_known(v___x_3880_, 3);
lean_dec(v_stx_3864_);
return v___x_3896_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3864_ = stack[0].m_obj;
lean_object* v_a_3865_ = stack[1].m_obj;
lean_object* v_a_3866_ = stack[2].m_obj;
lean_object* v_a_3867_ = stack[3].m_obj;
lean_object* v_a_3868_ = stack[4].m_obj;
lean_object* v_a_3869_ = stack[5].m_obj;
lean_object* v_a_3870_ = stack[6].m_obj;
lean_object* v_res_3906_;
v_res_3906_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
stack->m_obj
 = v_res_3906_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
return v_res_3915_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3947_, lean_object* v_item_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_item_3957_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3961_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3948_, v___x_3960_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3961_) == 0)
{
uint8_t v___x_3962_; 
lean_dec_ref_known(v___x_3961_, 1);
v___x_3962_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3948_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3963_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3948_);
lean_inc_ref(v_item_3948_);
v___x_3964_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3948_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3966_ = lean_string_dec_eq(v___x_3963_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3968_ = lean_string_dec_eq(v___x_3963_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3970_ = lean_string_dec_eq(v___x_3963_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3972_ = lean_string_dec_eq(v___x_3963_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3974_ = lean_string_dec_eq(v___x_3963_, v___x_3973_);
lean_dec_ref(v___x_3963_);
if (v___x_3974_ == 0)
{
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3976_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3948_, v___x_3975_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3976_) == 0)
{
uint8_t v___x_3977_; 
lean_dec_ref_known(v___x_3976_, 1);
v___x_3977_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3964_);
if (v___x_3977_ == 0)
{
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3978_; 
lean_dec_ref(v___x_3964_);
lean_inc_ref(v_item_3948_);
v___x_3978_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_value_3979_; lean_object* v___x_3980_; 
lean_dec_ref_known(v___x_3978_, 1);
v_value_3979_ = lean_ctor_get(v_item_3948_, 2);
lean_inc(v_value_3979_);
lean_dec_ref(v_item_3948_);
v___x_3980_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3979_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3999_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3999_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3999_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
uint8_t v_offsetCnstrs_3985_; lean_object* v_occs_3986_; uint8_t v_newGoals_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3998_; 
v_offsetCnstrs_3985_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 1);
v_occs_3986_ = lean_ctor_get(v_config_3947_, 0);
v_newGoals_3987_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 2);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_config_3947_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3989_ = v_config_3947_;
v_isShared_3990_ = v_isSharedCheck_3998_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_occs_3986_);
lean_dec(v_config_3947_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3998_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_occs_3986_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
uint8_t v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unbox(v_a_3981_);
lean_dec(v_a_3981_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*1, v___x_3993_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*1 + 1, v_offsetCnstrs_3985_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*1 + 2, v_newGoals_3987_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3992_);
v___x_3995_ = v___x_3983_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3992_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v_config_3947_);
v_a_4000_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3980_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3980_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4008_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3978_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3978_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4016_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3976_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3976_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_dec_ref(v___x_3963_);
v___x_4024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_4025_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3948_, v___x_4024_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4025_) == 0)
{
uint8_t v___x_4026_; 
lean_dec_ref_known(v___x_4025_, 1);
v___x_4026_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3964_);
if (v___x_4026_ == 0)
{
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4027_; 
lean_dec_ref(v___x_3964_);
v___x_4027_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4046_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4046_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4046_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
uint8_t v_transparency_4032_; lean_object* v_occs_4033_; uint8_t v_newGoals_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4045_; 
v_transparency_4032_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1);
v_occs_4033_ = lean_ctor_get(v_config_3947_, 0);
v_newGoals_4034_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 2);
v_isSharedCheck_4045_ = !lean_is_exclusive(v_config_3947_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4036_ = v_config_3947_;
v_isShared_4037_ = v_isSharedCheck_4045_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_occs_4033_);
lean_dec(v_config_3947_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4045_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_occs_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4044_, sizeof(void*)*1, v_transparency_4032_);
v___x_4039_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
uint8_t v___x_4040_; lean_object* v___x_4042_; 
v___x_4040_ = lean_unbox(v_a_4028_);
lean_dec(v_a_4028_);
lean_ctor_set_uint8(v___x_4039_, sizeof(void*)*1 + 1, v___x_4040_);
lean_ctor_set_uint8(v___x_4039_, sizeof(void*)*1 + 2, v_newGoals_4034_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v___x_4039_);
v___x_4042_ = v___x_4030_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4039_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec_ref(v_config_3947_);
v_a_4047_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4027_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4027_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4055_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4025_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4025_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
lean_dec_ref(v___x_3963_);
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_4064_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3948_, v___x_4063_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4064_) == 0)
{
uint8_t v___x_4065_; 
lean_dec_ref_known(v___x_4064_, 1);
v___x_4065_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3964_);
if (v___x_4065_ == 0)
{
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4066_; 
lean_dec_ref(v___x_3964_);
lean_inc_ref(v_item_3948_);
v___x_4066_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_value_4067_; lean_object* v___x_4068_; 
lean_dec_ref_known(v___x_4066_, 1);
v_value_4067_ = lean_ctor_get(v_item_3948_, 2);
lean_inc(v_value_4067_);
lean_dec_ref(v_item_3948_);
v___x_4068_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_4067_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4087_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4087_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4087_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
uint8_t v_transparency_4073_; uint8_t v_offsetCnstrs_4074_; uint8_t v_newGoals_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4085_; 
v_transparency_4073_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1);
v_offsetCnstrs_4074_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 1);
v_newGoals_4075_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 2);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_config_3947_);
if (v_isSharedCheck_4085_ == 0)
{
lean_object* v_unused_4086_; 
v_unused_4086_ = lean_ctor_get(v_config_3947_, 0);
lean_dec(v_unused_4086_);
v___x_4077_ = v_config_3947_;
v_isShared_4078_ = v_isSharedCheck_4085_;
goto v_resetjp_4076_;
}
else
{
lean_dec(v_config_3947_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4085_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v_a_4069_);
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4069_);
lean_ctor_set_uint8(v_reuseFailAlloc_4084_, sizeof(void*)*1, v_transparency_4073_);
lean_ctor_set_uint8(v_reuseFailAlloc_4084_, sizeof(void*)*1 + 1, v_offsetCnstrs_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4084_, sizeof(void*)*1 + 2, v_newGoals_4075_);
v___x_4080_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4082_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v___x_4080_);
v___x_4082_ = v___x_4071_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v_config_3947_);
v_a_4088_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4068_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4068_);
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
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4096_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4066_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4066_);
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
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4104_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4064_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4064_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec_ref(v___x_3963_);
v___x_4112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_4113_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3948_, v___x_4112_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4113_) == 0)
{
uint8_t v___x_4114_; 
lean_dec_ref_known(v___x_4113_, 1);
v___x_4114_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3964_);
if (v___x_4114_ == 0)
{
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4115_; 
lean_dec_ref(v___x_3964_);
lean_inc_ref(v_item_3948_);
v___x_4115_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_value_4116_; lean_object* v___x_4117_; 
lean_dec_ref_known(v___x_4115_, 1);
v_value_4116_ = lean_ctor_get(v_item_3948_, 2);
lean_inc(v_value_4116_);
lean_dec_ref(v_item_3948_);
v___x_4117_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_4116_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4136_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4136_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4136_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
uint8_t v_transparency_4122_; uint8_t v_offsetCnstrs_4123_; lean_object* v_occs_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4135_; 
v_transparency_4122_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1);
v_offsetCnstrs_4123_ = lean_ctor_get_uint8(v_config_3947_, sizeof(void*)*1 + 1);
v_occs_4124_ = lean_ctor_get(v_config_3947_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_config_3947_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4126_ = v_config_3947_;
v_isShared_4127_ = v_isSharedCheck_4135_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_occs_4124_);
lean_dec(v_config_3947_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4135_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_occs_4124_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*1, v_transparency_4122_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*1 + 1, v_offsetCnstrs_4123_);
v___x_4129_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
uint8_t v___x_4130_; lean_object* v___x_4132_; 
v___x_4130_ = lean_unbox(v_a_4118_);
lean_dec(v_a_4118_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*1 + 2, v___x_4130_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4129_);
v___x_4132_ = v___x_4120_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4129_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v_config_3947_);
v_a_4137_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4117_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4117_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4145_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4115_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4115_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4153_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4113_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4113_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
else
{
uint8_t v___x_4161_; 
lean_dec_ref(v___x_3963_);
lean_dec_ref(v_config_3947_);
v___x_4161_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3964_);
if (v___x_4161_ == 0)
{
lean_dec_ref(v_item_3948_);
v_item_3957_ = v___x_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v_value_4162_; lean_object* v___x_4163_; 
lean_dec_ref(v___x_3964_);
v_value_4162_ = lean_ctor_get(v_item_3948_, 2);
lean_inc(v_value_4162_);
lean_dec_ref(v_item_3948_);
v___x_4163_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_4162_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_4163_;
}
}
}
else
{
lean_dec_ref(v_config_3947_);
v_item_3957_ = v_item_3948_;
goto v___jp_3956_;
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_item_3948_);
lean_dec_ref(v_config_3947_);
v_a_4164_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_3961_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_3961_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
v___jp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3959_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3957_, v___x_3958_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3959_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_3947_ = stack[0].m_obj;
lean_object* v_item_3948_ = stack[1].m_obj;
lean_object* v___y_3949_ = stack[2].m_obj;
lean_object* v___y_3950_ = stack[3].m_obj;
lean_object* v___y_3951_ = stack[4].m_obj;
lean_object* v___y_3952_ = stack[5].m_obj;
lean_object* v___y_3953_ = stack[6].m_obj;
lean_object* v___y_3954_ = stack[7].m_obj;
lean_object* v_res_4172_;
v_res_4172_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_3947_, v_item_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
stack->m_obj
 = v_res_4172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_4173_, lean_object* v_item_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_4173_, v_item_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4182_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_4185_, v___y_4189_);
return v___x_4193_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4185_ = stack[0].m_obj;
lean_object* v___y_4186_ = stack[1].m_obj;
lean_object* v___y_4187_ = stack[2].m_obj;
lean_object* v___y_4188_ = stack[3].m_obj;
lean_object* v___y_4189_ = stack[4].m_obj;
lean_object* v___y_4190_ = stack[5].m_obj;
lean_object* v___y_4191_ = stack[6].m_obj;
lean_object* v_res_4194_;
v_res_4194_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
stack->m_obj
 = v_res_4194_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
return v_res_4203_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_4212_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4205_ = stack[1].m_obj;
lean_object* v___y_4206_ = stack[2].m_obj;
lean_object* v___y_4207_ = stack[3].m_obj;
lean_object* v___y_4208_ = stack[4].m_obj;
lean_object* v___y_4209_ = stack[5].m_obj;
lean_object* v___y_4210_ = stack[6].m_obj;
lean_object* v_res_4213_;
v_res_4213_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_box(0), v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
stack->m_obj
 = v_res_4213_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
return v_res_4222_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4223_, lean_object* v_msg_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4224_ = stack[1].m_obj;
lean_object* v___y_4225_ = stack[2].m_obj;
lean_object* v___y_4226_ = stack[3].m_obj;
lean_object* v___y_4227_ = stack[4].m_obj;
lean_object* v___y_4228_ = stack[5].m_obj;
lean_object* v___y_4229_ = stack[6].m_obj;
lean_object* v___y_4230_ = stack[7].m_obj;
lean_object* v_res_4233_;
v_res_4233_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_box(0), v_msg_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
stack->m_obj
 = v_res_4233_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4234_, lean_object* v_msg_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4234_, v_msg_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
return v_res_4243_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4244_, lean_object* v_macroStack_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4244_, v_macroStack_4245_, v___y_4250_);
return v___x_4253_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4244_ = stack[0].m_obj;
lean_object* v_macroStack_4245_ = stack[1].m_obj;
lean_object* v___y_4246_ = stack[2].m_obj;
lean_object* v___y_4247_ = stack[3].m_obj;
lean_object* v___y_4248_ = stack[4].m_obj;
lean_object* v___y_4249_ = stack[5].m_obj;
lean_object* v___y_4250_ = stack[6].m_obj;
lean_object* v___y_4251_ = stack[7].m_obj;
lean_object* v_res_4254_;
v_res_4254_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4244_, v_macroStack_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
stack->m_obj
 = v_res_4254_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4255_, lean_object* v_macroStack_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4255_, v_macroStack_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
return v_res_4264_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4265_ = lean_box(0);
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4267_ = l_Lean_mkConst(v___x_4266_, v___x_4265_);
return v___x_4267_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4270_, lean_object* v_cfgItem_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4280_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4270_, v_cfgItem_4271_, v___x_4279_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
return v___x_4280_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4270_ = stack[0].m_obj;
lean_object* v_cfgItem_4271_ = stack[1].m_obj;
lean_object* v___y_4272_ = stack[2].m_obj;
lean_object* v___y_4273_ = stack[3].m_obj;
lean_object* v___y_4274_ = stack[4].m_obj;
lean_object* v___y_4275_ = stack[5].m_obj;
lean_object* v___y_4276_ = stack[6].m_obj;
lean_object* v___y_4277_ = stack[7].m_obj;
lean_object* v_res_4281_;
v_res_4281_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4270_, v_cfgItem_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
stack->m_obj
 = v_res_4281_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4282_, lean_object* v_cfgItem_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4282_, v_cfgItem_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v_cfgItem_4283_);
return v_res_4291_;
}
}
lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4293_, lean_object* v_init_4294_, uint8_t v_logExceptions_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v_onErr_4300_; lean_object* v_eval_4301_; 
v_onErr_4300_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4295_ == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4301_, v_init_4294_, v_cfg_4293_, v_onErr_4300_, v_logExceptions_4295_, v_a_4297_, v_a_4298_);
return v___x_4302_;
}
else
{
uint8_t v_recover_4303_; lean_object* v___x_4304_; 
v_recover_4303_ = lean_ctor_get_uint8(v_a_4296_, sizeof(void*)*1);
v___x_4304_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4301_, v_init_4294_, v_cfg_4293_, v_onErr_4300_, v_recover_4303_, v_a_4297_, v_a_4298_);
return v___x_4304_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabRewriteConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4293_ = stack[0].m_obj;
lean_object* v_init_4294_ = stack[1].m_obj;
uint8_t v_logExceptions_4295_ = stack[2].m_num;
lean_object* v_a_4296_ = stack[3].m_obj;
lean_object* v_a_4297_ = stack[4].m_obj;
lean_object* v_a_4298_ = stack[5].m_obj;
lean_object* v_res_4305_;
v_res_4305_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4293_, v_init_4294_, v_logExceptions_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
stack->m_obj
 = v_res_4305_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4306_, lean_object* v_init_4307_, lean_object* v_logExceptions_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
uint8_t v_logExceptions_boxed_4313_; lean_object* v_res_4314_; 
v_logExceptions_boxed_4313_ = lean_unbox(v_logExceptions_4308_);
v_res_4314_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4306_, v_init_4307_, v_logExceptions_boxed_4313_, v_a_4309_, v_a_4310_, v_a_4311_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec_ref(v_a_4309_);
return v_res_4314_;
}
}
lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4315_, lean_object* v_init_4316_, uint8_t v_logExceptions_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4315_, v_init_4316_, v_logExceptions_4317_, v_a_4318_, v_a_4324_, v_a_4325_);
return v___x_4327_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabRewriteConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4315_ = stack[0].m_obj;
lean_object* v_init_4316_ = stack[1].m_obj;
uint8_t v_logExceptions_4317_ = stack[2].m_num;
lean_object* v_a_4318_ = stack[3].m_obj;
lean_object* v_a_4319_ = stack[4].m_obj;
lean_object* v_a_4320_ = stack[5].m_obj;
lean_object* v_a_4321_ = stack[6].m_obj;
lean_object* v_a_4322_ = stack[7].m_obj;
lean_object* v_a_4323_ = stack[8].m_obj;
lean_object* v_a_4324_ = stack[9].m_obj;
lean_object* v_a_4325_ = stack[10].m_obj;
lean_object* v_res_4328_;
v_res_4328_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4315_, v_init_4316_, v_logExceptions_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
stack->m_obj
 = v_res_4328_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4329_, lean_object* v_init_4330_, lean_object* v_logExceptions_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
uint8_t v_logExceptions_boxed_4341_; lean_object* v_res_4342_; 
v_logExceptions_boxed_4341_ = lean_unbox(v_logExceptions_4331_);
v_res_4342_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4329_, v_init_4330_, v_logExceptions_boxed_4341_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
return v_res_4342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4350_ = l_Lean_MessageData_ofFormat(v___x_4349_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4364_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4365_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4363_, v_x_4353_, v___x_4364_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4365_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRewriteSeq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4353_ = stack[0].m_obj;
lean_object* v___y_4354_ = stack[1].m_obj;
lean_object* v___y_4355_ = stack[2].m_obj;
lean_object* v___y_4356_ = stack[3].m_obj;
lean_object* v___y_4357_ = stack[4].m_obj;
lean_object* v___y_4358_ = stack[5].m_obj;
lean_object* v___y_4359_ = stack[6].m_obj;
lean_object* v___y_4360_ = stack[7].m_obj;
lean_object* v___y_4361_ = stack[8].m_obj;
lean_object* v_res_4366_;
v_res_4366_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
stack->m_obj
 = v_res_4366_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4377_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4378_, uint8_t v_symm_4379_, lean_object* v_a_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4378_, v_symm_4379_, v_x_4381_, v_a_4380_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRewriteSeq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_term_4378_ = stack[0].m_obj;
uint8_t v_symm_4379_ = stack[1].m_num;
lean_object* v_a_4380_ = stack[2].m_obj;
lean_object* v_x_4381_ = stack[3].m_obj;
lean_object* v___y_4382_ = stack[4].m_obj;
lean_object* v___y_4383_ = stack[5].m_obj;
lean_object* v___y_4384_ = stack[6].m_obj;
lean_object* v___y_4385_ = stack[7].m_obj;
lean_object* v___y_4386_ = stack[8].m_obj;
lean_object* v___y_4387_ = stack[9].m_obj;
lean_object* v___y_4388_ = stack[10].m_obj;
lean_object* v___y_4389_ = stack[11].m_obj;
lean_object* v_res_4392_;
v_res_4392_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4378_, v_symm_4379_, v_a_4380_, v_x_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
stack->m_obj
 = v_res_4392_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4393_, lean_object* v_symm_4394_, lean_object* v_a_4395_, lean_object* v_x_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
uint8_t v_symm_boxed_4406_; lean_object* v_res_4407_; 
v_symm_boxed_4406_ = lean_unbox(v_symm_4394_);
v_res_4407_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4393_, v_symm_boxed_4406_, v_a_4395_, v_x_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
return v_res_4407_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4408_, lean_object* v___x_4409_, lean_object* v___f_4410_, uint8_t v_symm_4411_, lean_object* v_term_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; lean_object* v___f_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4422_ = lean_box(v_symm_4411_);
lean_inc_ref(v_a_4408_);
lean_inc(v_term_4412_);
v___f_4423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4423_, 0, v_term_4412_);
lean_closure_set(v___f_4423_, 1, v___x_4422_);
lean_closure_set(v___f_4423_, 2, v_a_4408_);
v___x_4424_ = lean_box(v_symm_4411_);
v___x_4425_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4425_, 0, v_term_4412_);
lean_closure_set(v___x_4425_, 1, v___x_4424_);
lean_closure_set(v___x_4425_, 2, v_a_4408_);
v___x_4426_ = l_Lean_Elab_Tactic_withLocation(v___x_4409_, v___f_4423_, v___x_4425_, v___f_4410_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v___x_4426_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRewriteSeq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4408_ = stack[0].m_obj;
lean_object* v___x_4409_ = stack[1].m_obj;
lean_object* v___f_4410_ = stack[2].m_obj;
uint8_t v_symm_4411_ = stack[3].m_num;
lean_object* v_term_4412_ = stack[4].m_obj;
lean_object* v___y_4413_ = stack[5].m_obj;
lean_object* v___y_4414_ = stack[6].m_obj;
lean_object* v___y_4415_ = stack[7].m_obj;
lean_object* v___y_4416_ = stack[8].m_obj;
lean_object* v___y_4417_ = stack[9].m_obj;
lean_object* v___y_4418_ = stack[10].m_obj;
lean_object* v___y_4419_ = stack[11].m_obj;
lean_object* v___y_4420_ = stack[12].m_obj;
lean_object* v_res_4427_;
v_res_4427_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4408_, v___x_4409_, v___f_4410_, v_symm_4411_, v_term_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
stack->m_obj
 = v_res_4427_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4428_, lean_object* v___x_4429_, lean_object* v___f_4430_, lean_object* v_symm_4431_, lean_object* v_term_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
uint8_t v_symm_boxed_4442_; lean_object* v_res_4443_; 
v_symm_boxed_4442_ = lean_unbox(v_symm_4431_);
v_res_4443_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4428_, v___x_4429_, v___f_4430_, v_symm_boxed_4442_, v_term_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___x_4429_);
return v_res_4443_;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v___f_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; uint8_t v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___f_4460_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4461_ = lean_unsigned_to_nat(1u);
v___x_4462_ = l_Lean_Syntax_getArg(v_stx_4450_, v___x_4461_);
v___x_4463_ = 1;
v___x_4464_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4465_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4462_, v___x_4464_, v___x_4463_, v_a_4451_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___f_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4467_ = lean_unsigned_to_nat(3u);
v___x_4468_ = l_Lean_Syntax_getArg(v_stx_4450_, v___x_4467_);
v___x_4469_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4468_);
lean_dec(v___x_4468_);
v___f_4470_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4470_, 0, v_a_4466_);
lean_closure_set(v___f_4470_, 1, v___x_4469_);
lean_closure_set(v___f_4470_, 2, v___f_4460_);
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = l_Lean_Syntax_getArg(v_stx_4450_, v___x_4471_);
v___x_4473_ = lean_unsigned_to_nat(2u);
v___x_4474_ = l_Lean_Syntax_getArg(v_stx_4450_, v___x_4473_);
v___x_4475_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4472_, v___x_4474_, v___f_4470_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v___x_4474_);
return v___x_4475_;
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
v_a_4476_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4465_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4465_);
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
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalRewriteSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4450_ = stack[0].m_obj;
lean_object* v_a_4451_ = stack[1].m_obj;
lean_object* v_a_4452_ = stack[2].m_obj;
lean_object* v_a_4453_ = stack[3].m_obj;
lean_object* v_a_4454_ = stack[4].m_obj;
lean_object* v_a_4455_ = stack[5].m_obj;
lean_object* v_a_4456_ = stack[6].m_obj;
lean_object* v_a_4457_ = stack[7].m_obj;
lean_object* v_a_4458_ = stack[8].m_obj;
lean_object* v_res_4484_;
v_res_4484_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
stack->m_obj
 = v_res_4484_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_stx_4485_);
return v_res_4495_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4511_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4515_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4511_, v___x_4512_, v___x_4513_, v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4516_;
v_res_4516_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
stack->m_obj
 = v_res_4516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4518_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4547_ = l_Lean_addBuiltinDeclarationRanges(v___x_4545_, v___x_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4548_;
v_res_4548_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
stack->m_obj
 = v_res_4548_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4550_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig = _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig);
res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
