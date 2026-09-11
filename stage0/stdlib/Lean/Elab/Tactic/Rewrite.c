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
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Try rewriting with `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 107, 61, 219, 24, 145, 46, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 84, 11, 37, 124, 73, 156, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 125, 72, 83, 103, 118, 157, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalRewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
static lean_object* _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0));
v___x_25_ = l_Lean_stringToMessageData(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(lean_object* v_e_26_, uint8_t v___x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_check(v_e_26_, v___x_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_41_; 
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_41_ == 0)
{
lean_object* v_unused_42_; 
v_unused_42_ = lean_ctor_get(v___x_33_, 0);
lean_dec(v_unused_42_);
v___x_35_ = v___x_33_;
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
else
{
lean_dec(v___x_33_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = l_Lean_MessageData_nil;
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_62_; 
v_a_43_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_62_ == 0)
{
v___x_45_ = v___x_33_;
v_isShared_46_ = v_isSharedCheck_62_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_33_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_62_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
uint8_t v___y_48_; uint8_t v___x_60_; 
v___x_60_ = l_Lean_Exception_isInterrupt(v_a_43_);
if (v___x_60_ == 0)
{
uint8_t v___x_61_; 
lean_inc(v_a_43_);
v___x_61_ = l_Lean_Exception_isRuntime(v_a_43_);
v___y_48_ = v___x_61_;
goto v___jp_47_;
}
else
{
v___y_48_ = v___x_60_;
goto v___jp_47_;
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_49_ = lean_obj_once(&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1, &l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1);
v___x_50_ = l_Lean_Exception_toMessageData(v_a_43_);
v___x_51_ = l_Lean_indentD(v___x_50_);
v___x_52_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = l_Lean_MessageData_note(v___x_52_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 0);
lean_ctor_set(v___x_45_, 0, v___x_53_);
v___x_55_ = v___x_45_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
else
{
lean_object* v___x_58_; 
if (v_isShared_46_ == 0)
{
v___x_58_ = v___x_45_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_43_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed(lean_object* v_e_63_, lean_object* v___x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v___x_12331__boxed_70_; lean_object* v_res_71_; 
v___x_12331__boxed_70_ = lean_unbox(v___x_64_);
v_res_71_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_63_, v___x_12331__boxed_70_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2(lean_object* v_typeCheckNote_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_74_, 0, v_x_73_);
lean_ctor_set(v___x_74_, 1, v_typeCheckNote_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(lean_object* v_e_75_, lean_object* v_x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___f_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_typeCheckNote_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
v___f_86_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_86_, 0, v_x_76_);
lean_closure_set(v___f_86_, 1, v___y_77_);
lean_closure_set(v___f_86_, 2, v___y_78_);
lean_closure_set(v___f_86_, 3, v___y_79_);
lean_closure_set(v___f_86_, 4, v___y_80_);
v___x_87_ = 5;
v___x_88_ = lean_box(v___x_87_);
lean_inc_ref(v_e_75_);
v___f_89_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed), 7, 2);
lean_closure_set(v___f_89_, 0, v_e_75_);
lean_closure_set(v___f_89_, 1, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_array_push(v___x_91_, v_e_75_);
v_typeCheckNote_93_ = l_Lean_MessageData_ofLazyM(v___f_89_, v___x_92_);
v___f_94_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2), 2, 1);
lean_closure_set(v___f_94_, 0, v_typeCheckNote_93_);
v___x_95_ = l_Lean_Meta_mapErrorImp___redArg(v___f_86_, v___f_94_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_95_) == 0)
{
return v___x_95_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___boxed(lean_object* v_e_104_, lean_object* v_x_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_104_, v_x_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object* v_00_u03b1_116_, lean_object* v_e_117_, lean_object* v_x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_117_, v_x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object* v_00_u03b1_129_, lean_object* v_e_130_, lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v_00_u03b1_129_, v_e_130_, v_x_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_141_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_box(0);
v___x_143_ = l_Lean_Elab_abortTacticExceptionId;
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg(){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___boxed(lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(lean_object* v_00_u03b1_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___boxed(lean_object* v_00_u03b1_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(v_00_u03b1_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0(lean_object* v_mvarId_172_, lean_object* v_e_173_, lean_object* v_a_174_, uint8_t v_symm_175_, lean_object* v_config_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_MVarId_rewrite(v_mvarId_172_, v_e_173_, v_a_174_, v_symm_175_, v_config_176_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed(lean_object* v_mvarId_187_, lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_symm_190_, lean_object* v_config_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v_symm_boxed_201_; lean_object* v_res_202_; 
v_symm_boxed_201_ = lean_unbox(v_symm_190_);
v_res_202_ = l_Lean_Elab_Tactic_elabRewrite___lam__0(v_mvarId_187_, v_e_188_, v_a_189_, v_symm_boxed_201_, v_config_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_202_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
else
{
lean_object* v_key_206_; lean_object* v_tail_207_; uint8_t v___x_208_; 
v_key_206_ = lean_ctor_get(v_x_204_, 0);
v_tail_207_ = lean_ctor_get(v_x_204_, 2);
v___x_208_ = lean_expr_eqv(v_key_206_, v_a_203_);
if (v___x_208_ == 0)
{
v_x_204_ = v_tail_207_;
goto _start;
}
else
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_210_, v_x_211_);
lean_dec(v_x_211_);
lean_dec_ref(v_a_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_m_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_buckets_216_; lean_object* v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v_fold_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_buckets_216_ = lean_ctor_get(v_m_214_, 1);
v___x_217_ = lean_array_get_size(v_buckets_216_);
v___x_218_ = l_Lean_Expr_hash(v_a_215_);
v___x_219_ = 32ULL;
v___x_220_ = lean_uint64_shift_right(v___x_218_, v___x_219_);
v_fold_221_ = lean_uint64_xor(v___x_218_, v___x_220_);
v___x_222_ = 16ULL;
v___x_223_ = lean_uint64_shift_right(v_fold_221_, v___x_222_);
v___x_224_ = lean_uint64_xor(v_fold_221_, v___x_223_);
v___x_225_ = lean_uint64_to_usize(v___x_224_);
v___x_226_ = lean_usize_of_nat(v___x_217_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_sub(v___x_226_, v___x_227_);
v___x_229_ = lean_usize_land(v___x_225_, v___x_228_);
v___x_230_ = lean_array_uget_borrowed(v_buckets_216_, v___x_229_);
v___x_231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_215_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_232_, v_a_233_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_m_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(lean_object* v_mvarId_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_mctx_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_240_ = lean_st_ref_get(v___y_238_);
v_mctx_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_mctx_241_);
lean_dec(v___x_240_);
v___x_242_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_241_, v_mvarId_236_);
lean_dec_ref(v_mctx_241_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_237_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec(v_mvarId_246_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(lean_object* v_mvarId_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_mctx_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_mctx_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_mctx_256_);
lean_dec(v___x_255_);
v___x_257_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_256_, v_mvarId_251_);
lean_dec_ref(v_mctx_256_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___y_252_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg___boxed(lean_object* v_mvarId_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec(v_mvarId_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
return v_x_266_;
}
else
{
lean_object* v_key_268_; lean_object* v_value_269_; lean_object* v_tail_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_293_; 
v_key_268_ = lean_ctor_get(v_x_267_, 0);
v_value_269_ = lean_ctor_get(v_x_267_, 1);
v_tail_270_ = lean_ctor_get(v_x_267_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_293_ == 0)
{
v___x_272_ = v_x_267_;
v_isShared_273_ = v_isSharedCheck_293_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_tail_270_);
lean_inc(v_value_269_);
lean_inc(v_key_268_);
lean_dec(v_x_267_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_293_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v_fold_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_274_ = lean_array_get_size(v_x_266_);
v___x_275_ = l_Lean_Expr_hash(v_key_268_);
v___x_276_ = 32ULL;
v___x_277_ = lean_uint64_shift_right(v___x_275_, v___x_276_);
v_fold_278_ = lean_uint64_xor(v___x_275_, v___x_277_);
v___x_279_ = 16ULL;
v___x_280_ = lean_uint64_shift_right(v_fold_278_, v___x_279_);
v___x_281_ = lean_uint64_xor(v_fold_278_, v___x_280_);
v___x_282_ = lean_uint64_to_usize(v___x_281_);
v___x_283_ = lean_usize_of_nat(v___x_274_);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_sub(v___x_283_, v___x_284_);
v___x_286_ = lean_usize_land(v___x_282_, v___x_285_);
v___x_287_ = lean_array_uget_borrowed(v_x_266_, v___x_286_);
lean_inc(v___x_287_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 2, v___x_287_);
v___x_289_ = v___x_272_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_key_268_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_value_269_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v___x_287_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_array_uset(v_x_266_, v___x_286_, v___x_289_);
v_x_266_ = v___x_290_;
v_x_267_ = v_tail_270_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(lean_object* v_i_294_, lean_object* v_source_295_, lean_object* v_target_296_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_source_295_);
v___x_298_ = lean_nat_dec_lt(v_i_294_, v___x_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_source_295_);
lean_dec(v_i_294_);
return v_target_296_;
}
else
{
lean_object* v_es_299_; lean_object* v___x_300_; lean_object* v_source_301_; lean_object* v_target_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_es_299_ = lean_array_fget(v_source_295_, v_i_294_);
v___x_300_ = lean_box(0);
v_source_301_ = lean_array_fset(v_source_295_, v_i_294_, v___x_300_);
v_target_302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_target_296_, v_es_299_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_i_294_, v___x_303_);
lean_dec(v_i_294_);
v_i_294_ = v___x_304_;
v_source_295_ = v_source_301_;
v_target_296_ = v_target_302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object* v_data_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_nbuckets_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_307_ = lean_array_get_size(v_data_306_);
v___x_308_ = lean_unsigned_to_nat(2u);
v_nbuckets_309_ = lean_nat_mul(v___x_307_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_box(0);
v___x_312_ = lean_mk_array(v_nbuckets_309_, v___x_311_);
v___x_313_ = lean_array_propagate_mark(v_data_306_, v___x_312_);
v___x_314_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v___x_310_, v_data_306_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_m_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v_size_318_; lean_object* v_buckets_319_; lean_object* v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v_fold_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v_bkt_333_; uint8_t v___x_334_; 
v_size_318_ = lean_ctor_get(v_m_315_, 0);
v_buckets_319_ = lean_ctor_get(v_m_315_, 1);
v___x_320_ = lean_array_get_size(v_buckets_319_);
v___x_321_ = l_Lean_Expr_hash(v_a_316_);
v___x_322_ = 32ULL;
v___x_323_ = lean_uint64_shift_right(v___x_321_, v___x_322_);
v_fold_324_ = lean_uint64_xor(v___x_321_, v___x_323_);
v___x_325_ = 16ULL;
v___x_326_ = lean_uint64_shift_right(v_fold_324_, v___x_325_);
v___x_327_ = lean_uint64_xor(v_fold_324_, v___x_326_);
v___x_328_ = lean_uint64_to_usize(v___x_327_);
v___x_329_ = lean_usize_of_nat(v___x_320_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_sub(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_land(v___x_328_, v___x_331_);
v_bkt_333_ = lean_array_uget_borrowed(v_buckets_319_, v___x_332_);
v___x_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_316_, v_bkt_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_355_; 
lean_inc_ref(v_buckets_319_);
lean_inc(v_size_318_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_m_315_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_356_ = lean_ctor_get(v_m_315_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_m_315_, 0);
lean_dec(v_unused_357_);
v___x_336_ = v_m_315_;
v_isShared_337_ = v_isSharedCheck_355_;
goto v_resetjp_335_;
}
else
{
lean_dec(v_m_315_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_355_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v_size_x27_339_; lean_object* v___x_340_; lean_object* v_buckets_x27_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v_size_x27_339_ = lean_nat_add(v_size_318_, v___x_338_);
lean_dec(v_size_318_);
lean_inc(v_bkt_333_);
v___x_340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_340_, 0, v_a_316_);
lean_ctor_set(v___x_340_, 1, v_b_317_);
lean_ctor_set(v___x_340_, 2, v_bkt_333_);
v_buckets_x27_341_ = lean_array_uset(v_buckets_319_, v___x_332_, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = lean_nat_mul(v_size_x27_339_, v___x_342_);
v___x_344_ = lean_unsigned_to_nat(3u);
v___x_345_ = lean_nat_div(v___x_343_, v___x_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_array_get_size(v_buckets_x27_341_);
v___x_347_ = lean_nat_dec_le(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
if (v___x_347_ == 0)
{
lean_object* v_val_348_; lean_object* v___x_350_; 
v_val_348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_buckets_x27_341_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_val_348_);
lean_ctor_set(v___x_336_, 0, v_size_x27_339_);
v___x_350_ = v___x_336_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_size_x27_339_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_val_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v___x_353_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_buckets_x27_341_);
lean_ctor_set(v___x_336_, 0, v_size_x27_339_);
v___x_353_ = v___x_336_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_x27_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_buckets_x27_341_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_dec(v_b_317_);
lean_dec_ref(v_a_316_);
return v_m_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(lean_object* v_mvarId_362_, lean_object* v_e_363_, lean_object* v_a_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_d_375_; lean_object* v_b_376_; lean_object* v___y_377_; uint8_t v___x_383_; 
v___x_383_ = l_Lean_Expr_hasExprMVar(v_e_363_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref(v_e_363_);
v___x_384_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_a_364_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_364_, v_e_363_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_box(0);
lean_inc_ref(v_e_363_);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_364_, v_e_363_, v___x_388_);
switch(lean_obj_tag(v_e_363_))
{
case 11:
{
lean_object* v_struct_390_; 
v_struct_390_ = lean_ctor_get(v_e_363_, 2);
lean_inc_ref(v_struct_390_);
lean_dec_ref_known(v_e_363_, 3);
v_e_363_ = v_struct_390_;
v_a_364_ = v___x_389_;
goto _start;
}
case 7:
{
lean_object* v_binderType_392_; lean_object* v_body_393_; 
v_binderType_392_ = lean_ctor_get(v_e_363_, 1);
lean_inc_ref(v_binderType_392_);
v_body_393_ = lean_ctor_get(v_e_363_, 2);
lean_inc_ref(v_body_393_);
lean_dec_ref_known(v_e_363_, 3);
v_d_375_ = v_binderType_392_;
v_b_376_ = v_body_393_;
v___y_377_ = v___x_389_;
goto v___jp_374_;
}
case 6:
{
lean_object* v_binderType_394_; lean_object* v_body_395_; 
v_binderType_394_ = lean_ctor_get(v_e_363_, 1);
lean_inc_ref(v_binderType_394_);
v_body_395_ = lean_ctor_get(v_e_363_, 2);
lean_inc_ref(v_body_395_);
lean_dec_ref_known(v_e_363_, 3);
v_d_375_ = v_binderType_394_;
v_b_376_ = v_body_395_;
v___y_377_ = v___x_389_;
goto v___jp_374_;
}
case 8:
{
lean_object* v_type_396_; lean_object* v_value_397_; lean_object* v_body_398_; lean_object* v___x_399_; 
v_type_396_ = lean_ctor_get(v_e_363_, 1);
lean_inc_ref(v_type_396_);
v_value_397_ = lean_ctor_get(v_e_363_, 2);
lean_inc_ref(v_value_397_);
v_body_398_ = lean_ctor_get(v_e_363_, 3);
lean_inc_ref(v_body_398_);
lean_dec_ref_known(v_e_363_, 4);
v___x_399_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_362_, v_type_396_, v___x_389_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_fst_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
v_fst_401_ = lean_ctor_get(v_a_400_, 0);
if (lean_obj_tag(v_fst_401_) == 0)
{
lean_dec(v_a_400_);
lean_dec_ref(v_body_398_);
lean_dec_ref(v_value_397_);
return v___x_399_;
}
else
{
lean_object* v_snd_402_; lean_object* v___x_403_; 
lean_dec_ref_known(v___x_399_, 1);
v_snd_402_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_snd_402_);
lean_dec(v_a_400_);
v___x_403_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_362_, v_value_397_, v_snd_402_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_fst_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
v_fst_405_ = lean_ctor_get(v_a_404_, 0);
if (lean_obj_tag(v_fst_405_) == 0)
{
lean_dec(v_a_404_);
lean_dec_ref(v_body_398_);
return v___x_403_;
}
else
{
lean_object* v_snd_406_; 
lean_dec_ref_known(v___x_403_, 1);
v_snd_406_ = lean_ctor_get(v_a_404_, 1);
lean_inc(v_snd_406_);
lean_dec(v_a_404_);
v_e_363_ = v_body_398_;
v_a_364_ = v_snd_406_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_398_);
return v___x_403_;
}
}
}
else
{
lean_dec_ref(v_body_398_);
lean_dec_ref(v_value_397_);
return v___x_399_;
}
}
case 10:
{
lean_object* v_expr_408_; 
v_expr_408_ = lean_ctor_get(v_e_363_, 1);
lean_inc_ref(v_expr_408_);
lean_dec_ref_known(v_e_363_, 2);
v_e_363_ = v_expr_408_;
v_a_364_ = v___x_389_;
goto _start;
}
case 5:
{
lean_object* v_fn_410_; lean_object* v_arg_411_; lean_object* v___x_412_; 
v_fn_410_ = lean_ctor_get(v_e_363_, 0);
lean_inc_ref(v_fn_410_);
v_arg_411_ = lean_ctor_get(v_e_363_, 1);
lean_inc_ref(v_arg_411_);
lean_dec_ref_known(v_e_363_, 2);
v___x_412_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_362_, v_fn_410_, v___x_389_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_fst_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
v_fst_414_ = lean_ctor_get(v_a_413_, 0);
if (lean_obj_tag(v_fst_414_) == 0)
{
lean_dec(v_a_413_);
lean_dec_ref(v_arg_411_);
return v___x_412_;
}
else
{
lean_object* v_snd_415_; 
lean_dec_ref_known(v___x_412_, 1);
v_snd_415_ = lean_ctor_get(v_a_413_, 1);
lean_inc(v_snd_415_);
lean_dec(v_a_413_);
v_e_363_ = v_arg_411_;
v_a_364_ = v_snd_415_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_411_);
return v___x_412_;
}
}
case 2:
{
lean_object* v_mvarId_417_; lean_object* v___x_418_; 
v_mvarId_417_ = lean_ctor_get(v_e_363_, 0);
lean_inc(v_mvarId_417_);
lean_dec_ref_known(v_e_363_, 1);
v___x_418_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_362_, v_mvarId_417_, v___x_389_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_418_;
}
default: 
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_e_363_);
v___x_419_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_389_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_e_363_);
v___x_422_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_364_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
v___jp_374_:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_362_, v_d_375_, v___y_377_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_fst_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
v_fst_380_ = lean_ctor_get(v_a_379_, 0);
if (lean_obj_tag(v_fst_380_) == 0)
{
lean_dec(v_a_379_);
lean_dec_ref(v_b_376_);
return v___x_378_;
}
else
{
lean_object* v_snd_381_; 
lean_dec_ref_known(v___x_378_, 1);
v_snd_381_ = lean_ctor_get(v_a_379_, 1);
lean_inc(v_snd_381_);
lean_dec(v_a_379_);
v_e_363_ = v_b_376_;
v_a_364_ = v_snd_381_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_376_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(lean_object* v_mvarId_425_, lean_object* v_mvarId_x27_426_, lean_object* v_a_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_instBEqMVarId_beq(v_mvarId_425_, v_mvarId_x27_426_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_x27_426_, v_a_427_, v___y_433_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_522_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_522_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_522_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_522_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_fst_443_; 
v_fst_443_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_fst_443_);
if (lean_obj_tag(v_fst_443_) == 0)
{
lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_mvarId_x27_426_);
v_snd_444_ = lean_ctor_get(v_a_439_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v_a_439_, 0);
lean_dec(v_unused_463_);
v___x_446_ = v_a_439_;
v_isShared_447_ = v_isSharedCheck_462_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_dec(v_a_439_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_462_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
v_a_448_ = lean_ctor_get(v_fst_443_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_fst_443_);
if (v_isSharedCheck_461_ == 0)
{
v___x_450_ = v_fst_443_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v_fst_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_460_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_453_);
v___x_455_ = v___x_446_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_snd_444_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_455_);
v___x_457_ = v___x_441_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
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
else
{
lean_object* v_a_464_; 
lean_del_object(v___x_441_);
v_a_464_ = lean_ctor_get(v_fst_443_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v_fst_443_, 1);
if (lean_obj_tag(v_a_464_) == 0)
{
lean_object* v_snd_465_; lean_object* v___x_466_; 
v_snd_465_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_snd_465_);
lean_dec(v_a_439_);
v___x_466_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_x27_426_, v_snd_465_, v___y_433_);
lean_dec(v_mvarId_x27_426_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_510_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_510_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_510_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_510_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_fst_471_; 
v_fst_471_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_fst_471_);
if (lean_obj_tag(v_fst_471_) == 0)
{
lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_490_; 
v_snd_472_ = lean_ctor_get(v_a_467_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_a_467_, 0);
lean_dec(v_unused_491_);
v___x_474_ = v_a_467_;
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_a_467_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_489_; 
v_a_476_ = lean_ctor_get(v_fst_471_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_fst_471_);
if (v_isSharedCheck_489_ == 0)
{
v___x_478_ = v_fst_471_;
v_isShared_479_ = v_isSharedCheck_489_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v_fst_471_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_489_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_488_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_481_);
v___x_483_ = v___x_474_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_snd_472_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_483_);
v___x_485_ = v___x_469_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
else
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v_fst_471_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_fst_471_, 1);
if (lean_obj_tag(v_a_492_) == 0)
{
lean_object* v_snd_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_504_; 
v_snd_493_ = lean_ctor_get(v_a_467_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_a_467_, 0);
lean_dec(v_unused_505_);
v___x_495_ = v_a_467_;
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_snd_493_);
lean_dec(v_a_467_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_493_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_499_);
v___x_501_ = v___x_469_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
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
else
{
lean_object* v_val_506_; lean_object* v_snd_507_; lean_object* v_mvarIdPending_508_; 
lean_del_object(v___x_469_);
v_val_506_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_492_, 1);
v_snd_507_ = lean_ctor_get(v_a_467_, 1);
lean_inc(v_snd_507_);
lean_dec(v_a_467_);
v_mvarIdPending_508_ = lean_ctor_get(v_val_506_, 1);
lean_inc(v_mvarIdPending_508_);
lean_dec(v_val_506_);
v_mvarId_x27_426_ = v_mvarIdPending_508_;
v_a_427_ = v_snd_507_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_466_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_466_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_snd_519_; lean_object* v_val_520_; lean_object* v___x_521_; 
lean_dec(v_mvarId_x27_426_);
v_snd_519_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_snd_519_);
lean_dec(v_a_439_);
v_val_520_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_a_464_, 1);
v___x_521_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_425_, v_val_520_, v_snd_519_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_mvarId_x27_426_);
v_a_523_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_438_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_438_);
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
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_mvarId_x27_426_);
v___x_531_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1));
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_a_427_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(lean_object* v_mvarId_534_, lean_object* v_mvarId_x27_535_, lean_object* v_a_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_534_, v_mvarId_x27_535_, v_a_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v_mvarId_534_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(lean_object* v_mvarId_547_, lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_547_, v_e_548_, v_a_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_unsigned_to_nat(16u);
v___x_562_ = lean_mk_array(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_mvarId_566_, lean_object* v_e_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = l_Lean_Expr_hasExprMVar(v_e_567_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec_ref(v_e_567_);
v___x_578_ = 1;
v___x_579_ = lean_box(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
v___x_582_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_566_, v_e_567_, v___x_581_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_597_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_597_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_fst_587_; 
v_fst_587_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_fst_587_);
lean_dec(v_a_583_);
if (lean_obj_tag(v_fst_587_) == 0)
{
uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec_ref_known(v_fst_587_, 1);
v___x_588_ = 0;
v___x_589_ = lean_box(v___x_588_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_589_);
v___x_591_ = v___x_585_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec_ref_known(v_fst_587_, 1);
v___x_593_ = lean_box(v___x_577_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_593_);
v___x_595_ = v___x_585_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_582_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_582_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_mvarId_606_, lean_object* v_e_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_606_, v_e_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v_mvarId_606_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
if (lean_obj_tag(v_a_620_) == 0)
{
lean_object* v___x_622_; 
v___x_622_ = l_List_reverse___redArg(v_a_621_);
return v___x_622_;
}
else
{
lean_object* v_head_623_; lean_object* v_tail_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_636_; 
v_head_623_ = lean_ctor_get(v_a_620_, 0);
v_tail_624_ = lean_ctor_get(v_a_620_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_a_620_);
if (v_isSharedCheck_636_ == 0)
{
v___x_626_ = v_a_620_;
v_isShared_627_ = v_isSharedCheck_636_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_tail_624_);
lean_inc(v_head_623_);
lean_dec(v_a_620_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_636_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v_index_629_; uint8_t v___x_630_; 
lean_inc(v_head_623_);
v___x_628_ = l_Lean_MetavarContext_getDecl(v___x_618_, v_head_623_);
v_index_629_ = lean_ctor_get(v___x_628_, 6);
lean_inc(v_index_629_);
lean_dec_ref(v___x_628_);
v___x_630_ = lean_nat_dec_le(v___x_619_, v_index_629_);
lean_dec(v_index_629_);
if (v___x_630_ == 0)
{
lean_del_object(v___x_626_);
lean_dec(v_head_623_);
v_a_620_ = v_tail_624_;
goto _start;
}
else
{
lean_object* v___x_633_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_a_621_);
v___x_633_ = v___x_626_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_head_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_a_621_);
v___x_633_ = v_reuseFailAlloc_635_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
v_a_620_ = v_tail_624_;
v_a_621_ = v___x_633_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v___x_637_, v___x_638_, v_a_639_, v_a_640_);
lean_dec(v___x_638_);
lean_dec_ref(v___x_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(lean_object* v_msgData_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_toCold_651_; lean_object* v_mctx_652_; lean_object* v_lctx_653_; lean_object* v_options_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_648_ = lean_st_ref_get(v___y_646_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = lean_st_ref_get(v___y_644_);
v_toCold_651_ = lean_ctor_get(v___y_645_, 0);
v_mctx_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_mctx_652_);
lean_dec(v___x_650_);
v_lctx_653_ = lean_ctor_get(v___y_643_, 2);
v_options_654_ = lean_ctor_get(v_toCold_651_, 2);
lean_inc_ref(v_options_654_);
lean_inc_ref(v_lctx_653_);
v___x_655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_655_, 0, v_env_649_);
lean_ctor_set(v___x_655_, 1, v_mctx_652_);
lean_ctor_set(v___x_655_, 2, v_lctx_653_);
lean_ctor_set(v___x_655_, 3, v_options_654_);
v___x_656_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_msgData_642_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_ref_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_ref_671_ = lean_ctor_get(v___y_668_, 2);
v___x_672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_inc(v_ref_671_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_ref_671_);
lean_ctor_set(v___x_677_, 1, v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object* v_ref_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_toCold_700_; lean_object* v_currRecDepth_701_; lean_object* v_ref_702_; uint8_t v_diag_703_; uint8_t v_suppressElabErrors_704_; lean_object* v_ref_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_toCold_700_ = lean_ctor_get(v___y_697_, 0);
v_currRecDepth_701_ = lean_ctor_get(v___y_697_, 1);
v_ref_702_ = lean_ctor_get(v___y_697_, 2);
v_diag_703_ = lean_ctor_get_uint8(v___y_697_, sizeof(void*)*3);
v_suppressElabErrors_704_ = lean_ctor_get_uint8(v___y_697_, sizeof(void*)*3 + 1);
v_ref_705_ = l_Lean_replaceRef(v_ref_689_, v_ref_702_);
lean_inc(v_currRecDepth_701_);
lean_inc_ref(v_toCold_700_);
v___x_706_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_706_, 0, v_toCold_700_);
lean_ctor_set(v___x_706_, 1, v_currRecDepth_701_);
lean_ctor_set(v___x_706_, 2, v_ref_705_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3, v_diag_703_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 1, v_suppressElabErrors_704_);
v___x_707_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_690_, v___y_695_, v___y_696_, v___x_706_, v___y_698_);
lean_dec_ref_known(v___x_706_, 3);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_708_, v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v_ref_708_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_726_, lean_object* v_e_727_, lean_object* v_stx_728_, uint8_t v_symm_729_, lean_object* v_config_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_st_ref_get(v_a_736_);
v___x_741_ = lean_box(0);
v___x_742_ = 1;
lean_inc(v_stx_728_);
v___x_743_ = l_Lean_Elab_Tactic_elabTerm(v_stx_728_, v___x_741_, v___x_742_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_mctx_744_; lean_object* v_a_745_; lean_object* v_mvarCounter_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___x_818_; 
v_mctx_744_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_mctx_744_);
lean_dec(v___x_740_);
v_a_745_ = lean_ctor_get(v___x_743_, 0);
lean_inc_n(v_a_745_, 2);
lean_dec_ref_known(v___x_743_, 1);
v_mvarCounter_746_ = lean_ctor_get(v_mctx_744_, 3);
lean_inc(v_mvarCounter_746_);
lean_dec_ref(v_mctx_744_);
v___x_747_ = lean_box(v_symm_729_);
lean_inc_ref(v_e_727_);
lean_inc(v_mvarId_726_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_748_, 0, v_mvarId_726_);
lean_closure_set(v___f_748_, 1, v_e_727_);
lean_closure_set(v___f_748_, 2, v_a_745_);
lean_closure_set(v___f_748_, 3, v___x_747_);
lean_closure_set(v___f_748_, 4, v_config_730_);
v___x_818_ = l_Lean_Expr_hasSyntheticSorry(v_a_745_);
if (v___x_818_ == 0)
{
v___y_782_ = v_a_731_;
v___y_783_ = v_a_732_;
v___y_784_ = v_a_733_;
v___y_785_ = v_a_734_;
v___y_786_ = v_a_735_;
v___y_787_ = v_a_736_;
v___y_788_ = v_a_737_;
v___y_789_ = v_a_738_;
goto v___jp_781_;
}
else
{
lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v___f_748_);
lean_dec(v_mvarCounter_746_);
lean_dec(v_a_745_);
lean_dec(v_stx_728_);
lean_dec_ref(v_e_727_);
lean_dec(v_mvarId_726_);
v___x_819_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
v___jp_749_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_727_, v___f_748_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_780_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_780_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v_mctx_764_; lean_object* v_eNew_765_; lean_object* v_eqProof_766_; lean_object* v_mvarIds_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
v___x_763_ = lean_st_ref_get(v___y_755_);
v_mctx_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_ref(v_mctx_764_);
lean_dec(v___x_763_);
v_eNew_765_ = lean_ctor_get(v_a_759_, 0);
v_eqProof_766_ = lean_ctor_get(v_a_759_, 1);
v_mvarIds_767_ = lean_ctor_get(v_a_759_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_779_ == 0)
{
v___x_769_ = v_a_759_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_mvarIds_767_);
lean_inc(v_eqProof_766_);
lean_inc(v_eNew_765_);
lean_dec(v_a_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_764_, v_mvarCounter_746_, v_mvarIds_767_, v___x_771_);
lean_dec(v_mvarCounter_746_);
lean_dec_ref(v_mctx_764_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 2, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_eNew_765_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_eqProof_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_774_);
v___x_776_ = v___x_761_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_746_);
return v___x_758_;
}
}
v___jp_781_:
{
lean_object* v___x_790_; 
lean_inc(v_a_745_);
v___x_790_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_726_, v_a_745_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; uint8_t v___x_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = lean_unbox(v_a_791_);
lean_dec(v_a_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v___f_748_);
lean_dec(v_mvarCounter_746_);
lean_dec_ref(v_e_727_);
v___x_793_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_794_ = l_Lean_indentExpr(v_a_745_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_Expr_mvar___override(v_mvarId_726_);
v___x_799_ = l_Lean_MessageData_ofExpr(v___x_798_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_797_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_728_, v___x_800_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v_stx_728_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_dec(v_a_745_);
lean_dec(v_stx_728_);
lean_dec(v_mvarId_726_);
v___y_750_ = v___y_782_;
v___y_751_ = v___y_783_;
v___y_752_ = v___y_784_;
v___y_753_ = v___y_785_;
v___y_754_ = v___y_786_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
v___y_757_ = v___y_789_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___f_748_);
lean_dec(v_mvarCounter_746_);
lean_dec(v_a_745_);
lean_dec(v_stx_728_);
lean_dec_ref(v_e_727_);
lean_dec(v_mvarId_726_);
v_a_810_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_790_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_790_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v___x_740_);
lean_dec_ref(v_config_730_);
lean_dec(v_stx_728_);
lean_dec_ref(v_e_727_);
lean_dec(v_mvarId_726_);
v_a_828_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_743_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_743_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_836_, lean_object* v_e_837_, lean_object* v_stx_838_, lean_object* v_symm_839_, lean_object* v_config_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_symm_boxed_850_; lean_object* v_res_851_; 
v_symm_boxed_850_ = lean_unbox(v_symm_839_);
v_res_851_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_836_, v_e_837_, v_stx_838_, v_symm_boxed_850_, v_config_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_852_, lean_object* v_ref_853_, lean_object* v_msg_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_853_, v_msg_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_865_, lean_object* v_ref_866_, lean_object* v_msg_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_865_, v_ref_866_, v_msg_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v_ref_866_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_879_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_890_, lean_object* v_msg_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_890_, v_msg_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_901_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_902_, lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_903_, v_a_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_906_, v_m_907_, v_a_908_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_m_907_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_911_, lean_object* v_m_912_, lean_object* v_a_913_, lean_object* v_b_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_912_, v_a_913_, v_b_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_916_, v___y_917_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v_mvarId_928_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_940_, v___y_941_, v___y_947_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_mvarId_952_);
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_964_, lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_968_, lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_968_, v_a_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec_ref(v_a_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_973_, lean_object* v_data_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_976_, lean_object* v_i_977_, lean_object* v_source_978_, lean_object* v_target_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_977_, v_source_978_, v_target_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_992_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_992_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1017_, lean_object* v_mvarId_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_mvarId_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1026_, v_mvarId_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1035_, lean_object* v_i_1036_, lean_object* v_k_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_array_get_size(v_keys_1035_);
v___x_1039_ = lean_nat_dec_lt(v_i_1036_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_i_1036_);
return v___x_1039_;
}
else
{
lean_object* v_k_x27_1040_; uint8_t v___x_1041_; 
v_k_x27_1040_ = lean_array_fget_borrowed(v_keys_1035_, v_i_1036_);
v___x_1041_ = l_Lean_instBEqMVarId_beq(v_k_1037_, v_k_x27_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_add(v_i_1036_, v___x_1042_);
lean_dec(v_i_1036_);
v_i_1036_ = v___x_1043_;
goto _start;
}
else
{
lean_dec(v_i_1036_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1045_, v_i_1046_, v_k_1047_);
lean_dec(v_k_1047_);
lean_dec_ref(v_keys_1045_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1050_, size_t v_x_1051_, lean_object* v_x_1052_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
lean_object* v_es_1053_; lean_object* v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v_j_1057_; lean_object* v___x_1058_; 
v_es_1053_ = lean_ctor_get(v_x_1050_, 0);
v___x_1054_ = lean_box(2);
v___x_1055_ = ((size_t)31ULL);
v___x_1056_ = lean_usize_land(v_x_1051_, v___x_1055_);
v_j_1057_ = lean_usize_to_nat(v___x_1056_);
v___x_1058_ = lean_array_get_borrowed(v___x_1054_, v_es_1053_, v_j_1057_);
lean_dec(v_j_1057_);
switch(lean_obj_tag(v___x_1058_))
{
case 0:
{
lean_object* v_key_1059_; uint8_t v___x_1060_; 
v_key_1059_ = lean_ctor_get(v___x_1058_, 0);
v___x_1060_ = l_Lean_instBEqMVarId_beq(v_x_1052_, v_key_1059_);
return v___x_1060_;
}
case 1:
{
lean_object* v_node_1061_; size_t v___x_1062_; size_t v___x_1063_; 
v_node_1061_ = lean_ctor_get(v___x_1058_, 0);
v___x_1062_ = ((size_t)5ULL);
v___x_1063_ = lean_usize_shift_right(v_x_1051_, v___x_1062_);
v_x_1050_ = v_node_1061_;
v_x_1051_ = v___x_1063_;
goto _start;
}
default: 
{
uint8_t v___x_1065_; 
v___x_1065_ = 0;
return v___x_1065_;
}
}
}
else
{
lean_object* v_ks_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_ks_1066_ = lean_ctor_get(v_x_1050_, 0);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1066_, v___x_1067_, v_x_1052_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
size_t v_x_1908__boxed_1072_; uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_x_1908__boxed_1072_ = lean_unbox_usize(v_x_1070_);
lean_dec(v_x_1070_);
v_res_1073_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1069_, v_x_1908__boxed_1072_, v_x_1071_);
lean_dec(v_x_1071_);
lean_dec_ref(v_x_1069_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
uint64_t v___x_1077_; size_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = l_Lean_instHashableMVarId_hash(v_x_1076_);
v___x_1078_ = lean_uint64_to_usize(v___x_1077_);
v___x_1079_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1075_, v___x_1078_, v_x_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1080_, v_x_1081_);
lean_dec(v_x_1081_);
lean_dec_ref(v_x_1080_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_mctx_1088_; lean_object* v_eAssignment_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
v_mctx_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_mctx_1088_);
lean_dec(v___x_1087_);
v_eAssignment_1089_ = lean_ctor_get(v_mctx_1088_, 8);
lean_inc_ref(v_eAssignment_1089_);
lean_dec_ref(v_mctx_1088_);
v___x_1090_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1089_, v_mvarId_1084_);
lean_dec_ref(v_eAssignment_1089_);
v___x_1091_ = lean_box(v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec(v_mvarId_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_x_1098_);
return v___x_1104_;
}
else
{
lean_object* v_head_1105_; lean_object* v_tail_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1119_; 
v_head_1105_ = lean_ctor_get(v_x_1097_, 0);
v_tail_1106_ = lean_ctor_get(v_x_1097_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1108_ = v_x_1097_;
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_tail_1106_);
lean_inc(v_head_1105_);
lean_dec(v_x_1097_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1115_; lean_object* v_a_1116_; uint8_t v___x_1117_; 
v___x_1115_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1105_, v___y_1100_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = lean_unbox(v_a_1116_);
lean_dec(v_a_1116_);
if (v___x_1117_ == 0)
{
goto v___jp_1110_;
}
else
{
lean_del_object(v___x_1108_);
lean_dec(v_head_1105_);
v_x_1097_ = v_tail_1106_;
goto _start;
}
v___jp_1110_:
{
lean_object* v___x_1112_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v_x_1098_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_head_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_x_1098_);
v___x_1112_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v_x_1097_ = v_tail_1106_;
v_x_1098_ = v___x_1112_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
lean_inc(v_head_1128_);
v___x_1134_ = l_Lean_MVarId_getType(v_head_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Meta_isProp(v_a_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1148_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_unbox(v_a_1137_);
lean_dec(v_a_1137_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_head_1128_);
v___x_1142_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
uint8_t v___x_1146_; lean_object* v___x_1147_; 
lean_del_object(v___x_1139_);
v___x_1146_ = 2;
v___x_1147_ = l_Lean_MVarId_setKind___redArg(v_head_1128_, v___x_1146_, v___y_1130_);
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_head_1128_);
v_a_1149_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1136_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1136_);
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
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_head_1128_);
v_a_1157_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1134_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1134_);
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
if (lean_obj_tag(v_as_1172_) == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
else
{
lean_object* v_head_1180_; lean_object* v_tail_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v_head_1180_ = lean_ctor_get(v_as_1172_, 0);
lean_inc_n(v_head_1180_, 2);
v_tail_1181_ = lean_ctor_get(v_as_1172_, 1);
lean_inc(v_tail_1181_);
lean_dec_ref_known(v_as_1172_, 2);
v___f_1182_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1182_, 0, v_head_1180_);
v___x_1183_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1180_, v___f_1182_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_dec_ref_known(v___x_1183_, 1);
v_as_1172_ = v_tail_1181_;
goto _start;
}
else
{
lean_dec(v_tail_1181_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_eNew_1198_; lean_object* v_eqProof_1199_; lean_object* v_mvarIds_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1239_; 
v_eNew_1198_ = lean_ctor_get(v_r_1192_, 0);
v_eqProof_1199_ = lean_ctor_get(v_r_1192_, 1);
v_mvarIds_1200_ = lean_ctor_get(v_r_1192_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_r_1192_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1202_ = v_r_1192_;
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_mvarIds_1200_);
lean_inc(v_eqProof_1199_);
lean_inc(v_eNew_1198_);
lean_dec(v_r_1192_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_a_1205_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1200_, v___x_1226_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = l_List_reverse___redArg(v_a_1228_);
v_a_1205_ = v___x_1229_;
goto v___jp_1204_;
}
else
{
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1227_, 1);
v_a_1205_ = v_a_1230_;
goto v___jp_1204_;
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_del_object(v___x_1202_);
lean_dec_ref(v_eqProof_1199_);
lean_dec_ref(v_eNew_1198_);
v_a_1231_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1227_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1206_; 
lean_inc(v_a_1205_);
v___x_1206_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1205_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1216_; 
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1217_);
v___x_1208_ = v___x_1206_;
v_isShared_1209_ = v_isSharedCheck_1216_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v___x_1206_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1216_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 2, v_a_1205_);
v___x_1211_ = v___x_1202_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_eNew_1198_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_eqProof_1199_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_a_1205_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1211_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1205_);
lean_del_object(v___x_1202_);
lean_dec_ref(v_eqProof_1199_);
lean_dec_ref(v_eNew_1198_);
v_a_1218_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1206_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1206_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1247_, v___y_1249_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v_mvarId_1254_);
return v_res_1260_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1265_, v_x_1266_, v_x_1267_);
lean_dec(v_x_1267_);
lean_dec_ref(v_x_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1270_, lean_object* v_x_1271_, size_t v_x_1272_, lean_object* v_x_1273_){
_start:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1271_, v_x_1272_, v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v_x_2247__boxed_1279_; uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_x_2247__boxed_1279_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_res_1280_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1275_, v_x_1276_, v_x_2247__boxed_1279_, v_x_1278_);
lean_dec(v_x_1278_);
lean_dec_ref(v_x_1276_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1282_, lean_object* v_keys_1283_, lean_object* v_vals_1284_, lean_object* v_heq_1285_, lean_object* v_i_1286_, lean_object* v_k_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1283_, v_i_1286_, v_k_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_heq_1292_, lean_object* v_i_1293_, lean_object* v_k_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1289_, v_keys_1290_, v_vals_1291_, v_heq_1292_, v_i_1293_, v_k_1294_);
lean_dec(v_k_1294_);
lean_dec_ref(v_vals_1291_);
lean_dec_ref(v_keys_1290_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1297_, uint8_t v_symm_1298_, lean_object* v_config_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1301_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1310_, v_a_1312_, v_stx_1297_, v_symm_1298_, v_config_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1313_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_a_1310_);
lean_dec_ref(v_config_1299_);
lean_dec(v_stx_1297_);
v_a_1314_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1311_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1311_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_config_1299_);
lean_dec(v_stx_1297_);
v_a_1322_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1309_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1309_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1330_, lean_object* v_symm_1331_, lean_object* v_config_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v_symm_boxed_1342_; lean_object* v_res_1343_; 
v_symm_boxed_1342_ = lean_unbox(v_symm_1331_);
v_res_1343_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1330_, v_symm_boxed_1342_, v_config_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1344_, uint8_t v_symm_1345_, lean_object* v_config_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___f_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1356_ = lean_box(v_symm_1345_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1357_, 0, v_stx_1344_);
lean_closure_set(v___f_1357_, 1, v___x_1356_);
lean_closure_set(v___f_1357_, 2, v_config_1346_);
v___x_1358_ = 1;
lean_inc(v_a_1348_);
lean_inc_ref(v_a_1347_);
v___x_1359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1359_, 0, lean_box(0));
lean_closure_set(v___x_1359_, 1, v___f_1357_);
lean_closure_set(v___x_1359_, 2, v_a_1347_);
lean_closure_set(v___x_1359_, 3, v_a_1348_);
v___x_1360_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1359_, v___x_1358_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1361_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1348_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_eNew_1366_; lean_object* v_eqProof_1367_; lean_object* v_mvarIds_1368_; lean_object* v___x_1369_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_eNew_1366_ = lean_ctor_get(v_a_1363_, 0);
lean_inc_ref(v_eNew_1366_);
v_eqProof_1367_ = lean_ctor_get(v_a_1363_, 1);
lean_inc_ref(v_eqProof_1367_);
v_mvarIds_1368_ = lean_ctor_get(v_a_1363_, 2);
lean_inc(v_mvarIds_1368_);
lean_dec(v_a_1363_);
v___x_1369_ = l_Lean_MVarId_replaceTargetEq(v_a_1365_, v_eNew_1366_, v_eqProof_1367_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1370_);
lean_ctor_set(v___x_1371_, 1, v_mvarIds_1368_);
v___x_1372_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1371_, v_a_1348_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1372_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v_mvarIds_1368_);
v_a_1373_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1369_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1369_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1363_);
v_a_1381_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1364_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1364_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1362_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1362_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1360_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1360_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1405_, lean_object* v_symm_1406_, lean_object* v_config_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
uint8_t v_symm_boxed_1417_; lean_object* v_res_1418_; 
v_symm_boxed_1417_ = lean_unbox(v_symm_1406_);
v_res_1418_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1405_, v_symm_boxed_1417_, v_config_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(lean_object* v_fvarId_1419_, lean_object* v_stx_1420_, uint8_t v_symm_1421_, lean_object* v_config_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1419_, v___y_1427_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1424_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l_Lean_LocalDecl_type(v_a_1433_);
lean_dec(v_a_1433_);
v___x_1437_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1435_, v___x_1436_, v_stx_1420_, v_symm_1421_, v_config_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1433_);
lean_dec_ref(v_config_1422_);
lean_dec(v_stx_1420_);
v_a_1438_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1434_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_config_1422_);
lean_dec(v_stx_1420_);
v_a_1446_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1432_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1432_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed(lean_object* v_fvarId_1454_, lean_object* v_stx_1455_, lean_object* v_symm_1456_, lean_object* v_config_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_symm_boxed_1467_; lean_object* v_res_1468_; 
v_symm_boxed_1467_ = lean_unbox(v_symm_1456_);
v_res_1468_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(v_fvarId_1454_, v_stx_1455_, v_symm_boxed_1467_, v_config_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(lean_object* v_eqProof_1469_, lean_object* v___x_1470_, lean_object* v_eNew_1471_, lean_object* v_a_1472_, lean_object* v_fvarId_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_mkEqMP(v_eqProof_1469_, v___x_1470_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_eNew_1471_);
v___x_1482_ = lean_box(0);
v___x_1483_ = l_Lean_MVarId_replace(v_a_1472_, v_fvarId_1473_, v_a_1480_, v___x_1481_, v___x_1482_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_fvarId_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_eNew_1471_);
v_a_1484_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1479_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed(lean_object* v_eqProof_1492_, lean_object* v___x_1493_, lean_object* v_eNew_1494_, lean_object* v_a_1495_, lean_object* v_fvarId_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(v_eqProof_1492_, v___x_1493_, v_eNew_1494_, v_a_1495_, v_fvarId_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(lean_object* v___f_1503_, uint8_t v___x_1504_, lean_object* v_fvarId_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc(v___y_1507_);
v___x_1515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1515_, 0, lean_box(0));
lean_closure_set(v___x_1515_, 1, v___f_1503_);
lean_closure_set(v___x_1515_, 2, v___y_1506_);
lean_closure_set(v___x_1515_, 3, v___y_1507_);
v___x_1516_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1515_, v___x_1504_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1517_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1507_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_eNew_1522_; lean_object* v_eqProof_1523_; lean_object* v_mvarIds_1524_; lean_object* v___x_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_n(v_a_1521_, 2);
lean_dec_ref_known(v___x_1520_, 1);
v_eNew_1522_ = lean_ctor_get(v_a_1519_, 0);
lean_inc_ref(v_eNew_1522_);
v_eqProof_1523_ = lean_ctor_get(v_a_1519_, 1);
lean_inc_ref(v_eqProof_1523_);
v_mvarIds_1524_ = lean_ctor_get(v_a_1519_, 2);
lean_inc(v_mvarIds_1524_);
lean_dec(v_a_1519_);
lean_inc(v_fvarId_1505_);
v___x_1525_ = l_Lean_mkFVar(v_fvarId_1505_);
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1526_, 0, v_eqProof_1523_);
lean_closure_set(v___f_1526_, 1, v___x_1525_);
lean_closure_set(v___f_1526_, 2, v_eNew_1522_);
lean_closure_set(v___f_1526_, 3, v_a_1521_);
lean_closure_set(v___f_1526_, 4, v_fvarId_1505_);
v___x_1527_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1521_, v___f_1526_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_fvarId_1529_; lean_object* v_mvarId_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v_fvarId_1529_ = lean_ctor_get(v_a_1528_, 0);
lean_inc(v_fvarId_1529_);
v_mvarId_1530_ = lean_ctor_get(v_a_1528_, 1);
lean_inc(v_mvarId_1530_);
lean_dec(v_a_1528_);
v___x_1531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_mvarId_1530_);
lean_ctor_set(v___x_1531_, 1, v_mvarIds_1524_);
v___x_1532_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1531_, v___y_1507_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1507_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1532_, 0);
lean_dec(v_unused_1540_);
v___x_1534_ = v___x_1532_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v___x_1532_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v_fvarId_1529_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_fvarId_1529_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_fvarId_1529_);
v_a_1541_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1532_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1532_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_mvarIds_1524_);
lean_dec(v___y_1507_);
v_a_1549_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1527_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1527_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1519_);
lean_dec(v___y_1507_);
lean_dec(v_fvarId_1505_);
v_a_1557_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1520_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1520_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___y_1507_);
lean_dec(v_fvarId_1505_);
v_a_1565_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1518_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1518_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v___y_1507_);
lean_dec(v_fvarId_1505_);
v_a_1573_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1516_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1516_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed(lean_object* v___f_1581_, lean_object* v___x_1582_, lean_object* v_fvarId_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___x_1614__boxed_1593_; lean_object* v_res_1594_; 
v___x_1614__boxed_1593_ = lean_unbox(v___x_1582_);
v_res_1594_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(v___f_1581_, v___x_1614__boxed_1593_, v_fvarId_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore(lean_object* v_stx_1595_, uint8_t v_symm_1596_, lean_object* v_fvarId_1597_, lean_object* v_config_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___f_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; 
v___x_1608_ = lean_box(v_symm_1596_);
lean_inc(v_fvarId_1597_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1609_, 0, v_fvarId_1597_);
lean_closure_set(v___f_1609_, 1, v_stx_1595_);
lean_closure_set(v___f_1609_, 2, v___x_1608_);
lean_closure_set(v___f_1609_, 3, v_config_1598_);
v___x_1610_ = 1;
v___x_1611_ = lean_box(v___x_1610_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1612_, 0, v___f_1609_);
lean_closure_set(v___f_1612_, 1, v___x_1611_);
lean_closure_set(v___f_1612_, 2, v_fvarId_1597_);
v___x_1613_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1612_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___boxed(lean_object* v_stx_1614_, lean_object* v_symm_1615_, lean_object* v_fvarId_1616_, lean_object* v_config_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
uint8_t v_symm_boxed_1627_; lean_object* v_res_1628_; 
v_symm_boxed_1627_ = lean_unbox(v_symm_1615_);
v_res_1628_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1614_, v_symm_boxed_1627_, v_fvarId_1616_, v_config_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1629_, uint8_t v_symm_1630_, lean_object* v_fvarId_1631_, lean_object* v_config_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1629_, v_symm_1630_, v_fvarId_1631_, v_config_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1651_);
v___x_1644_ = v___x_1642_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v___x_1642_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(0);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1642_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1642_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1660_, lean_object* v_symm_1661_, lean_object* v_fvarId_1662_, lean_object* v_config_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
uint8_t v_symm_boxed_1673_; lean_object* v_res_1674_; 
v_symm_boxed_1673_ = lean_unbox(v_symm_1661_);
v_res_1674_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1660_, v_symm_boxed_1673_, v_fvarId_1662_, v_config_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1674_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(lean_object* v_x_1681_, lean_object* v_acc_1682_, uint8_t v_symm_1683_, lean_object* v_id_1684_, lean_object* v_declName_1685_, lean_object* v_hint_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
if (lean_obj_tag(v_a_1687_) == 0)
{
lean_object* v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v_acc_1682_);
lean_dec_ref(v_x_1681_);
v___x_1697_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1);
v___x_1698_ = 0;
v___x_1699_ = l_Lean_MessageData_ofConstName(v_declName_1685_, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1697_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_hint_1686_);
v___x_1704_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1703_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1704_;
}
else
{
lean_object* v_head_1705_; lean_object* v_tail_1706_; lean_object* v___x_1707_; 
v_head_1705_ = lean_ctor_get(v_a_1687_, 0);
lean_inc(v_head_1705_);
v_tail_1706_ = lean_ctor_get(v_a_1687_, 1);
lean_inc(v_tail_1706_);
lean_dec_ref_known(v_a_1687_, 2);
v___x_1707_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1689_, v_a_1691_, v_a_1693_, v_a_1695_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = 0;
v___x_1710_ = l_Lean_mkCIdentFrom(v_id_1684_, v_head_1705_, v___x_1709_);
v___x_1711_ = lean_box(v_symm_1683_);
lean_inc_ref(v_x_1681_);
lean_inc(v_acc_1682_);
v___x_1712_ = lean_apply_3(v_x_1681_, v_acc_1682_, v___x_1711_, v___x_1710_);
v___x_1713_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1712_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec(v_a_1708_);
lean_dec(v_tail_1706_);
lean_dec_ref(v_hint_1686_);
lean_dec(v_declName_1685_);
lean_dec(v_acc_1682_);
lean_dec_ref(v_x_1681_);
return v___x_1713_;
}
else
{
lean_object* v_a_1714_; uint8_t v___y_1716_; uint8_t v___x_1727_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
v___x_1727_ = l_Lean_Exception_isInterrupt(v_a_1714_);
if (v___x_1727_ == 0)
{
uint8_t v___x_1728_; 
v___x_1728_ = l_Lean_Exception_isRuntime(v_a_1714_);
v___y_1716_ = v___x_1728_;
goto v___jp_1715_;
}
else
{
lean_dec(v_a_1714_);
v___y_1716_ = v___x_1727_;
goto v___jp_1715_;
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1717_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1708_, v___y_1716_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_dec_ref_known(v___x_1717_, 1);
v_a_1687_ = v_tail_1706_;
goto _start;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_tail_1706_);
lean_dec_ref(v_hint_1686_);
lean_dec(v_declName_1685_);
lean_dec(v_acc_1682_);
lean_dec_ref(v_x_1681_);
v_a_1719_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1717_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_dec(v_a_1708_);
lean_dec(v_tail_1706_);
lean_dec_ref(v_hint_1686_);
lean_dec(v_declName_1685_);
lean_dec(v_acc_1682_);
lean_dec_ref(v_x_1681_);
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_tail_1706_);
lean_dec(v_head_1705_);
lean_dec_ref(v_hint_1686_);
lean_dec(v_declName_1685_);
lean_dec(v_acc_1682_);
lean_dec_ref(v_x_1681_);
v_a_1729_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1707_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1707_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___boxed(lean_object* v_x_1737_, lean_object* v_acc_1738_, lean_object* v_symm_1739_, lean_object* v_id_1740_, lean_object* v_declName_1741_, lean_object* v_hint_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
uint8_t v_symm_boxed_1753_; lean_object* v_res_1754_; 
v_symm_boxed_1753_ = lean_unbox(v_symm_1739_);
v_res_1754_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1737_, v_acc_1738_, v_symm_boxed_1753_, v_id_1740_, v_declName_1741_, v_hint_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_id_1740_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(lean_object* v_00_u03b1_1755_, lean_object* v_x_1756_, lean_object* v_acc_1757_, uint8_t v_symm_1758_, lean_object* v_id_1759_, lean_object* v_declName_1760_, lean_object* v_hint_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1756_, v_acc_1757_, v_symm_1758_, v_id_1759_, v_declName_1760_, v_hint_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___boxed(lean_object** _args){
lean_object* v_00_u03b1_1773_ = _args[0];
lean_object* v_x_1774_ = _args[1];
lean_object* v_acc_1775_ = _args[2];
lean_object* v_symm_1776_ = _args[3];
lean_object* v_id_1777_ = _args[4];
lean_object* v_declName_1778_ = _args[5];
lean_object* v_hint_1779_ = _args[6];
lean_object* v_a_1780_ = _args[7];
lean_object* v_a_1781_ = _args[8];
lean_object* v_a_1782_ = _args[9];
lean_object* v_a_1783_ = _args[10];
lean_object* v_a_1784_ = _args[11];
lean_object* v_a_1785_ = _args[12];
lean_object* v_a_1786_ = _args[13];
lean_object* v_a_1787_ = _args[14];
lean_object* v_a_1788_ = _args[15];
lean_object* v_a_1789_ = _args[16];
_start:
{
uint8_t v_symm_boxed_1790_; lean_object* v_res_1791_; 
v_symm_boxed_1790_ = lean_unbox(v_symm_1776_);
v_res_1791_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(v_00_u03b1_1773_, v_x_1774_, v_acc_1775_, v_symm_boxed_1790_, v_id_1777_, v_declName_1778_, v_hint_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_id_1777_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(lean_object* v_a_1792_, lean_object* v_trees_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
lean_inc(v___y_1801_);
lean_inc_ref(v___y_1800_);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
v___x_1803_ = lean_apply_9(v_a_1792_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, lean_box(0));
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1812_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1804_);
lean_ctor_set(v___x_1808_, 1, v_trees_1793_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1810_ = v___x_1806_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_trees_1793_);
v_a_1813_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1803_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1803_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed(lean_object* v_a_1821_, lean_object* v_trees_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(v_a_1821_, v_trees_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(lean_object* v___x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1833_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed(lean_object* v___x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(v___x_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1854_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_unsigned_to_nat(32u);
v___x_1856_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1858_ = ((size_t)5ULL);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_unsigned_to_nat(32u);
v___x_1861_ = lean_mk_empty_array_with_capacity(v___x_1860_);
v___x_1862_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1863_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___x_1861_);
lean_ctor_set(v___x_1863_, 2, v___x_1859_);
lean_ctor_set(v___x_1863_, 3, v___x_1859_);
lean_ctor_set_usize(v___x_1863_, 4, v___x_1858_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_infoState_1867_; lean_object* v_trees_1868_; lean_object* v___x_1869_; lean_object* v_infoState_1870_; lean_object* v_env_1871_; lean_object* v_nextMacroScope_1872_; lean_object* v_ngen_1873_; lean_object* v_auxDeclNGen_1874_; lean_object* v_traceState_1875_; lean_object* v_cache_1876_; lean_object* v_messages_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1899_; 
v___x_1866_ = lean_st_ref_get(v___y_1864_);
v_infoState_1867_ = lean_ctor_get(v___x_1866_, 7);
lean_inc_ref(v_infoState_1867_);
lean_dec(v___x_1866_);
v_trees_1868_ = lean_ctor_get(v_infoState_1867_, 2);
lean_inc_ref(v_trees_1868_);
lean_dec_ref(v_infoState_1867_);
v___x_1869_ = lean_st_ref_take(v___y_1864_);
v_infoState_1870_ = lean_ctor_get(v___x_1869_, 7);
v_env_1871_ = lean_ctor_get(v___x_1869_, 0);
v_nextMacroScope_1872_ = lean_ctor_get(v___x_1869_, 1);
v_ngen_1873_ = lean_ctor_get(v___x_1869_, 2);
v_auxDeclNGen_1874_ = lean_ctor_get(v___x_1869_, 3);
v_traceState_1875_ = lean_ctor_get(v___x_1869_, 4);
v_cache_1876_ = lean_ctor_get(v___x_1869_, 5);
v_messages_1877_ = lean_ctor_get(v___x_1869_, 6);
v_snapshotTasks_1878_ = lean_ctor_get(v___x_1869_, 8);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1880_ = v___x_1869_;
v_isShared_1881_ = v_isSharedCheck_1899_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snapshotTasks_1878_);
lean_inc(v_infoState_1870_);
lean_inc(v_messages_1877_);
lean_inc(v_cache_1876_);
lean_inc(v_traceState_1875_);
lean_inc(v_auxDeclNGen_1874_);
lean_inc(v_ngen_1873_);
lean_inc(v_nextMacroScope_1872_);
lean_inc(v_env_1871_);
lean_dec(v___x_1869_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1899_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
uint8_t v_enabled_1882_; lean_object* v_assignment_1883_; lean_object* v_lazyAssignment_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1897_; 
v_enabled_1882_ = lean_ctor_get_uint8(v_infoState_1870_, sizeof(void*)*3);
v_assignment_1883_ = lean_ctor_get(v_infoState_1870_, 0);
v_lazyAssignment_1884_ = lean_ctor_get(v_infoState_1870_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_infoState_1870_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_infoState_1870_, 2);
lean_dec(v_unused_1898_);
v___x_1886_ = v_infoState_1870_;
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_lazyAssignment_1884_);
lean_inc(v_assignment_1883_);
lean_dec(v_infoState_1870_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 2, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_assignment_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_lazyAssignment_1884_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___x_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*3, v_enabled_1882_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 7, v___x_1890_);
v___x_1892_ = v___x_1880_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_env_1871_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_nextMacroScope_1872_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_ngen_1873_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_auxDeclNGen_1874_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_traceState_1875_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_cache_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_messages_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_snapshotTasks_1878_);
v___x_1892_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_st_ref_put(v___y_1864_, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_trees_1868_);
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1900_);
lean_dec(v___y_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1903_, lean_object* v_mkInfoTree_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v_a_1912_, lean_object* v_a_x3f_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_infoState_1916_; lean_object* v_trees_1917_; lean_object* v___x_1918_; 
v___x_1915_ = lean_st_ref_get(v___y_1903_);
v_infoState_1916_ = lean_ctor_get(v___x_1915_, 7);
lean_inc_ref(v_infoState_1916_);
lean_dec(v___x_1915_);
v_trees_1917_ = lean_ctor_get(v_infoState_1916_, 2);
lean_inc_ref(v_trees_1917_);
lean_dec_ref(v_infoState_1916_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
v___x_1918_ = lean_apply_10(v_mkInfoTree_1904_, v_trees_1917_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1903_, lean_box(0));
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1957_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1957_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1957_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v_infoState_1924_; lean_object* v_env_1925_; lean_object* v_nextMacroScope_1926_; lean_object* v_ngen_1927_; lean_object* v_auxDeclNGen_1928_; lean_object* v_traceState_1929_; lean_object* v_cache_1930_; lean_object* v_messages_1931_; lean_object* v_snapshotTasks_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1956_; 
v___x_1923_ = lean_st_ref_take(v___y_1903_);
v_infoState_1924_ = lean_ctor_get(v___x_1923_, 7);
v_env_1925_ = lean_ctor_get(v___x_1923_, 0);
v_nextMacroScope_1926_ = lean_ctor_get(v___x_1923_, 1);
v_ngen_1927_ = lean_ctor_get(v___x_1923_, 2);
v_auxDeclNGen_1928_ = lean_ctor_get(v___x_1923_, 3);
v_traceState_1929_ = lean_ctor_get(v___x_1923_, 4);
v_cache_1930_ = lean_ctor_get(v___x_1923_, 5);
v_messages_1931_ = lean_ctor_get(v___x_1923_, 6);
v_snapshotTasks_1932_ = lean_ctor_get(v___x_1923_, 8);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1934_ = v___x_1923_;
v_isShared_1935_ = v_isSharedCheck_1956_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snapshotTasks_1932_);
lean_inc(v_infoState_1924_);
lean_inc(v_messages_1931_);
lean_inc(v_cache_1930_);
lean_inc(v_traceState_1929_);
lean_inc(v_auxDeclNGen_1928_);
lean_inc(v_ngen_1927_);
lean_inc(v_nextMacroScope_1926_);
lean_inc(v_env_1925_);
lean_dec(v___x_1923_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1956_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint8_t v_enabled_1936_; lean_object* v_assignment_1937_; lean_object* v_lazyAssignment_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1954_; 
v_enabled_1936_ = lean_ctor_get_uint8(v_infoState_1924_, sizeof(void*)*3);
v_assignment_1937_ = lean_ctor_get(v_infoState_1924_, 0);
v_lazyAssignment_1938_ = lean_ctor_get(v_infoState_1924_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_infoState_1924_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v_infoState_1924_, 2);
lean_dec(v_unused_1955_);
v___x_1940_ = v_infoState_1924_;
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_lazyAssignment_1938_);
lean_inc(v_assignment_1937_);
lean_dec(v_infoState_1924_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = l_Lean_PersistentArray_push___redArg(v_a_1912_, v_a_1919_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 2, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_assignment_1937_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_lazyAssignment_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3, v_enabled_1936_);
v___x_1944_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 7, v___x_1944_);
v___x_1946_ = v___x_1934_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_env_1925_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_nextMacroScope_1926_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_ngen_1927_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_auxDeclNGen_1928_);
lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_traceState_1929_);
lean_ctor_set(v_reuseFailAlloc_1952_, 5, v_cache_1930_);
lean_ctor_set(v_reuseFailAlloc_1952_, 6, v_messages_1931_);
lean_ctor_set(v_reuseFailAlloc_1952_, 7, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1952_, 8, v_snapshotTasks_1932_);
v___x_1946_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1947_ = lean_st_ref_put(v___y_1903_, v___x_1946_);
v___x_1948_ = lean_box(0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1948_);
v___x_1950_ = v___x_1921_;
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
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_a_1912_);
v_a_1958_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1918_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1918_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1966_, lean_object* v_mkInfoTree_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v_a_1975_, lean_object* v_a_x3f_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1966_, v_mkInfoTree_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v_a_1975_, v_a_x3f_1976_);
lean_dec(v_a_x3f_1976_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1966_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(lean_object* v_x_1979_, lean_object* v_mkInfoTree_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_infoState_1991_; uint8_t v_enabled_1992_; 
v___x_1990_ = lean_st_ref_get(v___y_1988_);
v_infoState_1991_ = lean_ctor_get(v___x_1990_, 7);
lean_inc_ref(v_infoState_1991_);
lean_dec(v___x_1990_);
v_enabled_1992_ = lean_ctor_get_uint8(v_infoState_1991_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1991_);
if (v_enabled_1992_ == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref(v_mkInfoTree_1980_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
v___x_1993_ = lean_apply_9(v_x_1979_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, lean_box(0));
return v___x_1993_;
}
else
{
lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v_r_1996_; 
v___x_1994_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1988_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
v_r_1996_ = lean_apply_9(v_x_1979_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, lean_box(0));
if (lean_obj_tag(v_r_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2021_; 
v_a_1997_ = lean_ctor_get(v_r_1996_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_r_1996_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1999_ = v_r_1996_;
v_isShared_2000_ = v_isSharedCheck_2021_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v_r_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2021_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
lean_inc(v_a_1997_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 1);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1988_, v_mkInfoTree_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v_a_1995_, v___x_2002_);
lean_dec_ref(v___x_2002_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_2003_, 0);
lean_dec(v_unused_2011_);
v___x_2005_ = v___x_2003_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v___x_2003_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_a_1997_);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_1997_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_a_1997_);
v_a_2012_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2003_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2003_);
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
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_a_2022_ = lean_ctor_get(v_r_1996_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v_r_1996_, 1);
v___x_2023_ = lean_box(0);
v___x_2024_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1988_, v_mkInfoTree_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v_a_1995_, v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v___x_2024_, 0);
lean_dec(v_unused_2032_);
v___x_2026_ = v___x_2024_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v___x_2024_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 1);
lean_ctor_set(v___x_2026_, 0, v_a_2022_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2022_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_2022_);
v_a_2033_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_2041_, lean_object* v_mkInfoTree_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2041_, v_mkInfoTree_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_2062_, uint8_t v___x_2063_, lean_object* v___x_2064_, lean_object* v_x_2065_, lean_object* v_b_2066_, uint8_t v___y_2067_, lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v___f_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_toCold_2080_; lean_object* v_currRecDepth_2081_; lean_object* v_ref_2082_; uint8_t v_diag_2083_; uint8_t v_suppressElabErrors_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2102_; 
v_toCold_2080_ = lean_ctor_get(v___y_2077_, 0);
v_currRecDepth_2081_ = lean_ctor_get(v___y_2077_, 1);
v_ref_2082_ = lean_ctor_get(v___y_2077_, 2);
v_diag_2083_ = lean_ctor_get_uint8(v___y_2077_, sizeof(void*)*3);
v_suppressElabErrors_2084_ = lean_ctor_get_uint8(v___y_2077_, sizeof(void*)*3 + 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___y_2077_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2086_ = v___y_2077_;
v_isShared_2087_ = v_isSharedCheck_2102_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_ref_2082_);
lean_inc(v_currRecDepth_2081_);
lean_inc(v_toCold_2080_);
lean_dec(v___y_2077_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2102_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_ref_2088_; lean_object* v___x_2090_; 
v_ref_2088_ = l_Lean_replaceRef(v___x_2062_, v_ref_2082_);
lean_dec(v_ref_2082_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 2, v_ref_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_toCold_2080_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_currRecDepth_2081_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_ref_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*3, v_diag_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*3 + 1, v_suppressElabErrors_2084_);
v___x_2090_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
if (v___x_2063_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_2064_);
v___x_2092_ = l_Lean_Syntax_isOfKind(v___x_2064_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec_ref(v___f_2070_);
v___x_2093_ = lean_box(v___y_2067_);
v___x_2094_ = lean_apply_12(v_x_2065_, v_b_2066_, v___x_2093_, v___x_2064_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___x_2090_, v___y_2078_, lean_box(0));
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = l_Lean_Syntax_getArg(v___x_2064_, v___x_2068_);
lean_inc(v___x_2095_);
v___x_2096_ = l_Lean_Syntax_isOfKind(v___x_2095_, v___x_2069_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v___x_2095_);
lean_dec_ref(v___f_2070_);
v___x_2097_ = lean_box(v___y_2067_);
v___x_2098_ = lean_apply_12(v_x_2065_, v_b_2066_, v___x_2097_, v___x_2064_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___x_2090_, v___y_2078_, lean_box(0));
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_b_2066_);
lean_dec_ref(v_x_2065_);
lean_dec(v___x_2064_);
v___x_2099_ = lean_apply_10(v___f_2070_, v___x_2095_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___x_2090_, v___y_2078_, lean_box(0));
return v___x_2099_;
}
}
}
else
{
lean_object* v___x_2100_; 
lean_dec(v_b_2066_);
lean_dec_ref(v_x_2065_);
v___x_2100_ = lean_apply_10(v___f_2070_, v___x_2064_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___x_2090_, v___y_2078_, lean_box(0));
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2103_ = _args[0];
lean_object* v___x_2104_ = _args[1];
lean_object* v___x_2105_ = _args[2];
lean_object* v_x_2106_ = _args[3];
lean_object* v_b_2107_ = _args[4];
lean_object* v___y_2108_ = _args[5];
lean_object* v___x_2109_ = _args[6];
lean_object* v___x_2110_ = _args[7];
lean_object* v___f_2111_ = _args[8];
lean_object* v___y_2112_ = _args[9];
lean_object* v___y_2113_ = _args[10];
lean_object* v___y_2114_ = _args[11];
lean_object* v___y_2115_ = _args[12];
lean_object* v___y_2116_ = _args[13];
lean_object* v___y_2117_ = _args[14];
lean_object* v___y_2118_ = _args[15];
lean_object* v___y_2119_ = _args[16];
lean_object* v___y_2120_ = _args[17];
_start:
{
uint8_t v___x_15826__boxed_2121_; uint8_t v___y_15828__boxed_2122_; lean_object* v_res_2123_; 
v___x_15826__boxed_2121_ = lean_unbox(v___x_2104_);
v___y_15828__boxed_2122_ = lean_unbox(v___y_2108_);
v_res_2123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(v___x_2103_, v___x_15826__boxed_2121_, v___x_2105_, v_x_2106_, v_b_2107_, v___y_15828__boxed_2122_, v___x_2109_, v___x_2110_, v___f_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___x_2110_);
lean_dec(v___x_2109_);
lean_dec(v___x_2103_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2124_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(v_id_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2145_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_2152_, lean_object* v_b_2153_, uint8_t v___y_2154_, lean_object* v___x_2155_, lean_object* v___x_2156_, lean_object* v_id_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___f_2167_; lean_object* v___x_2168_; 
lean_inc(v_id_2157_);
v___f_2167_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2167_, 0, v_id_2157_);
v___x_2168_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2167_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
if (lean_obj_tag(v_a_2169_) == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2159_, v___y_2161_, v___y_2163_, v___y_2165_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
lean_inc(v_id_2157_);
v___x_2172_ = l_Lean_realizeGlobalConstNoOverload(v_id_2157_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; 
lean_dec(v_a_2171_);
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_n(v_a_2173_, 2);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2173_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v___x_2156_);
v_val_2176_ = lean_ctor_get(v_a_2175_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2178_ = v_a_2175_;
v_isShared_2179_ = v_isSharedCheck_2220_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_val_2176_);
lean_dec(v_a_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2220_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint8_t v___x_2180_; lean_object* v___y_2182_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2180_ = 0;
v___x_2209_ = lean_array_get_size(v_val_2176_);
v___x_2210_ = lean_nat_dec_eq(v___x_2209_, v___x_2155_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2211_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_2212_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2173_);
v___x_2213_ = l_Lean_Name_str___override(v_a_2173_, v___x_2212_);
v___x_2214_ = l_Lean_MessageData_ofName(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2211_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_2217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = l_Lean_MessageData_hint_x27(v___x_2217_);
v___y_2182_ = v___x_2218_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2182_ = v___x_2219_;
goto v___jp_2181_;
}
v___jp_2181_:
{
lean_object* v___x_2183_; 
lean_inc(v_a_2173_);
v___x_2183_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2173_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_lctx_2185_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_lctx_2185_ = lean_ctor_get(v___y_2162_, 2);
lean_inc_ref(v_lctx_2185_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v_lctx_2185_);
v___x_2187_ = v___x_2178_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_lctx_2185_);
v___x_2187_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_box(0);
lean_inc(v_id_2157_);
v___x_2189_ = l_Lean_Elab_Term_addTermInfo(v_id_2157_, v_a_2184_, v_a_2169_, v___x_2187_, v___x_2188_, v___x_2180_, v___x_2180_, v___x_2180_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref_known(v___x_2189_, 1);
v___x_2190_ = lean_array_to_list(v_val_2176_);
v___x_2191_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_2152_, v_b_2153_, v___y_2154_, v_id_2157_, v_a_2173_, v___y_2182_, v___x_2190_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v_id_2157_);
return v___x_2191_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v___y_2182_);
lean_dec(v_val_2176_);
lean_dec(v_a_2173_);
lean_dec(v_id_2157_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2192_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2189_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2189_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v___y_2182_);
lean_del_object(v___x_2178_);
lean_dec(v_val_2176_);
lean_dec(v_a_2173_);
lean_dec(v_id_2157_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2201_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2183_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2183_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2173_);
lean_dec(v_id_2157_);
v___x_2221_ = lean_box(v___y_2154_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___y_2161_);
lean_inc_ref(v___y_2160_);
lean_inc(v___y_2159_);
lean_inc_ref(v___y_2158_);
v___x_2222_ = lean_apply_12(v_x_2152_, v_b_2153_, v___x_2221_, v___x_2156_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, lean_box(0));
return v___x_2222_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2173_);
lean_dec(v_id_2157_);
lean_dec(v___x_2156_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2223_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2174_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2174_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_id_2157_);
v_a_2231_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2233_ = v___x_2172_;
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2172_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v___y_2236_; uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_Exception_isInterrupt(v_a_2231_);
if (v___x_2251_ == 0)
{
uint8_t v___x_2252_; 
lean_inc(v_a_2231_);
v___x_2252_ = l_Lean_Exception_isRuntime(v_a_2231_);
v___y_2236_ = v___x_2252_;
goto v___jp_2235_;
}
else
{
v___y_2236_ = v___x_2251_;
goto v___jp_2235_;
}
v___jp_2235_:
{
if (v___y_2236_ == 0)
{
lean_object* v___x_2237_; 
lean_del_object(v___x_2233_);
lean_dec(v_a_2231_);
v___x_2237_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2171_, v___y_2236_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref_known(v___x_2237_, 1);
v___x_2238_ = lean_box(v___y_2154_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___y_2161_);
lean_inc_ref(v___y_2160_);
lean_inc(v___y_2159_);
lean_inc_ref(v___y_2158_);
v___x_2239_ = lean_apply_12(v_x_2152_, v_b_2153_, v___x_2238_, v___x_2156_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, lean_box(0));
return v___x_2239_;
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___x_2156_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2240_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2237_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2237_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v___x_2249_; 
lean_dec(v_a_2171_);
lean_dec(v___x_2156_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
if (v_isShared_2234_ == 0)
{
v___x_2249_ = v___x_2233_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2231_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_id_2157_);
lean_dec(v___x_2156_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2254_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2170_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2170_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref_known(v_a_2169_, 1);
lean_dec(v_id_2157_);
v___x_2262_ = lean_box(v___y_2154_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___y_2161_);
lean_inc_ref(v___y_2160_);
lean_inc(v___y_2159_);
lean_inc_ref(v___y_2158_);
v___x_2263_ = lean_apply_12(v_x_2152_, v_b_2153_, v___x_2262_, v___x_2156_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, lean_box(0));
return v___x_2263_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_id_2157_);
lean_dec(v___x_2156_);
lean_dec(v_b_2153_);
lean_dec_ref(v_x_2152_);
v_a_2264_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2168_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2168_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___x_2275_, lean_object* v___x_2276_, lean_object* v_id_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v___y_15960__boxed_2287_; lean_object* v_res_2288_; 
v___y_15960__boxed_2287_ = lean_unbox(v___y_2274_);
v_res_2288_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(v_x_2272_, v_b_2273_, v___y_15960__boxed_2287_, v___x_2275_, v___x_2276_, v_id_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___x_2275_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_2289_, lean_object* v_trees_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
v___x_2300_ = lean_apply_9(v_a_2289_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, lean_box(0));
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2309_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2301_);
lean_ctor_set(v___x_2305_, 1, v_trees_2290_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2305_);
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_trees_2290_);
v_a_2310_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2300_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2300_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_2318_, lean_object* v_trees_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(v_a_2318_, v_trees_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2336_, lean_object* v_rules_2337_, lean_object* v_x_2338_, lean_object* v_a_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_nat_dec_lt(v_a_2339_, v_upperBound_2336_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec(v_a_2339_);
lean_dec_ref(v_x_2338_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_b_2340_);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___y_2359_; uint8_t v___y_2360_; lean_object* v___y_2385_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2352_ = lean_unsigned_to_nat(2u);
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_nat_mul(v_a_2339_, v___x_2352_);
v___x_2357_ = lean_array_get_borrowed(v___x_2353_, v_rules_2337_, v___x_2356_);
v___x_2395_ = lean_nat_add(v___x_2356_, v___x_2354_);
lean_dec(v___x_2356_);
v___x_2396_ = lean_array_get_size(v_rules_2337_);
v___x_2397_ = lean_nat_dec_lt(v___x_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_dec(v___x_2395_);
v___y_2385_ = v___x_2353_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_array_fget_borrowed(v_rules_2337_, v___x_2395_);
lean_dec(v___x_2395_);
lean_inc(v___x_2398_);
v___y_2385_ = v___x_2398_;
goto v___jp_2384_;
}
v___jp_2358_:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2359_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___f_2363_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2363_, 0, v_a_2362_);
v___x_2364_ = l_Lean_Syntax_getArg(v___x_2357_, v___x_2354_);
v___x_2365_ = lean_box(v___y_2360_);
lean_inc_n(v___x_2364_, 2);
lean_inc(v_b_2340_);
lean_inc_ref_n(v_x_2338_, 2);
v___f_2366_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed), 15, 5);
lean_closure_set(v___f_2366_, 0, v_x_2338_);
lean_closure_set(v___f_2366_, 1, v_b_2340_);
lean_closure_set(v___f_2366_, 2, v___x_2365_);
lean_closure_set(v___f_2366_, 3, v___x_2354_);
lean_closure_set(v___f_2366_, 4, v___x_2364_);
v___x_2367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1));
v___x_2368_ = l_Lean_Syntax_isOfKind(v___x_2364_, v___x_2367_);
v___x_2369_ = lean_box(v___x_2368_);
v___x_2370_ = lean_box(v___y_2360_);
lean_inc(v___x_2357_);
v___f_2371_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed), 18, 9);
lean_closure_set(v___f_2371_, 0, v___x_2357_);
lean_closure_set(v___f_2371_, 1, v___x_2369_);
lean_closure_set(v___f_2371_, 2, v___x_2364_);
lean_closure_set(v___f_2371_, 3, v_x_2338_);
lean_closure_set(v___f_2371_, 4, v_b_2340_);
lean_closure_set(v___f_2371_, 5, v___x_2370_);
lean_closure_set(v___f_2371_, 6, v___x_2354_);
lean_closure_set(v___f_2371_, 7, v___x_2367_);
lean_closure_set(v___f_2371_, 8, v___f_2366_);
v___x_2372_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2371_, v___f_2363_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = lean_nat_add(v_a_2339_, v___x_2354_);
lean_dec(v_a_2339_);
v_a_2339_ = v___x_2374_;
v_b_2340_ = v_a_2373_;
goto _start;
}
else
{
lean_dec(v_a_2339_);
lean_dec_ref(v_x_2338_);
return v___x_2372_;
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_b_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_x_2338_);
v_a_2376_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2361_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2361_);
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
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2386_ = lean_mk_empty_array_with_capacity(v___x_2352_);
lean_inc(v___x_2357_);
v___x_2387_ = lean_array_push(v___x_2386_, v___x_2357_);
v___x_2388_ = lean_array_push(v___x_2387_, v___y_2385_);
v___x_2389_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2390_ = lean_box(2);
v___x_2391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2389_);
lean_ctor_set(v___x_2391_, 2, v___x_2388_);
v___x_2392_ = l_Lean_Syntax_getArg(v___x_2357_, v___x_2355_);
v___x_2393_ = l_Lean_Syntax_isNone(v___x_2392_);
lean_dec(v___x_2392_);
if (v___x_2393_ == 0)
{
v___y_2359_ = v___x_2391_;
v___y_2360_ = v___x_2350_;
goto v___jp_2358_;
}
else
{
uint8_t v___x_2394_; 
v___x_2394_ = 0;
v___y_2359_ = v___x_2391_;
v___y_2360_ = v___x_2394_;
goto v___jp_2358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2399_, lean_object* v_rules_2400_, lean_object* v_x_2401_, lean_object* v_a_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2399_, v_rules_2400_, v_x_2401_, v_a_2402_, v_b_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_rules_2400_);
lean_dec(v_upperBound_2399_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(lean_object* v_token_2416_, lean_object* v_rwRulesSeqStx_2417_, lean_object* v_init_2418_, lean_object* v_x_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v_lbrak_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2429_ = lean_unsigned_to_nat(0u);
v_lbrak_2430_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2417_, v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(2u);
v___x_2432_ = lean_mk_empty_array_with_capacity(v___x_2431_);
v___x_2433_ = lean_array_push(v___x_2432_, v_token_2416_);
v___x_2434_ = lean_array_push(v___x_2433_, v_lbrak_2430_);
v___x_2435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2436_ = lean_box(2);
v___x_2437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v___x_2435_);
lean_ctor_set(v___x_2437_, 2, v___x_2434_);
v___x_2438_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2437_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2440_, 0, v_a_2439_);
v___f_2441_ = ((lean_object*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0));
v___x_2442_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2441_, v___f_2440_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_rules_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec_ref_known(v___x_2442_, 1);
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2417_, v___x_2443_);
v_rules_2445_ = l_Lean_Syntax_getArgs(v___x_2444_);
lean_dec(v___x_2444_);
v___x_2446_ = lean_array_get_size(v_rules_2445_);
v___x_2447_ = lean_nat_add(v___x_2446_, v___x_2443_);
v___x_2448_ = lean_nat_shiftr(v___x_2447_, v___x_2443_);
lean_dec(v___x_2447_);
v___x_2449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v___x_2448_, v_rules_2445_, v_x_2419_, v___x_2429_, v_init_2418_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
lean_dec_ref(v_rules_2445_);
lean_dec(v___x_2448_);
return v___x_2449_;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v_x_2419_);
lean_dec(v_init_2418_);
v_a_2450_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2442_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2442_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v_x_2419_);
lean_dec(v_init_2418_);
v_a_2458_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2438_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2438_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___boxed(lean_object* v_token_2466_, lean_object* v_rwRulesSeqStx_2467_, lean_object* v_init_2468_, lean_object* v_x_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2466_, v_rwRulesSeqStx_2467_, v_init_2468_, v_x_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_rwRulesSeqStx_2467_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq(lean_object* v_00_u03b1_2480_, lean_object* v_token_2481_, lean_object* v_rwRulesSeqStx_2482_, lean_object* v_init_2483_, lean_object* v_x_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2481_, v_rwRulesSeqStx_2482_, v_init_2483_, v_x_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___boxed(lean_object* v_00_u03b1_2495_, lean_object* v_token_2496_, lean_object* v_rwRulesSeqStx_2497_, lean_object* v_init_2498_, lean_object* v_x_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Elab_Tactic_foldRWRulesSeq(v_00_u03b1_2495_, v_token_2496_, v_rwRulesSeqStx_2497_, v_init_2498_, v_x_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_rwRulesSeqStx_2497_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(lean_object* v_00_u03b1_2530_, lean_object* v_x_2531_, lean_object* v_mkInfoTree_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2531_, v_mkInfoTree_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_x_2544_, lean_object* v_mkInfoTree_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(v_00_u03b1_2543_, v_x_2544_, v_mkInfoTree_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(lean_object* v_00_u03b1_2556_, lean_object* v_upperBound_2557_, lean_object* v_rules_2558_, lean_object* v_x_2559_, lean_object* v_inst_2560_, lean_object* v_R_2561_, lean_object* v_a_2562_, lean_object* v_b_2563_, lean_object* v_c_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2557_, v_rules_2558_, v_x_2559_, v_a_2562_, v_b_2563_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_2575_ = _args[0];
lean_object* v_upperBound_2576_ = _args[1];
lean_object* v_rules_2577_ = _args[2];
lean_object* v_x_2578_ = _args[3];
lean_object* v_inst_2579_ = _args[4];
lean_object* v_R_2580_ = _args[5];
lean_object* v_a_2581_ = _args[6];
lean_object* v_b_2582_ = _args[7];
lean_object* v_c_2583_ = _args[8];
lean_object* v___y_2584_ = _args[9];
lean_object* v___y_2585_ = _args[10];
lean_object* v___y_2586_ = _args[11];
lean_object* v___y_2587_ = _args[12];
lean_object* v___y_2588_ = _args[13];
lean_object* v___y_2589_ = _args[14];
lean_object* v___y_2590_ = _args[15];
lean_object* v___y_2591_ = _args[16];
lean_object* v___y_2592_ = _args[17];
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(v_00_u03b1_2575_, v_upperBound_2576_, v_rules_2577_, v_x_2578_, v_inst_2579_, v_R_2580_, v_a_2581_, v_b_2582_, v_c_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_rules_2577_);
lean_dec(v_upperBound_2576_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_x_2594_, lean_object* v_x_2595_, uint8_t v_symm_2596_, lean_object* v_term_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_box(v_symm_2596_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
v___x_2608_ = lean_apply_11(v_x_2594_, v___x_2607_, v_term_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, lean_box(0));
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_x_2609_, lean_object* v_x_2610_, lean_object* v_symm_2611_, lean_object* v_term_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v_symm_boxed_2622_; lean_object* v_res_2623_; 
v_symm_boxed_2622_ = lean_unbox(v_symm_2611_);
v_res_2623_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_x_2609_, v_x_2610_, v_symm_boxed_2622_, v_term_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2624_, lean_object* v_rwRulesSeqStx_2625_, lean_object* v_x_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2636_, 0, v_x_2626_);
v___x_2637_ = lean_box(0);
v___x_2638_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2624_, v_rwRulesSeqStx_2625_, v___x_2637_, v___f_2636_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2638_, 0);
lean_dec(v_unused_2646_);
v___x_2640_ = v___x_2638_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v___x_2638_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2637_);
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2637_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2647_, lean_object* v_rwRulesSeqStx_2648_, lean_object* v_x_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2647_, v_rwRulesSeqStx_2648_, v_x_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_rwRulesSeqStx_2648_);
return v_res_2659_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_ref_2688_; lean_object* v___x_2689_; lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2698_; 
v_ref_2688_ = lean_ctor_get(v___y_2685_, 2);
v___x_2689_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
lean_inc(v_ref_2688_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_ref_2688_);
lean_ctor_set(v___x_2694_, 1, v_a_2690_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2694_);
v___x_2696_ = v___x_2692_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2709_ = l_Lean_stringToMessageData(v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_2710_, lean_object* v_ctor_2711_, lean_object* v_args_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2779_ = lean_string_dec_eq(v_ctor_2711_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2781_ = lean_array_get_size(v_args_2712_);
v___x_2782_ = lean_unsigned_to_nat(4u);
v___x_2783_ = lean_nat_dec_eq(v___x_2781_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2785_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2784_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
goto v___jp_2718_;
}
}
v___jp_2718_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_unsigned_to_nat(0u);
v___x_2720_ = lean_array_get_borrowed(v___x_2710_, v_args_2712_, v___x_2719_);
lean_inc(v___x_2720_);
v___x_2721_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2720_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2723_ = lean_unsigned_to_nat(1u);
v___x_2724_ = lean_array_get_borrowed(v___x_2710_, v_args_2712_, v___x_2723_);
lean_inc(v___x_2724_);
v___x_2725_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2724_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = lean_unsigned_to_nat(2u);
v___x_2728_ = lean_array_get_borrowed(v___x_2710_, v_args_2712_, v___x_2727_);
lean_inc(v___x_2728_);
v___x_2729_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2728_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = lean_unsigned_to_nat(3u);
v___x_2732_ = lean_array_get_borrowed(v___x_2710_, v_args_2712_, v___x_2731_);
lean_inc(v___x_2732_);
v___x_2733_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2732_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; uint8_t v___x_2739_; uint8_t v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2743_; 
v___x_2738_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2738_, 0, v_a_2730_);
v___x_2739_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*1, v___x_2739_);
v___x_2740_ = lean_unbox(v_a_2726_);
lean_dec(v_a_2726_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*1 + 1, v___x_2740_);
v___x_2741_ = lean_unbox(v_a_2734_);
lean_dec(v_a_2734_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*1 + 2, v___x_2741_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2738_);
v___x_2743_ = v___x_2736_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2730_);
lean_dec(v_a_2726_);
lean_dec(v_a_2722_);
v_a_2746_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2733_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2733_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2726_);
lean_dec(v_a_2722_);
v_a_2754_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2729_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2729_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2722_);
v_a_2762_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2725_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2725_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_a_2770_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2721_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2721_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_2794_, lean_object* v_ctor_2795_, lean_object* v_args_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v___x_2794_, v_ctor_2795_, v_args_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_args_2796_);
lean_dec_ref(v_ctor_2795_);
lean_dec_ref(v___x_2794_);
return v_res_2802_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___f_2804_; 
v___x_2803_ = l_Lean_instInhabitedExpr;
v___f_2804_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2804_, 0, v___x_2803_);
return v___f_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___f_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___f_2819_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0);
v___x_2820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2821_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2820_, v___f_2819_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2829_, lean_object* v_msg_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_msg_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2837_, v_msg_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2844_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_box(0);
v___x_2847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2848_ = l_Lean_Expr_const___override(v___x_2847_, v___x_2846_);
return v___x_2848_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2851_);
return v___x_2853_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2854_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_box(1);
v___x_2856_ = l_Lean_MessageData_ofFormat(v___x_2855_);
return v___x_2856_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2861_ = l_Lean_MessageData_ofFormat(v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2862_, lean_object* v_x_2863_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
return v_x_2862_;
}
else
{
lean_object* v_head_2864_; lean_object* v_tail_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2887_; 
v_head_2864_ = lean_ctor_get(v_x_2863_, 0);
v_tail_2865_ = lean_ctor_get(v_x_2863_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2863_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2867_ = v_x_2863_;
v_isShared_2868_ = v_isSharedCheck_2887_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_tail_2865_);
lean_inc(v_head_2864_);
lean_dec(v_x_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2887_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v_before_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2885_; 
v_before_2869_ = lean_ctor_get(v_head_2864_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_head_2864_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v_head_2864_, 1);
lean_dec(v_unused_2886_);
v___x_2871_ = v_head_2864_;
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_before_2869_);
lean_dec(v_head_2864_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 7);
lean_ctor_set(v___x_2871_, 1, v___x_2873_);
lean_ctor_set(v___x_2871_, 0, v_x_2862_);
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_x_2862_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 7);
lean_ctor_set(v___x_2867_, 1, v___x_2876_);
lean_ctor_set(v___x_2867_, 0, v___x_2875_);
v___x_2878_ = v___x_2867_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = l_Lean_MessageData_ofSyntax(v_before_2869_);
v___x_2880_ = l_Lean_indentD(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v_x_2862_ = v___x_2881_;
v_x_2863_ = v_tail_2865_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2888_, lean_object* v_opt_2889_){
_start:
{
lean_object* v_name_2890_; lean_object* v_defValue_2891_; lean_object* v_map_2892_; lean_object* v___x_2893_; 
v_name_2890_ = lean_ctor_get(v_opt_2889_, 0);
v_defValue_2891_ = lean_ctor_get(v_opt_2889_, 1);
v_map_2892_ = lean_ctor_get(v_opts_2888_, 0);
v___x_2893_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2892_, v_name_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
uint8_t v___x_2894_; 
v___x_2894_ = lean_unbox(v_defValue_2891_);
return v___x_2894_;
}
else
{
lean_object* v_val_2895_; 
v_val_2895_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_val_2895_);
lean_dec_ref_known(v___x_2893_, 1);
if (lean_obj_tag(v_val_2895_) == 1)
{
uint8_t v_v_2896_; 
v_v_2896_ = lean_ctor_get_uint8(v_val_2895_, 0);
lean_dec_ref_known(v_val_2895_, 0);
return v_v_2896_;
}
else
{
uint8_t v___x_2897_; 
lean_dec(v_val_2895_);
v___x_2897_ = lean_unbox(v_defValue_2891_);
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2898_, lean_object* v_opt_2899_){
_start:
{
uint8_t v_res_2900_; lean_object* v_r_2901_; 
v_res_2900_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2898_, v_opt_2899_);
lean_dec_ref(v_opt_2899_);
lean_dec_ref(v_opts_2898_);
v_r_2901_ = lean_box(v_res_2900_);
return v_r_2901_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2906_ = l_Lean_MessageData_ofFormat(v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2907_, lean_object* v_macroStack_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_toCold_2911_; lean_object* v_options_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_toCold_2911_ = lean_ctor_get(v___y_2909_, 0);
v_options_2912_ = lean_ctor_get(v_toCold_2911_, 2);
v___x_2913_ = l_Lean_Elab_pp_macroStack;
v___x_2914_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_2912_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_dec(v_macroStack_2908_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_msgData_2907_);
return v___x_2915_;
}
else
{
if (lean_obj_tag(v_macroStack_2908_) == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_msgData_2907_);
return v___x_2916_;
}
else
{
lean_object* v_head_2917_; lean_object* v_after_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2933_; 
v_head_2917_ = lean_ctor_get(v_macroStack_2908_, 0);
lean_inc(v_head_2917_);
v_after_2918_ = lean_ctor_get(v_head_2917_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_head_2917_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v_head_2917_, 0);
lean_dec(v_unused_2934_);
v___x_2920_ = v_head_2917_;
v_isShared_2921_ = v_isSharedCheck_2933_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_after_2918_);
lean_dec(v_head_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2933_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 7);
lean_ctor_set(v___x_2920_, 1, v___x_2922_);
lean_ctor_set(v___x_2920_, 0, v_msgData_2907_);
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_msgData_2907_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v_msgData_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2925_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = l_Lean_MessageData_ofSyntax(v_after_2918_);
v___x_2928_ = l_Lean_indentD(v___x_2927_);
v_msgData_2929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2929_, 0, v___x_2926_);
lean_ctor_set(v_msgData_2929_, 1, v___x_2928_);
v___x_2930_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_2929_, v_macroStack_2908_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_2935_, lean_object* v_macroStack_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2935_, v_macroStack_2936_, v___y_2937_);
lean_dec_ref(v___y_2937_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_ref_2948_; lean_object* v___x_2949_; lean_object* v_a_2950_; lean_object* v_macroStack_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
v_ref_2948_ = lean_ctor_get(v___y_2945_, 2);
v___x_2949_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2940_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v_macroStack_2951_ = lean_ctor_get(v___y_2941_, 1);
v___x_2952_ = l_Lean_Elab_getBetterRef(v_ref_2948_, v_macroStack_2951_);
lean_inc(v_macroStack_2951_);
v___x_2953_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_2950_, v_macroStack_2951_, v___y_2945_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2952_);
lean_ctor_set(v___x_2958_, 1, v_a_2954_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 1);
lean_ctor_set(v___x_2956_, 0, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v___x_2975_; 
v___x_2975_ = l_Lean_Expr_hasMVar(v_e_2972_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_e_2972_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v_mctx_2978_; lean_object* v___x_2979_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2982_; lean_object* v_cache_2983_; lean_object* v_zetaDeltaFVarIds_2984_; lean_object* v_postponed_2985_; lean_object* v_diag_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
v___x_2977_ = lean_st_ref_get(v___y_2973_);
v_mctx_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_mctx_2978_);
lean_dec(v___x_2977_);
v___x_2979_ = l_Lean_instantiateMVarsCore(v_mctx_2978_, v_e_2972_);
v_fst_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_fst_2980_);
v_snd_2981_ = lean_ctor_get(v___x_2979_, 1);
lean_inc(v_snd_2981_);
lean_dec_ref(v___x_2979_);
v___x_2982_ = lean_st_ref_take(v___y_2973_);
v_cache_2983_ = lean_ctor_get(v___x_2982_, 1);
v_zetaDeltaFVarIds_2984_ = lean_ctor_get(v___x_2982_, 2);
v_postponed_2985_ = lean_ctor_get(v___x_2982_, 3);
v_diag_2986_ = lean_ctor_get(v___x_2982_, 4);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v___x_2982_, 0);
lean_dec(v_unused_2996_);
v___x_2988_ = v___x_2982_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_diag_2986_);
lean_inc(v_postponed_2985_);
lean_inc(v_zetaDeltaFVarIds_2984_);
lean_inc(v_cache_2983_);
lean_dec(v___x_2982_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v_snd_2981_);
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_snd_2981_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_cache_2983_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_zetaDeltaFVarIds_2984_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_postponed_2985_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_diag_2986_);
v___x_2991_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_st_ref_put(v___y_2973_, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_fst_2980_);
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_2997_, v___y_2998_);
lean_dec(v___y_2998_);
return v_res_3000_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = l_Lean_Elab_abortTermExceptionId;
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v___x_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_3008_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_3016_ = l_Lean_Expr_const___override(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3017_; lean_object* v_ty_x3f_3018_; 
v___x_3017_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3018_, 0, v___x_3017_);
return v_ty_x3f_3018_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_3021_ = l_Lean_stringToMessageData(v___x_3020_);
return v___x_3021_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_3023_ = l_Lean_MessageData_ofExpr(v___x_3022_);
return v___x_3023_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_3025_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
return v___x_3026_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3028_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_ty_x3f_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v_toCold_3050_; lean_object* v_currRecDepth_3051_; lean_object* v_ref_3052_; uint8_t v_diag_3053_; uint8_t v_suppressElabErrors_3054_; uint8_t v___x_3055_; lean_object* v_ref_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_ty_x3f_3044_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_3045_ = 1;
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_box(v___x_3045_);
v___x_3048_ = lean_box(v___x_3045_);
lean_inc(v_stx_3036_);
v___x_3049_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3049_, 0, v_stx_3036_);
lean_closure_set(v___x_3049_, 1, v_ty_x3f_3044_);
lean_closure_set(v___x_3049_, 2, v___x_3047_);
lean_closure_set(v___x_3049_, 3, v___x_3048_);
lean_closure_set(v___x_3049_, 4, v___x_3046_);
v_toCold_3050_ = lean_ctor_get(v_a_3041_, 0);
v_currRecDepth_3051_ = lean_ctor_get(v_a_3041_, 1);
v_ref_3052_ = lean_ctor_get(v_a_3041_, 2);
v_diag_3053_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*3);
v_suppressElabErrors_3054_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*3 + 1);
v___x_3055_ = 1;
v_ref_3056_ = l_Lean_replaceRef(v_stx_3036_, v_ref_3052_);
lean_dec(v_stx_3036_);
lean_inc(v_currRecDepth_3051_);
lean_inc_ref(v_toCold_3050_);
v___x_3057_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3057_, 0, v_toCold_3050_);
lean_ctor_set(v___x_3057_, 1, v_currRecDepth_3051_);
lean_ctor_set(v___x_3057_, 2, v_ref_3056_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*3, v_diag_3053_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*3 + 1, v_suppressElabErrors_3054_);
v___x_3058_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3049_, v___x_3055_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v___x_3057_, v_a_3042_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v_a_3061_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; uint8_t v___x_3156_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3059_, v_a_3040_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3060_);
v___x_3156_ = l_Lean_Expr_hasSorry(v_a_3061_);
if (v___x_3156_ == 0)
{
v___y_3101_ = v_a_3037_;
v___y_3102_ = v_a_3038_;
v___y_3103_ = v_a_3039_;
v___y_3104_ = v_a_3040_;
v___y_3105_ = v___x_3057_;
v___y_3106_ = v_a_3042_;
goto v___jp_3100_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = l_Lean_Expr_hasSyntheticSorry(v_a_3061_);
if (v___x_3157_ == 0)
{
v___y_3138_ = v_a_3037_;
v___y_3139_ = v_a_3038_;
v___y_3140_ = v_a_3039_;
v___y_3141_ = v_a_3040_;
v___y_3142_ = v___x_3057_;
v___y_3143_ = v_a_3042_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3158_; lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_a_3061_);
lean_dec_ref_known(v___x_3057_, 3);
v___x_3158_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
v___jp_3062_:
{
if (v___y_3072_ == 0)
{
if (lean_obj_tag(v___y_3063_) == 0)
{
lean_dec_ref_known(v___y_3063_, 2);
lean_dec_ref(v___y_3066_);
lean_dec(v_a_3061_);
return v___y_3071_;
}
else
{
lean_object* v_id_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3086_; 
v_id_3073_ = lean_ctor_get(v___y_3063_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___y_3063_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___y_3063_, 1);
lean_dec(v_unused_3087_);
v___x_3075_ = v___y_3063_;
v_isShared_3076_ = v_isSharedCheck_3086_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_id_3073_);
lean_dec(v___y_3063_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3086_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
uint8_t v___x_3077_; 
v___x_3077_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3069_, v_id_3073_);
lean_dec(v_id_3073_);
if (v___x_3077_ == 0)
{
lean_del_object(v___x_3075_);
lean_dec_ref(v___y_3066_);
lean_dec(v_a_3061_);
return v___y_3071_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
lean_dec_ref(v___y_3071_);
v___x_3078_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_3079_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3080_ = l_Lean_indentExpr(v_a_3061_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set_tag(v___x_3075_, 7);
lean_ctor_set(v___x_3075_, 1, v___x_3080_);
lean_ctor_set(v___x_3075_, 0, v___x_3079_);
v___x_3082_ = v___x_3075_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3078_);
v___x_3084_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3083_, v___y_3064_, v___y_3068_, v___y_3067_, v___y_3070_, v___y_3066_, v___y_3065_);
lean_dec_ref(v___y_3066_);
return v___x_3084_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec_ref(v___y_3063_);
lean_dec(v_a_3061_);
return v___y_3071_;
}
}
v___jp_3088_:
{
lean_object* v___x_3095_; 
lean_inc(v_a_3061_);
v___x_3095_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_3061_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3061_);
return v___x_3095_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
v___x_3097_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3098_ = l_Lean_Exception_isInterrupt(v_a_3096_);
if (v___x_3098_ == 0)
{
uint8_t v___x_3099_; 
lean_inc(v_a_3096_);
v___x_3099_ = l_Lean_Exception_isRuntime(v_a_3096_);
v___y_3063_ = v_a_3096_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v___y_3090_;
v___y_3069_ = v___x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___x_3095_;
v___y_3072_ = v___x_3099_;
goto v___jp_3062_;
}
else
{
v___y_3063_ = v_a_3096_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v___y_3090_;
v___y_3069_ = v___x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___x_3095_;
v___y_3072_ = v___x_3098_;
goto v___jp_3062_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3107_; 
lean_inc(v_a_3061_);
v___x_3107_ = l_Lean_Meta_getMVars(v_a_3061_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3109_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3108_, v___x_3046_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v_a_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; uint8_t v___x_3111_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = lean_unbox(v_a_3110_);
lean_dec(v_a_3110_);
if (v___x_3111_ == 0)
{
v___y_3089_ = v___y_3101_;
v___y_3090_ = v___y_3102_;
v___y_3091_ = v___y_3103_;
v___y_3092_ = v___y_3104_;
v___y_3093_ = v___y_3105_;
v___y_3094_ = v___y_3106_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3112_; lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v___y_3105_);
lean_dec(v_a_3061_);
v___x_3112_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v___y_3105_);
lean_dec(v_a_3061_);
v_a_3121_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3109_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3109_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___y_3105_);
lean_dec(v_a_3061_);
v_a_3129_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3107_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3107_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
v___jp_3137_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v___x_3144_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3145_ = l_Lean_indentExpr(v_a_3061_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3146_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec_ref(v___y_3142_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref_known(v___x_3057_, 3);
v_a_3167_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3058_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3058_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_toCold_3192_; lean_object* v_currRecDepth_3193_; lean_object* v_ref_3194_; uint8_t v_diag_3195_; uint8_t v_suppressElabErrors_3196_; lean_object* v_ref_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_toCold_3192_ = lean_ctor_get(v_a_3189_, 0);
v_currRecDepth_3193_ = lean_ctor_get(v_a_3189_, 1);
v_ref_3194_ = lean_ctor_get(v_a_3189_, 2);
v_diag_3195_ = lean_ctor_get_uint8(v_a_3189_, sizeof(void*)*3);
v_suppressElabErrors_3196_ = lean_ctor_get_uint8(v_a_3189_, sizeof(void*)*3 + 1);
v_ref_3197_ = l_Lean_replaceRef(v_stx_3184_, v_ref_3194_);
lean_inc(v_currRecDepth_3193_);
lean_inc_ref(v_toCold_3192_);
v___x_3198_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3198_, 0, v_toCold_3192_);
lean_ctor_set(v___x_3198_, 1, v_currRecDepth_3193_);
lean_ctor_set(v___x_3198_, 2, v_ref_3197_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*3, v_diag_3195_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*3 + 1, v_suppressElabErrors_3196_);
lean_inc(v_stx_3184_);
v___x_3199_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v___x_3198_, v_a_3190_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref_known(v___x_3198_, 3);
lean_dec(v_stx_3184_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_fst_3204_; lean_object* v___x_3206_; 
v_fst_3204_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_fst_3204_);
lean_dec(v_a_3200_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v_fst_3204_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_fst_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3224_; 
v_a_3209_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3211_ = v___x_3199_;
v_isShared_3212_ = v_isSharedCheck_3224_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3199_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3224_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3213_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3209_);
if (v_isShared_3212_ == 0)
{
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3209_);
v___x_3215_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
uint8_t v___y_3217_; uint8_t v___x_3221_; 
v___x_3221_ = l_Lean_Exception_isInterrupt(v_a_3209_);
if (v___x_3221_ == 0)
{
uint8_t v___x_3222_; 
lean_inc(v_a_3209_);
v___x_3222_ = l_Lean_Exception_isRuntime(v_a_3209_);
v___y_3217_ = v___x_3222_;
goto v___jp_3216_;
}
else
{
v___y_3217_ = v___x_3221_;
goto v___jp_3216_;
}
v___jp_3216_:
{
if (v___y_3217_ == 0)
{
if (lean_obj_tag(v_a_3209_) == 0)
{
lean_dec_ref_known(v_a_3209_, 2);
lean_dec_ref_known(v___x_3198_, 3);
lean_dec(v_stx_3184_);
return v___x_3215_;
}
else
{
lean_object* v_id_3218_; uint8_t v___x_3219_; 
v_id_3218_ = lean_ctor_get(v_a_3209_, 0);
lean_inc(v_id_3218_);
lean_dec_ref_known(v_a_3209_, 2);
v___x_3219_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3213_, v_id_3218_);
lean_dec(v_id_3218_);
if (v___x_3219_ == 0)
{
lean_dec_ref_known(v___x_3198_, 3);
lean_dec(v_stx_3184_);
return v___x_3215_;
}
else
{
lean_object* v___x_3220_; 
lean_dec_ref(v___x_3215_);
v___x_3220_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v___x_3198_, v_a_3190_);
lean_dec_ref_known(v___x_3198_, 3);
return v___x_3220_;
}
}
}
else
{
lean_dec(v_a_3209_);
lean_dec_ref_known(v___x_3198_, 3);
lean_dec(v_stx_3184_);
return v___x_3215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_a_3228_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
return v_res_3233_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_box(0);
v___x_3240_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3241_ = l_Lean_Expr_const___override(v___x_3240_, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3242_; lean_object* v_ty_x3f_3243_; 
v___x_3242_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3243_, 0, v___x_3242_);
return v_ty_x3f_3243_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3245_ = l_Lean_MessageData_ofExpr(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3247_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
lean_ctor_set(v___x_3248_, 1, v___x_3246_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3250_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v___x_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_ty_x3f_3260_; uint8_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_toCold_3266_; lean_object* v_currRecDepth_3267_; lean_object* v_ref_3268_; uint8_t v_diag_3269_; uint8_t v_suppressElabErrors_3270_; uint8_t v___x_3271_; lean_object* v_ref_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_ty_x3f_3260_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3261_ = 1;
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_box(v___x_3261_);
v___x_3264_ = lean_box(v___x_3261_);
lean_inc(v_stx_3252_);
v___x_3265_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3265_, 0, v_stx_3252_);
lean_closure_set(v___x_3265_, 1, v_ty_x3f_3260_);
lean_closure_set(v___x_3265_, 2, v___x_3263_);
lean_closure_set(v___x_3265_, 3, v___x_3264_);
lean_closure_set(v___x_3265_, 4, v___x_3262_);
v_toCold_3266_ = lean_ctor_get(v_a_3257_, 0);
v_currRecDepth_3267_ = lean_ctor_get(v_a_3257_, 1);
v_ref_3268_ = lean_ctor_get(v_a_3257_, 2);
v_diag_3269_ = lean_ctor_get_uint8(v_a_3257_, sizeof(void*)*3);
v_suppressElabErrors_3270_ = lean_ctor_get_uint8(v_a_3257_, sizeof(void*)*3 + 1);
v___x_3271_ = 1;
v_ref_3272_ = l_Lean_replaceRef(v_stx_3252_, v_ref_3268_);
lean_dec(v_stx_3252_);
lean_inc(v_currRecDepth_3267_);
lean_inc_ref(v_toCold_3266_);
v___x_3273_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3273_, 0, v_toCold_3266_);
lean_ctor_set(v___x_3273_, 1, v_currRecDepth_3267_);
lean_ctor_set(v___x_3273_, 2, v_ref_3272_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*3, v_diag_3269_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*3 + 1, v_suppressElabErrors_3270_);
v___x_3274_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3265_, v___x_3271_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v___x_3273_, v_a_3258_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v_a_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; uint8_t v___x_3372_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3275_, v_a_3256_);
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___x_3372_ = l_Lean_Expr_hasSorry(v_a_3277_);
if (v___x_3372_ == 0)
{
v___y_3317_ = v_a_3253_;
v___y_3318_ = v_a_3254_;
v___y_3319_ = v_a_3255_;
v___y_3320_ = v_a_3256_;
v___y_3321_ = v___x_3273_;
v___y_3322_ = v_a_3258_;
goto v___jp_3316_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Expr_hasSyntheticSorry(v_a_3277_);
if (v___x_3373_ == 0)
{
v___y_3354_ = v_a_3253_;
v___y_3355_ = v_a_3254_;
v___y_3356_ = v_a_3255_;
v___y_3357_ = v_a_3256_;
v___y_3358_ = v___x_3273_;
v___y_3359_ = v_a_3258_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3374_; lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3277_);
lean_dec_ref_known(v___x_3273_, 3);
v___x_3374_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
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
v___jp_3278_:
{
if (v___y_3288_ == 0)
{
if (lean_obj_tag(v___y_3281_) == 0)
{
lean_dec_ref_known(v___y_3281_, 2);
lean_dec_ref(v___y_3284_);
lean_dec(v_a_3277_);
return v___y_3280_;
}
else
{
lean_object* v_id_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3302_; 
v_id_3289_ = lean_ctor_get(v___y_3281_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___y_3281_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v___y_3281_, 1);
lean_dec(v_unused_3303_);
v___x_3291_ = v___y_3281_;
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_id_3289_);
lean_dec(v___y_3281_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
uint8_t v___x_3293_; 
v___x_3293_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3282_, v_id_3289_);
lean_dec(v_id_3289_);
if (v___x_3293_ == 0)
{
lean_del_object(v___x_3291_);
lean_dec_ref(v___y_3284_);
lean_dec(v_a_3277_);
return v___y_3280_;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
lean_dec_ref(v___y_3280_);
v___x_3294_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3295_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3296_ = l_Lean_indentExpr(v_a_3277_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 7);
lean_ctor_set(v___x_3291_, 1, v___x_3296_);
lean_ctor_set(v___x_3291_, 0, v___x_3295_);
v___x_3298_ = v___x_3291_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v___x_3294_);
v___x_3300_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3299_, v___y_3283_, v___y_3285_, v___y_3287_, v___y_3286_, v___y_3284_, v___y_3279_);
lean_dec_ref(v___y_3284_);
return v___x_3300_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3284_);
lean_dec_ref(v___y_3281_);
lean_dec(v_a_3277_);
return v___y_3280_;
}
}
v___jp_3304_:
{
lean_object* v___x_3311_; 
lean_inc(v_a_3277_);
v___x_3311_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3277_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_dec_ref(v___y_3309_);
lean_dec(v_a_3277_);
return v___x_3311_;
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
v___x_3313_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3314_ = l_Lean_Exception_isInterrupt(v_a_3312_);
if (v___x_3314_ == 0)
{
uint8_t v___x_3315_; 
lean_inc(v_a_3312_);
v___x_3315_ = l_Lean_Exception_isRuntime(v_a_3312_);
v___y_3279_ = v___y_3310_;
v___y_3280_ = v___x_3311_;
v___y_3281_ = v_a_3312_;
v___y_3282_ = v___x_3313_;
v___y_3283_ = v___y_3305_;
v___y_3284_ = v___y_3309_;
v___y_3285_ = v___y_3306_;
v___y_3286_ = v___y_3308_;
v___y_3287_ = v___y_3307_;
v___y_3288_ = v___x_3315_;
goto v___jp_3278_;
}
else
{
v___y_3279_ = v___y_3310_;
v___y_3280_ = v___x_3311_;
v___y_3281_ = v_a_3312_;
v___y_3282_ = v___x_3313_;
v___y_3283_ = v___y_3305_;
v___y_3284_ = v___y_3309_;
v___y_3285_ = v___y_3306_;
v___y_3286_ = v___y_3308_;
v___y_3287_ = v___y_3307_;
v___y_3288_ = v___x_3314_;
goto v___jp_3278_;
}
}
}
v___jp_3316_:
{
lean_object* v___x_3323_; 
lean_inc(v_a_3277_);
v___x_3323_ = l_Lean_Meta_getMVars(v_a_3277_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3324_, v___x_3262_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v_a_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; uint8_t v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = lean_unbox(v_a_3326_);
lean_dec(v_a_3326_);
if (v___x_3327_ == 0)
{
v___y_3305_ = v___y_3317_;
v___y_3306_ = v___y_3318_;
v___y_3307_ = v___y_3319_;
v___y_3308_ = v___y_3320_;
v___y_3309_ = v___y_3321_;
v___y_3310_ = v___y_3322_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___y_3321_);
lean_dec(v_a_3277_);
v___x_3328_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v___y_3321_);
lean_dec(v_a_3277_);
v_a_3337_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3325_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3325_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v___y_3321_);
lean_dec(v_a_3277_);
v_a_3345_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3323_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3323_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
v___jp_3353_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
v___x_3360_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3361_ = l_Lean_indentExpr(v_a_3277_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3362_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec_ref(v___y_3358_);
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref_known(v___x_3273_, 3);
v_a_3383_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3274_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3274_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_toCold_3408_; lean_object* v_currRecDepth_3409_; lean_object* v_ref_3410_; uint8_t v_diag_3411_; uint8_t v_suppressElabErrors_3412_; lean_object* v_ref_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v_toCold_3408_ = lean_ctor_get(v_a_3405_, 0);
v_currRecDepth_3409_ = lean_ctor_get(v_a_3405_, 1);
v_ref_3410_ = lean_ctor_get(v_a_3405_, 2);
v_diag_3411_ = lean_ctor_get_uint8(v_a_3405_, sizeof(void*)*3);
v_suppressElabErrors_3412_ = lean_ctor_get_uint8(v_a_3405_, sizeof(void*)*3 + 1);
v_ref_3413_ = l_Lean_replaceRef(v_stx_3400_, v_ref_3410_);
lean_inc(v_currRecDepth_3409_);
lean_inc_ref(v_toCold_3408_);
v___x_3414_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3414_, 0, v_toCold_3408_);
lean_ctor_set(v___x_3414_, 1, v_currRecDepth_3409_);
lean_ctor_set(v___x_3414_, 2, v_ref_3413_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*3, v_diag_3411_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*3 + 1, v_suppressElabErrors_3412_);
lean_inc(v_stx_3400_);
v___x_3415_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v___x_3414_, v_a_3406_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref_known(v___x_3414_, 3);
lean_dec(v_stx_3400_);
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v___x_3422_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_fst_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_fst_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3440_; 
v_a_3425_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3427_ = v___x_3415_;
v_isShared_3428_ = v_isSharedCheck_3440_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3415_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3440_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3425_);
if (v_isShared_3428_ == 0)
{
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3425_);
v___x_3431_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
uint8_t v___y_3433_; uint8_t v___x_3437_; 
v___x_3437_ = l_Lean_Exception_isInterrupt(v_a_3425_);
if (v___x_3437_ == 0)
{
uint8_t v___x_3438_; 
lean_inc(v_a_3425_);
v___x_3438_ = l_Lean_Exception_isRuntime(v_a_3425_);
v___y_3433_ = v___x_3438_;
goto v___jp_3432_;
}
else
{
v___y_3433_ = v___x_3437_;
goto v___jp_3432_;
}
v___jp_3432_:
{
if (v___y_3433_ == 0)
{
if (lean_obj_tag(v_a_3425_) == 0)
{
lean_dec_ref_known(v_a_3425_, 2);
lean_dec_ref_known(v___x_3414_, 3);
lean_dec(v_stx_3400_);
return v___x_3431_;
}
else
{
lean_object* v_id_3434_; uint8_t v___x_3435_; 
v_id_3434_ = lean_ctor_get(v_a_3425_, 0);
lean_inc(v_id_3434_);
lean_dec_ref_known(v_a_3425_, 2);
v___x_3435_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3429_, v_id_3434_);
lean_dec(v_id_3434_);
if (v___x_3435_ == 0)
{
lean_dec_ref_known(v___x_3414_, 3);
lean_dec(v_stx_3400_);
return v___x_3431_;
}
else
{
lean_object* v___x_3436_; 
lean_dec_ref(v___x_3431_);
v___x_3436_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v___x_3414_, v_a_3406_);
lean_dec_ref_known(v___x_3414_, 3);
return v___x_3436_;
}
}
}
else
{
lean_dec(v_a_3425_);
lean_dec_ref_known(v___x_3414_, 3);
lean_dec(v_stx_3400_);
return v___x_3431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
return v_res_3449_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3451_ = l_Lean_MessageData_ofExpr(v___x_3450_);
return v___x_3451_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3453_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
lean_ctor_set(v___x_3454_, 1, v___x_3452_);
return v___x_3454_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_ty_x3f_3466_; uint8_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v_toCold_3472_; lean_object* v_currRecDepth_3473_; lean_object* v_ref_3474_; uint8_t v_diag_3475_; uint8_t v_suppressElabErrors_3476_; uint8_t v___x_3477_; lean_object* v_ref_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v_ty_x3f_3466_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3467_ = 1;
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_box(v___x_3467_);
v___x_3470_ = lean_box(v___x_3467_);
lean_inc(v_stx_3458_);
v___x_3471_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3471_, 0, v_stx_3458_);
lean_closure_set(v___x_3471_, 1, v_ty_x3f_3466_);
lean_closure_set(v___x_3471_, 2, v___x_3469_);
lean_closure_set(v___x_3471_, 3, v___x_3470_);
lean_closure_set(v___x_3471_, 4, v___x_3468_);
v_toCold_3472_ = lean_ctor_get(v_a_3463_, 0);
v_currRecDepth_3473_ = lean_ctor_get(v_a_3463_, 1);
v_ref_3474_ = lean_ctor_get(v_a_3463_, 2);
v_diag_3475_ = lean_ctor_get_uint8(v_a_3463_, sizeof(void*)*3);
v_suppressElabErrors_3476_ = lean_ctor_get_uint8(v_a_3463_, sizeof(void*)*3 + 1);
v___x_3477_ = 1;
v_ref_3478_ = l_Lean_replaceRef(v_stx_3458_, v_ref_3474_);
lean_dec(v_stx_3458_);
lean_inc(v_currRecDepth_3473_);
lean_inc_ref(v_toCold_3472_);
v___x_3479_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3479_, 0, v_toCold_3472_);
lean_ctor_set(v___x_3479_, 1, v_currRecDepth_3473_);
lean_ctor_set(v___x_3479_, 2, v_ref_3478_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*3, v_diag_3475_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*3 + 1, v_suppressElabErrors_3476_);
v___x_3480_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3471_, v___x_3477_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v___x_3479_, v_a_3464_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; lean_object* v_a_3483_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; uint8_t v___x_3578_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3482_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3481_, v_a_3462_);
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref(v___x_3482_);
v___x_3578_ = l_Lean_Expr_hasSorry(v_a_3483_);
if (v___x_3578_ == 0)
{
v___y_3523_ = v_a_3459_;
v___y_3524_ = v_a_3460_;
v___y_3525_ = v_a_3461_;
v___y_3526_ = v_a_3462_;
v___y_3527_ = v___x_3479_;
v___y_3528_ = v_a_3464_;
goto v___jp_3522_;
}
else
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_Expr_hasSyntheticSorry(v_a_3483_);
if (v___x_3579_ == 0)
{
v___y_3560_ = v_a_3459_;
v___y_3561_ = v_a_3460_;
v___y_3562_ = v_a_3461_;
v___y_3563_ = v_a_3462_;
v___y_3564_ = v___x_3479_;
v___y_3565_ = v_a_3464_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3580_; lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_a_3483_);
lean_dec_ref_known(v___x_3479_, 3);
v___x_3580_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
v___jp_3484_:
{
if (v___y_3494_ == 0)
{
if (lean_obj_tag(v___y_3491_) == 0)
{
lean_dec_ref_known(v___y_3491_, 2);
lean_dec_ref(v___y_3490_);
lean_dec(v_a_3483_);
return v___y_3488_;
}
else
{
lean_object* v_id_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3508_; 
v_id_3495_ = lean_ctor_get(v___y_3491_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___y_3491_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; 
v_unused_3509_ = lean_ctor_get(v___y_3491_, 1);
lean_dec(v_unused_3509_);
v___x_3497_ = v___y_3491_;
v_isShared_3498_ = v_isSharedCheck_3508_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_id_3495_);
lean_dec(v___y_3491_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3508_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
uint8_t v___x_3499_; 
v___x_3499_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3486_, v_id_3495_);
lean_dec(v_id_3495_);
if (v___x_3499_ == 0)
{
lean_del_object(v___x_3497_);
lean_dec_ref(v___y_3490_);
lean_dec(v_a_3483_);
return v___y_3488_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
lean_dec_ref(v___y_3488_);
v___x_3500_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3501_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3502_ = l_Lean_indentExpr(v_a_3483_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set_tag(v___x_3497_, 7);
lean_ctor_set(v___x_3497_, 1, v___x_3502_);
lean_ctor_set(v___x_3497_, 0, v___x_3501_);
v___x_3504_ = v___x_3497_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3500_);
v___x_3506_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3505_, v___y_3485_, v___y_3493_, v___y_3487_, v___y_3489_, v___y_3490_, v___y_3492_);
lean_dec_ref(v___y_3490_);
return v___x_3506_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_a_3483_);
return v___y_3488_;
}
}
v___jp_3510_:
{
lean_object* v___x_3517_; 
lean_inc(v_a_3483_);
v___x_3517_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3483_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_dec_ref(v___y_3515_);
lean_dec(v_a_3483_);
return v___x_3517_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
v___x_3519_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3520_ = l_Lean_Exception_isInterrupt(v_a_3518_);
if (v___x_3520_ == 0)
{
uint8_t v___x_3521_; 
lean_inc(v_a_3518_);
v___x_3521_ = l_Lean_Exception_isRuntime(v_a_3518_);
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___x_3519_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___x_3517_;
v___y_3489_ = v___y_3514_;
v___y_3490_ = v___y_3515_;
v___y_3491_ = v_a_3518_;
v___y_3492_ = v___y_3516_;
v___y_3493_ = v___y_3512_;
v___y_3494_ = v___x_3521_;
goto v___jp_3484_;
}
else
{
v___y_3485_ = v___y_3511_;
v___y_3486_ = v___x_3519_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___x_3517_;
v___y_3489_ = v___y_3514_;
v___y_3490_ = v___y_3515_;
v___y_3491_ = v_a_3518_;
v___y_3492_ = v___y_3516_;
v___y_3493_ = v___y_3512_;
v___y_3494_ = v___x_3520_;
goto v___jp_3484_;
}
}
}
v___jp_3522_:
{
lean_object* v___x_3529_; 
lean_inc(v_a_3483_);
v___x_3529_ = l_Lean_Meta_getMVars(v_a_3483_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___x_3531_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3530_, v___x_3468_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v_a_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; uint8_t v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = lean_unbox(v_a_3532_);
lean_dec(v_a_3532_);
if (v___x_3533_ == 0)
{
v___y_3511_ = v___y_3523_;
v___y_3512_ = v___y_3524_;
v___y_3513_ = v___y_3525_;
v___y_3514_ = v___y_3526_;
v___y_3515_ = v___y_3527_;
v___y_3516_ = v___y_3528_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3534_; lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___y_3527_);
lean_dec(v_a_3483_);
v___x_3534_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___y_3527_);
lean_dec(v_a_3483_);
v_a_3543_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3531_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3531_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v___y_3527_);
lean_dec(v_a_3483_);
v_a_3551_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3529_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3529_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
v___jp_3559_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v___x_3566_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3567_ = l_Lean_indentExpr(v_a_3483_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3568_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec_ref(v___y_3564_);
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
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
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref_known(v___x_3479_, 3);
v_a_3589_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3480_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3480_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
return v_res_3605_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = lean_box(0);
v___x_3612_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3613_ = l_Lean_Expr_const___override(v___x_3612_, v___x_3611_);
return v___x_3613_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3614_; lean_object* v_ty_x3f_3615_; 
v___x_3614_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3615_, 0, v___x_3614_);
return v_ty_x3f_3615_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3617_ = l_Lean_MessageData_ofExpr(v___x_3616_);
return v___x_3617_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3619_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3618_);
return v___x_3620_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3622_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v___x_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_ty_x3f_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v_toCold_3638_; lean_object* v_currRecDepth_3639_; lean_object* v_ref_3640_; uint8_t v_diag_3641_; uint8_t v_suppressElabErrors_3642_; uint8_t v___x_3643_; lean_object* v_ref_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_ty_x3f_3632_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3633_ = 1;
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_box(v___x_3633_);
v___x_3636_ = lean_box(v___x_3633_);
lean_inc(v_stx_3624_);
v___x_3637_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3637_, 0, v_stx_3624_);
lean_closure_set(v___x_3637_, 1, v_ty_x3f_3632_);
lean_closure_set(v___x_3637_, 2, v___x_3635_);
lean_closure_set(v___x_3637_, 3, v___x_3636_);
lean_closure_set(v___x_3637_, 4, v___x_3634_);
v_toCold_3638_ = lean_ctor_get(v_a_3629_, 0);
v_currRecDepth_3639_ = lean_ctor_get(v_a_3629_, 1);
v_ref_3640_ = lean_ctor_get(v_a_3629_, 2);
v_diag_3641_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*3);
v_suppressElabErrors_3642_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*3 + 1);
v___x_3643_ = 1;
v_ref_3644_ = l_Lean_replaceRef(v_stx_3624_, v_ref_3640_);
lean_dec(v_stx_3624_);
lean_inc(v_currRecDepth_3639_);
lean_inc_ref(v_toCold_3638_);
v___x_3645_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3645_, 0, v_toCold_3638_);
lean_ctor_set(v___x_3645_, 1, v_currRecDepth_3639_);
lean_ctor_set(v___x_3645_, 2, v_ref_3644_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*3, v_diag_3641_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*3 + 1, v_suppressElabErrors_3642_);
v___x_3646_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3637_, v___x_3643_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v___x_3645_, v_a_3630_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v_a_3649_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; uint8_t v___y_3660_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; uint8_t v___x_3744_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3647_, v_a_3628_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3744_ = l_Lean_Expr_hasSorry(v_a_3649_);
if (v___x_3744_ == 0)
{
v___y_3689_ = v_a_3625_;
v___y_3690_ = v_a_3626_;
v___y_3691_ = v_a_3627_;
v___y_3692_ = v_a_3628_;
v___y_3693_ = v___x_3645_;
v___y_3694_ = v_a_3630_;
goto v___jp_3688_;
}
else
{
uint8_t v___x_3745_; 
v___x_3745_ = l_Lean_Expr_hasSyntheticSorry(v_a_3649_);
if (v___x_3745_ == 0)
{
v___y_3726_ = v_a_3625_;
v___y_3727_ = v_a_3626_;
v___y_3728_ = v_a_3627_;
v___y_3729_ = v_a_3628_;
v___y_3730_ = v___x_3645_;
v___y_3731_ = v_a_3630_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3746_; lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3649_);
lean_dec_ref_known(v___x_3645_, 3);
v___x_3746_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
v___jp_3650_:
{
if (v___y_3660_ == 0)
{
if (lean_obj_tag(v___y_3659_) == 0)
{
lean_dec_ref_known(v___y_3659_, 2);
lean_dec_ref(v___y_3658_);
lean_dec(v_a_3649_);
return v___y_3651_;
}
else
{
lean_object* v_id_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3674_; 
v_id_3661_ = lean_ctor_get(v___y_3659_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___y_3659_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; 
v_unused_3675_ = lean_ctor_get(v___y_3659_, 1);
lean_dec(v_unused_3675_);
v___x_3663_ = v___y_3659_;
v_isShared_3664_ = v_isSharedCheck_3674_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_id_3661_);
lean_dec(v___y_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3674_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
uint8_t v___x_3665_; 
v___x_3665_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3653_, v_id_3661_);
lean_dec(v_id_3661_);
if (v___x_3665_ == 0)
{
lean_del_object(v___x_3663_);
lean_dec_ref(v___y_3658_);
lean_dec(v_a_3649_);
return v___y_3651_;
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_dec_ref(v___y_3651_);
v___x_3666_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3667_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3668_ = l_Lean_indentExpr(v_a_3649_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set_tag(v___x_3663_, 7);
lean_ctor_set(v___x_3663_, 1, v___x_3668_);
lean_ctor_set(v___x_3663_, 0, v___x_3667_);
v___x_3670_ = v___x_3663_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___x_3666_);
v___x_3672_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3671_, v___y_3656_, v___y_3655_, v___y_3654_, v___y_3652_, v___y_3658_, v___y_3657_);
lean_dec_ref(v___y_3658_);
return v___x_3672_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v_a_3649_);
return v___y_3651_;
}
}
v___jp_3676_:
{
lean_object* v___x_3683_; 
lean_inc(v_a_3649_);
v___x_3683_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3649_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_dec_ref(v___y_3681_);
lean_dec(v_a_3649_);
return v___x_3683_;
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
v___x_3685_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3686_ = l_Lean_Exception_isInterrupt(v_a_3684_);
if (v___x_3686_ == 0)
{
uint8_t v___x_3687_; 
lean_inc(v_a_3684_);
v___x_3687_ = l_Lean_Exception_isRuntime(v_a_3684_);
v___y_3651_ = v___x_3683_;
v___y_3652_ = v___y_3680_;
v___y_3653_ = v___x_3685_;
v___y_3654_ = v___y_3679_;
v___y_3655_ = v___y_3678_;
v___y_3656_ = v___y_3677_;
v___y_3657_ = v___y_3682_;
v___y_3658_ = v___y_3681_;
v___y_3659_ = v_a_3684_;
v___y_3660_ = v___x_3687_;
goto v___jp_3650_;
}
else
{
v___y_3651_ = v___x_3683_;
v___y_3652_ = v___y_3680_;
v___y_3653_ = v___x_3685_;
v___y_3654_ = v___y_3679_;
v___y_3655_ = v___y_3678_;
v___y_3656_ = v___y_3677_;
v___y_3657_ = v___y_3682_;
v___y_3658_ = v___y_3681_;
v___y_3659_ = v_a_3684_;
v___y_3660_ = v___x_3686_;
goto v___jp_3650_;
}
}
}
v___jp_3688_:
{
lean_object* v___x_3695_; 
lean_inc(v_a_3649_);
v___x_3695_ = l_Lean_Meta_getMVars(v_a_3649_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3696_, v___x_3634_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v_a_3696_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; uint8_t v___x_3699_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = lean_unbox(v_a_3698_);
lean_dec(v_a_3698_);
if (v___x_3699_ == 0)
{
v___y_3677_ = v___y_3689_;
v___y_3678_ = v___y_3690_;
v___y_3679_ = v___y_3691_;
v___y_3680_ = v___y_3692_;
v___y_3681_ = v___y_3693_;
v___y_3682_ = v___y_3694_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3700_; lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v___y_3693_);
lean_dec(v_a_3649_);
v___x_3700_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v___y_3693_);
lean_dec(v_a_3649_);
v_a_3709_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3697_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3697_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___y_3693_);
lean_dec(v_a_3649_);
v_a_3717_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3695_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3695_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
v___jp_3725_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
v___x_3732_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3733_ = l_Lean_indentExpr(v_a_3649_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3734_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec_ref(v___y_3730_);
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3735_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref_known(v___x_3645_, 3);
v_a_3755_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3646_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3646_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_toCold_3780_; lean_object* v_currRecDepth_3781_; lean_object* v_ref_3782_; uint8_t v_diag_3783_; uint8_t v_suppressElabErrors_3784_; lean_object* v_ref_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_toCold_3780_ = lean_ctor_get(v_a_3777_, 0);
v_currRecDepth_3781_ = lean_ctor_get(v_a_3777_, 1);
v_ref_3782_ = lean_ctor_get(v_a_3777_, 2);
v_diag_3783_ = lean_ctor_get_uint8(v_a_3777_, sizeof(void*)*3);
v_suppressElabErrors_3784_ = lean_ctor_get_uint8(v_a_3777_, sizeof(void*)*3 + 1);
v_ref_3785_ = l_Lean_replaceRef(v_stx_3772_, v_ref_3782_);
lean_inc(v_currRecDepth_3781_);
lean_inc_ref(v_toCold_3780_);
v___x_3786_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3786_, 0, v_toCold_3780_);
lean_ctor_set(v___x_3786_, 1, v_currRecDepth_3781_);
lean_ctor_set(v___x_3786_, 2, v_ref_3785_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*3, v_diag_3783_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*3 + 1, v_suppressElabErrors_3784_);
lean_inc(v_stx_3772_);
v___x_3787_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v___x_3786_, v_a_3778_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref_known(v___x_3786_, 3);
lean_dec(v_stx_3772_);
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3796_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3796_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_fst_3792_; lean_object* v___x_3794_; 
v_fst_3792_ = lean_ctor_get(v_a_3788_, 0);
lean_inc(v_fst_3792_);
lean_dec(v_a_3788_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_fst_3792_);
v___x_3794_ = v___x_3790_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_fst_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3812_; 
v_a_3797_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3799_ = v___x_3787_;
v_isShared_3800_ = v_isSharedCheck_3812_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3787_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3812_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3801_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3797_);
if (v_isShared_3800_ == 0)
{
v___x_3803_ = v___x_3799_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3797_);
v___x_3803_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
uint8_t v___y_3805_; uint8_t v___x_3809_; 
v___x_3809_ = l_Lean_Exception_isInterrupt(v_a_3797_);
if (v___x_3809_ == 0)
{
uint8_t v___x_3810_; 
lean_inc(v_a_3797_);
v___x_3810_ = l_Lean_Exception_isRuntime(v_a_3797_);
v___y_3805_ = v___x_3810_;
goto v___jp_3804_;
}
else
{
v___y_3805_ = v___x_3809_;
goto v___jp_3804_;
}
v___jp_3804_:
{
if (v___y_3805_ == 0)
{
if (lean_obj_tag(v_a_3797_) == 0)
{
lean_dec_ref_known(v_a_3797_, 2);
lean_dec_ref_known(v___x_3786_, 3);
lean_dec(v_stx_3772_);
return v___x_3803_;
}
else
{
lean_object* v_id_3806_; uint8_t v___x_3807_; 
v_id_3806_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_id_3806_);
lean_dec_ref_known(v_a_3797_, 2);
v___x_3807_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3801_, v_id_3806_);
lean_dec(v_id_3806_);
if (v___x_3807_ == 0)
{
lean_dec_ref_known(v___x_3786_, 3);
lean_dec(v_stx_3772_);
return v___x_3803_;
}
else
{
lean_object* v___x_3808_; 
lean_dec_ref(v___x_3803_);
v___x_3808_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v___x_3786_, v_a_3778_);
lean_dec_ref_known(v___x_3786_, 3);
return v___x_3808_;
}
}
}
else
{
lean_dec(v_a_3797_);
lean_dec_ref_known(v___x_3786_, 3);
lean_dec(v_stx_3772_);
return v___x_3803_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3853_, lean_object* v_item_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_item_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3873_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3854_, v___x_3872_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3873_) == 0)
{
uint8_t v___x_3874_; 
lean_dec_ref_known(v___x_3873_, 1);
v___x_3874_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3854_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3875_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3854_);
lean_inc_ref(v_item_3854_);
v___x_3876_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3854_);
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3878_ = lean_string_dec_eq(v___x_3875_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3880_ = lean_string_dec_eq(v___x_3875_, v___x_3879_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3882_ = lean_string_dec_eq(v___x_3875_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3884_ = lean_string_dec_eq(v___x_3875_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3886_ = lean_string_dec_eq(v___x_3875_, v___x_3885_);
lean_dec_ref(v___x_3875_);
if (v___x_3886_ == 0)
{
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3888_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3854_, v___x_3887_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3888_) == 0)
{
uint8_t v___x_3889_; 
lean_dec_ref_known(v___x_3888_, 1);
v___x_3889_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3876_);
if (v___x_3889_ == 0)
{
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3890_; 
lean_dec_ref(v___x_3876_);
lean_inc_ref(v_item_3854_);
v___x_3890_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_value_3891_; lean_object* v___x_3892_; 
lean_dec_ref_known(v___x_3890_, 1);
v_value_3891_ = lean_ctor_get(v_item_3854_, 2);
lean_inc(v_value_3891_);
lean_dec_ref(v_item_3854_);
v___x_3892_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3891_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3911_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3911_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3911_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
uint8_t v_offsetCnstrs_3897_; lean_object* v_occs_3898_; uint8_t v_newGoals_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3910_; 
v_offsetCnstrs_3897_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 1);
v_occs_3898_ = lean_ctor_get(v_config_3853_, 0);
v_newGoals_3899_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 2);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_config_3853_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3901_ = v_config_3853_;
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_occs_3898_);
lean_dec(v_config_3853_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_occs_3898_);
v___x_3904_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
uint8_t v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_unbox(v_a_3893_);
lean_dec(v_a_3893_);
lean_ctor_set_uint8(v___x_3904_, sizeof(void*)*1, v___x_3905_);
lean_ctor_set_uint8(v___x_3904_, sizeof(void*)*1 + 1, v_offsetCnstrs_3897_);
lean_ctor_set_uint8(v___x_3904_, sizeof(void*)*1 + 2, v_newGoals_3899_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3904_);
v___x_3907_ = v___x_3895_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3904_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_config_3853_);
v_a_3912_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3892_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3892_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_3920_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3890_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3890_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_3928_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3888_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3888_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec_ref(v___x_3875_);
v___x_3936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_3937_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3854_, v___x_3936_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3937_) == 0)
{
uint8_t v___x_3938_; 
lean_dec_ref_known(v___x_3937_, 1);
v___x_3938_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3876_);
if (v___x_3938_ == 0)
{
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3939_; 
lean_dec_ref(v___x_3876_);
v___x_3939_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3958_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_3958_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3958_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
uint8_t v_transparency_3944_; lean_object* v_occs_3945_; uint8_t v_newGoals_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3957_; 
v_transparency_3944_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1);
v_occs_3945_ = lean_ctor_get(v_config_3853_, 0);
v_newGoals_3946_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 2);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_config_3853_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3948_ = v_config_3853_;
v_isShared_3949_ = v_isSharedCheck_3957_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_occs_3945_);
lean_dec(v_config_3853_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3957_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_occs_3945_);
lean_ctor_set_uint8(v_reuseFailAlloc_3956_, sizeof(void*)*1, v_transparency_3944_);
v___x_3951_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
uint8_t v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = lean_unbox(v_a_3940_);
lean_dec(v_a_3940_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*1 + 1, v___x_3952_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*1 + 2, v_newGoals_3946_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3951_);
v___x_3954_ = v___x_3942_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3951_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec_ref(v_config_3853_);
v_a_3959_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3939_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3939_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_3967_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3937_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3937_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
lean_dec_ref(v___x_3875_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_3976_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3854_, v___x_3975_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3976_) == 0)
{
uint8_t v___x_3977_; 
lean_dec_ref_known(v___x_3976_, 1);
v___x_3977_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3876_);
if (v___x_3977_ == 0)
{
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3978_; 
lean_dec_ref(v___x_3876_);
lean_inc_ref(v_item_3854_);
v___x_3978_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_value_3979_; lean_object* v___x_3980_; 
lean_dec_ref_known(v___x_3978_, 1);
v_value_3979_ = lean_ctor_get(v_item_3854_, 2);
lean_inc(v_value_3979_);
lean_dec_ref(v_item_3854_);
v___x_3980_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_3979_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
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
uint8_t v_transparency_3985_; uint8_t v_offsetCnstrs_3986_; uint8_t v_newGoals_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3997_; 
v_transparency_3985_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1);
v_offsetCnstrs_3986_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 1);
v_newGoals_3987_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 2);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_config_3853_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; 
v_unused_3998_ = lean_ctor_get(v_config_3853_, 0);
lean_dec(v_unused_3998_);
v___x_3989_ = v_config_3853_;
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v_config_3853_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_a_3981_);
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*1, v_transparency_3985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*1 + 1, v_offsetCnstrs_3986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*1 + 2, v_newGoals_3987_);
v___x_3992_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3992_);
v___x_3994_ = v___x_3983_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v_config_3853_);
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
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
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
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
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
lean_dec_ref(v___x_3875_);
v___x_4024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_4025_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3854_, v___x_4024_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_4025_) == 0)
{
uint8_t v___x_4026_; 
lean_dec_ref_known(v___x_4025_, 1);
v___x_4026_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3876_);
if (v___x_4026_ == 0)
{
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_4027_; 
lean_dec_ref(v___x_3876_);
lean_inc_ref(v_item_3854_);
v___x_4027_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_value_4028_; lean_object* v___x_4029_; 
lean_dec_ref_known(v___x_4027_, 1);
v_value_4028_ = lean_ctor_get(v_item_3854_, 2);
lean_inc(v_value_4028_);
lean_dec_ref(v_item_3854_);
v___x_4029_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_4028_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4048_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4048_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4048_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
uint8_t v_transparency_4034_; uint8_t v_offsetCnstrs_4035_; lean_object* v_occs_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4047_; 
v_transparency_4034_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1);
v_offsetCnstrs_4035_ = lean_ctor_get_uint8(v_config_3853_, sizeof(void*)*1 + 1);
v_occs_4036_ = lean_ctor_get(v_config_3853_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_config_3853_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4038_ = v_config_3853_;
v_isShared_4039_ = v_isSharedCheck_4047_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_occs_4036_);
lean_dec(v_config_3853_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4047_;
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
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_occs_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4046_, sizeof(void*)*1, v_transparency_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4046_, sizeof(void*)*1 + 1, v_offsetCnstrs_4035_);
v___x_4041_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
uint8_t v___x_4042_; lean_object* v___x_4044_; 
v___x_4042_ = lean_unbox(v_a_4030_);
lean_dec(v_a_4030_);
lean_ctor_set_uint8(v___x_4041_, sizeof(void*)*1 + 2, v___x_4042_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4041_);
v___x_4044_ = v___x_4032_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4041_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v_config_3853_);
v_a_4049_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4029_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4029_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_4057_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4027_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4027_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_4065_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4025_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4025_);
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
}
else
{
uint8_t v___x_4073_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v_config_3853_);
v___x_4073_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3876_);
if (v___x_4073_ == 0)
{
lean_dec_ref(v_item_3854_);
v_item_3863_ = v___x_3876_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
else
{
lean_object* v_value_4074_; lean_object* v___x_4075_; 
lean_dec_ref(v___x_3876_);
v_value_4074_ = lean_ctor_get(v_item_3854_, 2);
lean_inc(v_value_4074_);
lean_dec_ref(v_item_3854_);
v___x_4075_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_4074_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
return v___x_4075_;
}
}
}
else
{
lean_dec_ref(v_config_3853_);
v_item_3863_ = v_item_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
goto v___jp_3862_;
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref(v_item_3854_);
lean_dec_ref(v_config_3853_);
v_a_4076_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_3873_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_3873_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
v___jp_3862_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3871_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3863_, v___x_3870_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
return v___x_3871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_4084_, lean_object* v_item_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_4084_, v_item_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_4096_, v___y_4100_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4132_, lean_object* v_msg_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4142_, lean_object* v_msg_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4142_, v_msg_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4152_, lean_object* v_macroStack_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4152_, v_macroStack_4153_, v___y_4158_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4162_, lean_object* v_macroStack_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4162_, v_macroStack_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
return v_res_4171_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = lean_box(0);
v___x_4173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4174_ = l_Lean_mkConst(v___x_4173_, v___x_4172_);
return v___x_4174_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4177_, lean_object* v_cfgItem_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4187_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4177_, v_cfgItem_4178_, v___x_4186_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4188_, lean_object* v_cfgItem_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4188_, v_cfgItem_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v_cfgItem_4189_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4199_, lean_object* v_init_4200_, uint8_t v_logExceptions_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_onErr_4206_; lean_object* v_eval_4207_; 
v_onErr_4206_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4201_ == 0)
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4207_, v_init_4200_, v_cfg_4199_, v_onErr_4206_, v_logExceptions_4201_, v_a_4203_, v_a_4204_);
return v___x_4208_;
}
else
{
uint8_t v_recover_4209_; lean_object* v___x_4210_; 
v_recover_4209_ = lean_ctor_get_uint8(v_a_4202_, sizeof(void*)*1);
v___x_4210_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4207_, v_init_4200_, v_cfg_4199_, v_onErr_4206_, v_recover_4209_, v_a_4203_, v_a_4204_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4211_, lean_object* v_init_4212_, lean_object* v_logExceptions_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
uint8_t v_logExceptions_boxed_4218_; lean_object* v_res_4219_; 
v_logExceptions_boxed_4218_ = lean_unbox(v_logExceptions_4213_);
v_res_4219_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4211_, v_init_4212_, v_logExceptions_boxed_4218_, v_a_4214_, v_a_4215_, v_a_4216_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4220_, lean_object* v_init_4221_, uint8_t v_logExceptions_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4220_, v_init_4221_, v_logExceptions_4222_, v_a_4223_, v_a_4229_, v_a_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4233_, lean_object* v_init_4234_, lean_object* v_logExceptions_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
uint8_t v_logExceptions_boxed_4245_; lean_object* v_res_4246_; 
v_logExceptions_boxed_4245_ = lean_unbox(v_logExceptions_4235_);
v_res_4246_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4233_, v_init_4234_, v_logExceptions_boxed_4245_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
return v_res_4246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4254_ = l_Lean_MessageData_ofFormat(v___x_4253_);
return v___x_4254_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4268_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4269_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4267_, v_x_4257_, v___x_4268_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4281_, uint8_t v_symm_4282_, lean_object* v_a_4283_, lean_object* v_x_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4281_, v_symm_4282_, v_x_4284_, v_a_4283_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4295_, lean_object* v_symm_4296_, lean_object* v_a_4297_, lean_object* v_x_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
uint8_t v_symm_boxed_4308_; lean_object* v_res_4309_; 
v_symm_boxed_4308_ = lean_unbox(v_symm_4296_);
v_res_4309_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4295_, v_symm_boxed_4308_, v_a_4297_, v_x_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4310_, lean_object* v___x_4311_, lean_object* v___f_4312_, uint8_t v_symm_4313_, lean_object* v_term_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; lean_object* v___f_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4324_ = lean_box(v_symm_4313_);
lean_inc_ref(v_a_4310_);
lean_inc(v_term_4314_);
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4325_, 0, v_term_4314_);
lean_closure_set(v___f_4325_, 1, v___x_4324_);
lean_closure_set(v___f_4325_, 2, v_a_4310_);
v___x_4326_ = lean_box(v_symm_4313_);
v___x_4327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4327_, 0, v_term_4314_);
lean_closure_set(v___x_4327_, 1, v___x_4326_);
lean_closure_set(v___x_4327_, 2, v_a_4310_);
v___x_4328_ = l_Lean_Elab_Tactic_withLocation(v___x_4311_, v___f_4325_, v___x_4327_, v___f_4312_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4329_, lean_object* v___x_4330_, lean_object* v___f_4331_, lean_object* v_symm_4332_, lean_object* v_term_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
uint8_t v_symm_boxed_4343_; lean_object* v_res_4344_; 
v_symm_boxed_4343_ = lean_unbox(v_symm_4332_);
v_res_4344_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4329_, v___x_4330_, v___f_4331_, v_symm_boxed_4343_, v_term_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___x_4330_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = l_Lean_Syntax_getArg(v_stx_4351_, v___x_4361_);
v___x_4363_ = 1;
v___x_4364_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4365_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4362_, v___x_4364_, v___x_4363_, v_a_4352_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___f_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v___f_4367_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4368_ = lean_unsigned_to_nat(3u);
v___x_4369_ = l_Lean_Syntax_getArg(v_stx_4351_, v___x_4368_);
v___x_4370_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4369_);
lean_dec(v___x_4369_);
v___f_4371_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4371_, 0, v_a_4366_);
lean_closure_set(v___f_4371_, 1, v___x_4370_);
lean_closure_set(v___f_4371_, 2, v___f_4367_);
v___x_4372_ = lean_unsigned_to_nat(0u);
v___x_4373_ = l_Lean_Syntax_getArg(v_stx_4351_, v___x_4372_);
v___x_4374_ = lean_unsigned_to_nat(2u);
v___x_4375_ = l_Lean_Syntax_getArg(v_stx_4351_, v___x_4374_);
v___x_4376_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4373_, v___x_4375_, v___f_4371_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
lean_dec(v___x_4375_);
return v___x_4376_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v_a_4377_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4365_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4365_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_stx_4385_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4411_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4414_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4415_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4411_, v___x_4412_, v___x_4413_, v___x_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4446_ = l_Lean_addBuiltinDeclarationRanges(v___x_4444_, v___x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4448_;
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
