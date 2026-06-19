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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 312, .m_capacity = 312, .m_length = 311, .m_data = "The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.\nFull error:"};
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to rewrite using equation theorems for `"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Try rewriting with `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Rewrite"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 107, 61, 219, 24, 145, 46, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 84, 11, 37, 124, 73, 156, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 52, 185, 71, 227, 101, 217, 44)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 82, 208, 43, 125, 37, 174, 61)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 125, 72, 83, 103, 118, 157, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalRewriteSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
uint8_t v___x_12854__boxed_70_; lean_object* v_res_71_; 
v___x_12854__boxed_70_ = lean_unbox(v___x_64_);
v_res_71_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_63_, v___x_12854__boxed_70_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
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
v___x_87_ = 3;
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
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_nbuckets_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_307_ = lean_array_get_size(v_data_306_);
v___x_308_ = lean_unsigned_to_nat(2u);
v_nbuckets_309_ = lean_nat_mul(v___x_307_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_box(0);
v___x_312_ = lean_mk_array(v_nbuckets_309_, v___x_311_);
v___x_313_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v___x_310_, v_data_306_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_m_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_size_317_; lean_object* v_buckets_318_; lean_object* v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v_fold_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v_bkt_332_; uint8_t v___x_333_; 
v_size_317_ = lean_ctor_get(v_m_314_, 0);
v_buckets_318_ = lean_ctor_get(v_m_314_, 1);
v___x_319_ = lean_array_get_size(v_buckets_318_);
v___x_320_ = l_Lean_Expr_hash(v_a_315_);
v___x_321_ = 32ULL;
v___x_322_ = lean_uint64_shift_right(v___x_320_, v___x_321_);
v_fold_323_ = lean_uint64_xor(v___x_320_, v___x_322_);
v___x_324_ = 16ULL;
v___x_325_ = lean_uint64_shift_right(v_fold_323_, v___x_324_);
v___x_326_ = lean_uint64_xor(v_fold_323_, v___x_325_);
v___x_327_ = lean_uint64_to_usize(v___x_326_);
v___x_328_ = lean_usize_of_nat(v___x_319_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_sub(v___x_328_, v___x_329_);
v___x_331_ = lean_usize_land(v___x_327_, v___x_330_);
v_bkt_332_ = lean_array_uget_borrowed(v_buckets_318_, v___x_331_);
v___x_333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_315_, v_bkt_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_354_; 
lean_inc_ref(v_buckets_318_);
lean_inc(v_size_317_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_m_314_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_m_314_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_m_314_, 0);
lean_dec(v_unused_356_);
v___x_335_ = v_m_314_;
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
else
{
lean_dec(v_m_314_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v_size_x27_338_; lean_object* v___x_339_; lean_object* v_buckets_x27_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v_size_x27_338_ = lean_nat_add(v_size_317_, v___x_337_);
lean_dec(v_size_317_);
lean_inc(v_bkt_332_);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v_a_315_);
lean_ctor_set(v___x_339_, 1, v_b_316_);
lean_ctor_set(v___x_339_, 2, v_bkt_332_);
v_buckets_x27_340_ = lean_array_uset(v_buckets_318_, v___x_331_, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(4u);
v___x_342_ = lean_nat_mul(v_size_x27_338_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(3u);
v___x_344_ = lean_nat_div(v___x_342_, v___x_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_array_get_size(v_buckets_x27_340_);
v___x_346_ = lean_nat_dec_le(v___x_344_, v___x_345_);
lean_dec(v___x_344_);
if (v___x_346_ == 0)
{
lean_object* v_val_347_; lean_object* v___x_349_; 
v_val_347_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_buckets_x27_340_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_347_);
lean_ctor_set(v___x_335_, 0, v_size_x27_338_);
v___x_349_ = v___x_335_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_size_x27_338_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_val_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
else
{
lean_object* v___x_352_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_340_);
lean_ctor_set(v___x_335_, 0, v_size_x27_338_);
v___x_352_ = v___x_335_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_size_x27_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_buckets_x27_340_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_dec(v_b_316_);
lean_dec_ref(v_a_315_);
return v_m_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(lean_object* v_mvarId_361_, lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_d_374_; lean_object* v_b_375_; lean_object* v___y_376_; uint8_t v___x_382_; 
v___x_382_ = l_Lean_Expr_hasExprMVar(v_e_362_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_e_362_);
v___x_383_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_a_363_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_363_, v_e_362_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_box(0);
lean_inc_ref(v_e_362_);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_363_, v_e_362_, v___x_387_);
switch(lean_obj_tag(v_e_362_))
{
case 11:
{
lean_object* v_struct_389_; 
v_struct_389_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_struct_389_);
lean_dec_ref_known(v_e_362_, 3);
v_e_362_ = v_struct_389_;
v_a_363_ = v___x_388_;
goto _start;
}
case 7:
{
lean_object* v_binderType_391_; lean_object* v_body_392_; 
v_binderType_391_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_binderType_391_);
v_body_392_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_392_);
lean_dec_ref_known(v_e_362_, 3);
v_d_374_ = v_binderType_391_;
v_b_375_ = v_body_392_;
v___y_376_ = v___x_388_;
goto v___jp_373_;
}
case 6:
{
lean_object* v_binderType_393_; lean_object* v_body_394_; 
v_binderType_393_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_binderType_393_);
v_body_394_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_394_);
lean_dec_ref_known(v_e_362_, 3);
v_d_374_ = v_binderType_393_;
v_b_375_ = v_body_394_;
v___y_376_ = v___x_388_;
goto v___jp_373_;
}
case 8:
{
lean_object* v_type_395_; lean_object* v_value_396_; lean_object* v_body_397_; lean_object* v___x_398_; 
v_type_395_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_type_395_);
v_value_396_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_value_396_);
v_body_397_ = lean_ctor_get(v_e_362_, 3);
lean_inc_ref(v_body_397_);
lean_dec_ref_known(v_e_362_, 4);
v___x_398_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_type_395_, v___x_388_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v_fst_400_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
v_fst_400_ = lean_ctor_get(v_a_399_, 0);
if (lean_obj_tag(v_fst_400_) == 0)
{
lean_dec(v_a_399_);
lean_dec_ref(v_body_397_);
lean_dec_ref(v_value_396_);
return v___x_398_;
}
else
{
lean_object* v_snd_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_398_, 1);
v_snd_401_ = lean_ctor_get(v_a_399_, 1);
lean_inc(v_snd_401_);
lean_dec(v_a_399_);
v___x_402_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_value_396_, v_snd_401_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_fst_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
v_fst_404_ = lean_ctor_get(v_a_403_, 0);
if (lean_obj_tag(v_fst_404_) == 0)
{
lean_dec(v_a_403_);
lean_dec_ref(v_body_397_);
return v___x_402_;
}
else
{
lean_object* v_snd_405_; 
lean_dec_ref_known(v___x_402_, 1);
v_snd_405_ = lean_ctor_get(v_a_403_, 1);
lean_inc(v_snd_405_);
lean_dec(v_a_403_);
v_e_362_ = v_body_397_;
v_a_363_ = v_snd_405_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_397_);
return v___x_402_;
}
}
}
else
{
lean_dec_ref(v_body_397_);
lean_dec_ref(v_value_396_);
return v___x_398_;
}
}
case 10:
{
lean_object* v_expr_407_; 
v_expr_407_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_expr_407_);
lean_dec_ref_known(v_e_362_, 2);
v_e_362_ = v_expr_407_;
v_a_363_ = v___x_388_;
goto _start;
}
case 5:
{
lean_object* v_fn_409_; lean_object* v_arg_410_; lean_object* v___x_411_; 
v_fn_409_ = lean_ctor_get(v_e_362_, 0);
lean_inc_ref(v_fn_409_);
v_arg_410_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_arg_410_);
lean_dec_ref_known(v_e_362_, 2);
v___x_411_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_fn_409_, v___x_388_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_fst_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
v_fst_413_ = lean_ctor_get(v_a_412_, 0);
if (lean_obj_tag(v_fst_413_) == 0)
{
lean_dec(v_a_412_);
lean_dec_ref(v_arg_410_);
return v___x_411_;
}
else
{
lean_object* v_snd_414_; 
lean_dec_ref_known(v___x_411_, 1);
v_snd_414_ = lean_ctor_get(v_a_412_, 1);
lean_inc(v_snd_414_);
lean_dec(v_a_412_);
v_e_362_ = v_arg_410_;
v_a_363_ = v_snd_414_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_410_);
return v___x_411_;
}
}
case 2:
{
lean_object* v_mvarId_416_; lean_object* v___x_417_; 
v_mvarId_416_ = lean_ctor_get(v_e_362_, 0);
lean_inc(v_mvarId_416_);
lean_dec_ref_known(v_e_362_, 1);
v___x_417_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_361_, v_mvarId_416_, v___x_388_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_417_;
}
default: 
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v_e_362_);
v___x_418_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_388_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_e_362_);
v___x_421_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_363_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
v___jp_373_:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_d_374_, v___y_376_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v_fst_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
v_fst_379_ = lean_ctor_get(v_a_378_, 0);
if (lean_obj_tag(v_fst_379_) == 0)
{
lean_dec(v_a_378_);
lean_dec_ref(v_b_375_);
return v___x_377_;
}
else
{
lean_object* v_snd_380_; 
lean_dec_ref_known(v___x_377_, 1);
v_snd_380_ = lean_ctor_get(v_a_378_, 1);
lean_inc(v_snd_380_);
lean_dec(v_a_378_);
v_e_362_ = v_b_375_;
v_a_363_ = v_snd_380_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_375_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(lean_object* v_mvarId_424_, lean_object* v_mvarId_x27_425_, lean_object* v_a_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_instBEqMVarId_beq(v_mvarId_424_, v_mvarId_x27_425_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_x27_425_, v_a_426_, v___y_432_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_521_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_521_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_521_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_521_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_fst_442_; 
v_fst_442_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_fst_442_);
if (lean_obj_tag(v_fst_442_) == 0)
{
lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_mvarId_x27_425_);
v_snd_443_ = lean_ctor_get(v_a_438_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_a_438_, 0);
lean_dec(v_unused_462_);
v___x_445_ = v_a_438_;
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_dec(v_a_438_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_460_; 
v_a_447_ = lean_ctor_get(v_fst_442_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_fst_442_);
if (v_isSharedCheck_460_ == 0)
{
v___x_449_ = v_fst_442_;
v_isShared_450_ = v_isSharedCheck_460_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_fst_442_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_460_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_459_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_452_);
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_snd_443_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_454_);
v___x_456_ = v___x_440_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
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
else
{
lean_object* v_a_463_; 
lean_del_object(v___x_440_);
v_a_463_ = lean_ctor_get(v_fst_442_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v_fst_442_, 1);
if (lean_obj_tag(v_a_463_) == 0)
{
lean_object* v_snd_464_; lean_object* v___x_465_; 
v_snd_464_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_464_);
lean_dec(v_a_438_);
v___x_465_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_x27_425_, v_snd_464_, v___y_432_);
lean_dec(v_mvarId_x27_425_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_509_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_509_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_fst_470_; 
v_fst_470_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_fst_470_);
if (lean_obj_tag(v_fst_470_) == 0)
{
lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_489_; 
v_snd_471_ = lean_ctor_get(v_a_466_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_a_466_, 0);
lean_dec(v_unused_490_);
v___x_473_ = v_a_466_;
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_dec(v_a_466_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_488_; 
v_a_475_ = lean_ctor_get(v_fst_470_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_fst_470_);
if (v_isSharedCheck_488_ == 0)
{
v___x_477_ = v_fst_470_;
v_isShared_478_ = v_isSharedCheck_488_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v_fst_470_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_488_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_487_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_480_);
v___x_482_ = v___x_473_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_snd_471_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_482_);
v___x_484_ = v___x_468_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
else
{
lean_object* v_a_491_; 
v_a_491_ = lean_ctor_get(v_fst_470_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_fst_470_, 1);
if (lean_obj_tag(v_a_491_) == 0)
{
lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_503_; 
v_snd_492_ = lean_ctor_get(v_a_466_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_a_466_, 0);
lean_dec(v_unused_504_);
v___x_494_ = v_a_466_;
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_dec(v_a_466_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_snd_492_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_498_);
v___x_500_ = v___x_468_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
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
else
{
lean_object* v_val_505_; lean_object* v_snd_506_; lean_object* v_mvarIdPending_507_; 
lean_del_object(v___x_468_);
v_val_505_ = lean_ctor_get(v_a_491_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_a_491_, 1);
v_snd_506_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_snd_506_);
lean_dec(v_a_466_);
v_mvarIdPending_507_ = lean_ctor_get(v_val_505_, 1);
lean_inc(v_mvarIdPending_507_);
lean_dec(v_val_505_);
v_mvarId_x27_425_ = v_mvarIdPending_507_;
v_a_426_ = v_snd_506_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_465_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_465_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_snd_518_; lean_object* v_val_519_; lean_object* v___x_520_; 
lean_dec(v_mvarId_x27_425_);
v_snd_518_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_518_);
lean_dec(v_a_438_);
v_val_519_ = lean_ctor_get(v_a_463_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_a_463_, 1);
v___x_520_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_424_, v_val_519_, v_snd_518_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_mvarId_x27_425_);
v_a_522_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_437_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_437_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_mvarId_x27_425_);
v___x_530_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1));
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_a_426_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(lean_object* v_mvarId_533_, lean_object* v_mvarId_x27_534_, lean_object* v_a_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_533_, v_mvarId_x27_534_, v_a_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v_mvarId_533_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(lean_object* v_mvarId_546_, lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_546_, v_e_547_, v_a_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v_mvarId_546_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_unsigned_to_nat(16u);
v___x_561_ = lean_mk_array(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_mvarId_565_, lean_object* v_e_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = l_Lean_Expr_hasExprMVar(v_e_566_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_e_566_);
v___x_577_ = 1;
v___x_578_ = lean_box(v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
v___x_581_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_565_, v_e_566_, v___x_580_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_596_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_596_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_fst_586_; 
v_fst_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_fst_586_);
lean_dec(v_a_582_);
if (lean_obj_tag(v_fst_586_) == 0)
{
uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec_ref_known(v_fst_586_, 1);
v___x_587_ = 0;
v___x_588_ = lean_box(v___x_587_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_588_);
v___x_590_ = v___x_584_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_dec_ref_known(v_fst_586_, 1);
v___x_592_ = lean_box(v___x_576_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_592_);
v___x_594_ = v___x_584_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_581_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_581_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_mvarId_605_, lean_object* v_e_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_605_, v_e_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v_mvarId_605_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
if (lean_obj_tag(v_a_619_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = l_List_reverse___redArg(v_a_620_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_head_622_ = lean_ctor_get(v_a_619_, 0);
v_tail_623_ = lean_ctor_get(v_a_619_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_635_ == 0)
{
v___x_625_ = v_a_619_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_head_622_);
lean_dec(v_a_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v_index_628_; uint8_t v___x_629_; 
lean_inc(v_head_622_);
v___x_627_ = l_Lean_MetavarContext_getDecl(v___x_617_, v_head_622_);
v_index_628_ = lean_ctor_get(v___x_627_, 6);
lean_inc(v_index_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_nat_dec_le(v___x_618_, v_index_628_);
lean_dec(v_index_628_);
if (v___x_629_ == 0)
{
lean_del_object(v___x_625_);
lean_dec(v_head_622_);
v_a_619_ = v_tail_623_;
goto _start;
}
else
{
lean_object* v___x_632_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_a_620_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_head_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_a_620_);
v___x_632_ = v_reuseFailAlloc_634_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
v_a_619_ = v_tail_623_;
v_a_620_ = v___x_632_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v___x_636_, v___x_637_, v_a_638_, v_a_639_);
lean_dec(v___x_637_);
lean_dec_ref(v___x_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(lean_object* v_msgData_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v_mctx_650_; lean_object* v_lctx_651_; lean_object* v_options_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_647_ = lean_st_ref_get(v___y_645_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_643_);
v_mctx_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_mctx_650_);
lean_dec(v___x_649_);
v_lctx_651_ = lean_ctor_get(v___y_642_, 2);
v_options_652_ = lean_ctor_get(v___y_644_, 2);
lean_inc_ref(v_options_652_);
lean_inc_ref(v_lctx_651_);
v___x_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_653_, 0, v_env_648_);
lean_ctor_set(v___x_653_, 1, v_mctx_650_);
lean_ctor_set(v___x_653_, 2, v_lctx_651_);
lean_ctor_set(v___x_653_, 3, v_options_652_);
v___x_654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_msgData_641_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object* v_msgData_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_ref_669_ = lean_ctor_get(v___y_666_, 5);
v___x_670_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_ref_669_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_ref_669_);
lean_ctor_set(v___x_675_, 1, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object* v_ref_687_, lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_fileName_698_; lean_object* v_fileMap_699_; lean_object* v_options_700_; lean_object* v_currRecDepth_701_; lean_object* v_maxRecDepth_702_; lean_object* v_ref_703_; lean_object* v_currNamespace_704_; lean_object* v_openDecls_705_; lean_object* v_initHeartbeats_706_; lean_object* v_maxHeartbeats_707_; lean_object* v_quotContext_708_; lean_object* v_currMacroScope_709_; uint8_t v_diag_710_; lean_object* v_cancelTk_x3f_711_; uint8_t v_suppressElabErrors_712_; lean_object* v_inheritedTraceOptions_713_; lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_fileName_698_ = lean_ctor_get(v___y_695_, 0);
v_fileMap_699_ = lean_ctor_get(v___y_695_, 1);
v_options_700_ = lean_ctor_get(v___y_695_, 2);
v_currRecDepth_701_ = lean_ctor_get(v___y_695_, 3);
v_maxRecDepth_702_ = lean_ctor_get(v___y_695_, 4);
v_ref_703_ = lean_ctor_get(v___y_695_, 5);
v_currNamespace_704_ = lean_ctor_get(v___y_695_, 6);
v_openDecls_705_ = lean_ctor_get(v___y_695_, 7);
v_initHeartbeats_706_ = lean_ctor_get(v___y_695_, 8);
v_maxHeartbeats_707_ = lean_ctor_get(v___y_695_, 9);
v_quotContext_708_ = lean_ctor_get(v___y_695_, 10);
v_currMacroScope_709_ = lean_ctor_get(v___y_695_, 11);
v_diag_710_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*14);
v_cancelTk_x3f_711_ = lean_ctor_get(v___y_695_, 12);
v_suppressElabErrors_712_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_713_ = lean_ctor_get(v___y_695_, 13);
v_ref_714_ = l_Lean_replaceRef(v_ref_687_, v_ref_703_);
lean_inc_ref(v_inheritedTraceOptions_713_);
lean_inc(v_cancelTk_x3f_711_);
lean_inc(v_currMacroScope_709_);
lean_inc(v_quotContext_708_);
lean_inc(v_maxHeartbeats_707_);
lean_inc(v_initHeartbeats_706_);
lean_inc(v_openDecls_705_);
lean_inc(v_currNamespace_704_);
lean_inc(v_maxRecDepth_702_);
lean_inc(v_currRecDepth_701_);
lean_inc_ref(v_options_700_);
lean_inc_ref(v_fileMap_699_);
lean_inc_ref(v_fileName_698_);
v___x_715_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_715_, 0, v_fileName_698_);
lean_ctor_set(v___x_715_, 1, v_fileMap_699_);
lean_ctor_set(v___x_715_, 2, v_options_700_);
lean_ctor_set(v___x_715_, 3, v_currRecDepth_701_);
lean_ctor_set(v___x_715_, 4, v_maxRecDepth_702_);
lean_ctor_set(v___x_715_, 5, v_ref_714_);
lean_ctor_set(v___x_715_, 6, v_currNamespace_704_);
lean_ctor_set(v___x_715_, 7, v_openDecls_705_);
lean_ctor_set(v___x_715_, 8, v_initHeartbeats_706_);
lean_ctor_set(v___x_715_, 9, v_maxHeartbeats_707_);
lean_ctor_set(v___x_715_, 10, v_quotContext_708_);
lean_ctor_set(v___x_715_, 11, v_currMacroScope_709_);
lean_ctor_set(v___x_715_, 12, v_cancelTk_x3f_711_);
lean_ctor_set(v___x_715_, 13, v_inheritedTraceOptions_713_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*14, v_diag_710_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*14 + 1, v_suppressElabErrors_712_);
v___x_716_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_688_, v___y_693_, v___y_694_, v___x_715_, v___y_696_);
lean_dec_ref_known(v___x_715_, 14);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_717_, v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v_ref_717_);
return v_res_728_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_731_ = l_Lean_stringToMessageData(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_735_, lean_object* v_e_736_, lean_object* v_stx_737_, uint8_t v_symm_738_, lean_object* v_config_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_st_ref_get(v_a_745_);
v___x_750_ = lean_box(0);
v___x_751_ = 1;
lean_inc(v_stx_737_);
v___x_752_ = l_Lean_Elab_Tactic_elabTerm(v_stx_737_, v___x_750_, v___x_751_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_mctx_753_; lean_object* v_a_754_; lean_object* v_mvarCounter_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___x_827_; 
v_mctx_753_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_mctx_753_);
lean_dec(v___x_749_);
v_a_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc_n(v_a_754_, 2);
lean_dec_ref_known(v___x_752_, 1);
v_mvarCounter_755_ = lean_ctor_get(v_mctx_753_, 3);
lean_inc(v_mvarCounter_755_);
lean_dec_ref(v_mctx_753_);
v___x_756_ = lean_box(v_symm_738_);
lean_inc_ref(v_e_736_);
lean_inc(v_mvarId_735_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_757_, 0, v_mvarId_735_);
lean_closure_set(v___f_757_, 1, v_e_736_);
lean_closure_set(v___f_757_, 2, v_a_754_);
lean_closure_set(v___f_757_, 3, v___x_756_);
lean_closure_set(v___f_757_, 4, v_config_739_);
v___x_827_ = l_Lean_Expr_hasSyntheticSorry(v_a_754_);
if (v___x_827_ == 0)
{
v___y_791_ = v_a_740_;
v___y_792_ = v_a_741_;
v___y_793_ = v_a_742_;
v___y_794_ = v_a_743_;
v___y_795_ = v_a_744_;
v___y_796_ = v_a_745_;
v___y_797_ = v_a_746_;
v___y_798_ = v_a_747_;
goto v___jp_790_;
}
else
{
lean_object* v___x_828_; lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v___f_757_);
lean_dec(v_mvarCounter_755_);
lean_dec(v_a_754_);
lean_dec(v_stx_737_);
lean_dec_ref(v_e_736_);
lean_dec(v_mvarId_735_);
v___x_828_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
v___jp_758_:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_736_, v___f_757_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_789_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_789_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_mctx_773_; lean_object* v_eNew_774_; lean_object* v_eqProof_775_; lean_object* v_mvarIds_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_788_; 
v___x_772_ = lean_st_ref_get(v___y_764_);
v_mctx_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_mctx_773_);
lean_dec(v___x_772_);
v_eNew_774_ = lean_ctor_get(v_a_768_, 0);
v_eqProof_775_ = lean_ctor_get(v_a_768_, 1);
v_mvarIds_776_ = lean_ctor_get(v_a_768_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_768_);
if (v_isSharedCheck_788_ == 0)
{
v___x_778_ = v_a_768_;
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_mvarIds_776_);
lean_inc(v_eqProof_775_);
lean_inc(v_eNew_774_);
lean_dec(v_a_768_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_773_, v_mvarCounter_755_, v_mvarIds_776_, v___x_780_);
lean_dec(v_mvarCounter_755_);
lean_dec_ref(v_mctx_773_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 2, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_eNew_774_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_eqProof_775_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v___x_781_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_783_);
v___x_785_ = v___x_770_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_755_);
return v___x_767_;
}
}
v___jp_790_:
{
lean_object* v___x_799_; 
lean_inc(v_a_754_);
v___x_799_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_735_, v_a_754_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; uint8_t v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v___f_757_);
lean_dec(v_mvarCounter_755_);
lean_dec_ref(v_e_736_);
v___x_802_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_803_ = l_Lean_indentExpr(v_a_754_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_Expr_mvar___override(v_mvarId_735_);
v___x_808_ = l_Lean_MessageData_ofExpr(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_737_, v___x_809_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v_stx_737_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_dec(v_a_754_);
lean_dec(v_stx_737_);
lean_dec(v_mvarId_735_);
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
v___y_763_ = v___y_795_;
v___y_764_ = v___y_796_;
v___y_765_ = v___y_797_;
v___y_766_ = v___y_798_;
goto v___jp_758_;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v___f_757_);
lean_dec(v_mvarCounter_755_);
lean_dec(v_a_754_);
lean_dec(v_stx_737_);
lean_dec_ref(v_e_736_);
lean_dec(v_mvarId_735_);
v_a_819_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_799_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_799_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v___x_749_);
lean_dec_ref(v_config_739_);
lean_dec(v_stx_737_);
lean_dec_ref(v_e_736_);
lean_dec(v_mvarId_735_);
v_a_837_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_752_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_752_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_845_, lean_object* v_e_846_, lean_object* v_stx_847_, lean_object* v_symm_848_, lean_object* v_config_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_symm_boxed_859_; lean_object* v_res_860_; 
v_symm_boxed_859_ = lean_unbox(v_symm_848_);
v_res_860_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_845_, v_e_846_, v_stx_847_, v_symm_boxed_859_, v_config_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_861_, lean_object* v_ref_862_, lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_862_, v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_874_, lean_object* v_ref_875_, lean_object* v_msg_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_874_, v_ref_875_, v_msg_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v_ref_875_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_887_, lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_888_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_899_, v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_910_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_911_, lean_object* v_m_912_, lean_object* v_a_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_912_, v_a_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_915_, v_m_916_, v_a_917_);
lean_dec_ref(v_a_917_);
lean_dec_ref(v_m_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_920_, lean_object* v_m_921_, lean_object* v_a_922_, lean_object* v_b_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_921_, v_a_922_, v_b_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_925_, v___y_926_, v___y_932_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v_mvarId_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_949_, v___y_950_, v___y_956_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v_mvarId_961_);
return v_res_972_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_973_, lean_object* v_a_974_, lean_object* v_x_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_977_, lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
uint8_t v_res_980_; lean_object* v_r_981_; 
v_res_980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_977_, v_a_978_, v_x_979_);
lean_dec(v_x_979_);
lean_dec_ref(v_a_978_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_982_, lean_object* v_data_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_985_, lean_object* v_i_986_, lean_object* v_source_987_, lean_object* v_target_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_986_, v_source_987_, v_target_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1026_, lean_object* v_mvarId_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_mvarId_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1035_, v_mvarId_1036_, v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_array_get_size(v_keys_1044_);
v___x_1048_ = lean_nat_dec_lt(v_i_1045_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_i_1045_);
return v___x_1048_;
}
else
{
lean_object* v_k_x27_1049_; uint8_t v___x_1050_; 
v_k_x27_1049_ = lean_array_fget_borrowed(v_keys_1044_, v_i_1045_);
v___x_1050_ = l_Lean_instBEqMVarId_beq(v_k_1046_, v_k_x27_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_nat_add(v_i_1045_, v___x_1051_);
lean_dec(v_i_1045_);
v_i_1045_ = v___x_1052_;
goto _start;
}
else
{
lean_dec(v_i_1045_);
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1054_, lean_object* v_i_1055_, lean_object* v_k_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1054_, v_i_1055_, v_k_1056_);
lean_dec(v_k_1056_);
lean_dec_ref(v_keys_1054_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; 
v___x_1059_ = ((size_t)5ULL);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_shift_left(v___x_1060_, v___x_1059_);
return v___x_1061_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1064_ = lean_usize_sub(v___x_1063_, v___x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v_es_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; lean_object* v_j_1073_; lean_object* v___x_1074_; 
v_es_1068_ = lean_ctor_get(v_x_1065_, 0);
v___x_1069_ = lean_box(2);
v___x_1070_ = ((size_t)5ULL);
v___x_1071_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1072_ = lean_usize_land(v_x_1066_, v___x_1071_);
v_j_1073_ = lean_usize_to_nat(v___x_1072_);
v___x_1074_ = lean_array_get_borrowed(v___x_1069_, v_es_1068_, v_j_1073_);
lean_dec(v_j_1073_);
switch(lean_obj_tag(v___x_1074_))
{
case 0:
{
lean_object* v_key_1075_; uint8_t v___x_1076_; 
v_key_1075_ = lean_ctor_get(v___x_1074_, 0);
v___x_1076_ = l_Lean_instBEqMVarId_beq(v_x_1067_, v_key_1075_);
return v___x_1076_;
}
case 1:
{
lean_object* v_node_1077_; size_t v___x_1078_; 
v_node_1077_ = lean_ctor_get(v___x_1074_, 0);
v___x_1078_ = lean_usize_shift_right(v_x_1066_, v___x_1070_);
v_x_1065_ = v_node_1077_;
v_x_1066_ = v___x_1078_;
goto _start;
}
default: 
{
uint8_t v___x_1080_; 
v___x_1080_ = 0;
return v___x_1080_;
}
}
}
else
{
lean_object* v_ks_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_ks_1081_ = lean_ctor_get(v_x_1065_, 0);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1081_, v___x_1082_, v_x_1067_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
size_t v_x_1972__boxed_1087_; uint8_t v_res_1088_; lean_object* v_r_1089_; 
v_x_1972__boxed_1087_ = lean_unbox_usize(v_x_1085_);
lean_dec(v_x_1085_);
v_res_1088_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1084_, v_x_1972__boxed_1087_, v_x_1086_);
lean_dec(v_x_1086_);
lean_dec_ref(v_x_1084_);
v_r_1089_ = lean_box(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
uint64_t v___x_1092_; size_t v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = l_Lean_instHashableMVarId_hash(v_x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1090_, v___x_1093_, v_x_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_res_1097_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1095_, v_x_1096_);
lean_dec(v_x_1096_);
lean_dec_ref(v_x_1095_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_mctx_1103_; lean_object* v_eAssignment_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_mctx_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_mctx_1103_);
lean_dec(v___x_1102_);
v_eAssignment_1104_ = lean_ctor_get(v_mctx_1103_, 8);
lean_inc_ref(v_eAssignment_1104_);
lean_dec_ref(v_mctx_1103_);
v___x_1105_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1104_, v_mvarId_1099_);
lean_dec_ref(v_eAssignment_1104_);
v___x_1106_ = lean_box(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec(v_mvarId_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_x_1113_);
return v___x_1119_;
}
else
{
lean_object* v_head_1120_; lean_object* v_tail_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1134_; 
v_head_1120_ = lean_ctor_get(v_x_1112_, 0);
v_tail_1121_ = lean_ctor_get(v_x_1112_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1123_ = v_x_1112_;
v_isShared_1124_ = v_isSharedCheck_1134_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_tail_1121_);
lean_inc(v_head_1120_);
lean_dec(v_x_1112_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1134_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1130_; lean_object* v_a_1131_; uint8_t v___x_1132_; 
v___x_1130_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1120_, v___y_1115_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1132_ == 0)
{
goto v___jp_1125_;
}
else
{
lean_del_object(v___x_1123_);
lean_dec(v_head_1120_);
v_x_1112_ = v_tail_1121_;
goto _start;
}
v___jp_1125_:
{
lean_object* v___x_1127_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v_x_1113_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_head_1120_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_x_1113_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v_x_1112_ = v_tail_1121_;
v_x_1113_ = v___x_1127_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1135_, v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
lean_inc(v_head_1143_);
v___x_1149_ = l_Lean_MVarId_getType(v_head_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_Meta_isProp(v_a_1150_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1163_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_unbox(v_a_1152_);
lean_dec(v_a_1152_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v_head_1143_);
v___x_1157_ = lean_box(0);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
uint8_t v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1154_);
v___x_1161_ = 2;
v___x_1162_ = l_Lean_MVarId_setKind___redArg(v_head_1143_, v___x_1161_, v___y_1145_);
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_head_1143_);
v_a_1164_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1151_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1151_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_head_1143_);
v_a_1172_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1149_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1149_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
if (lean_obj_tag(v_as_1187_) == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v_head_1195_; lean_object* v_tail_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_head_1195_ = lean_ctor_get(v_as_1187_, 0);
lean_inc_n(v_head_1195_, 2);
v_tail_1196_ = lean_ctor_get(v_as_1187_, 1);
lean_inc(v_tail_1196_);
lean_dec_ref_known(v_as_1187_, 2);
v___f_1197_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1197_, 0, v_head_1195_);
v___x_1198_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1195_, v___f_1197_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_dec_ref_known(v___x_1198_, 1);
v_as_1187_ = v_tail_1196_;
goto _start;
}
else
{
lean_dec(v_tail_1196_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_eNew_1213_; lean_object* v_eqProof_1214_; lean_object* v_mvarIds_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1254_; 
v_eNew_1213_ = lean_ctor_get(v_r_1207_, 0);
v_eqProof_1214_ = lean_ctor_get(v_r_1207_, 1);
v_mvarIds_1215_ = lean_ctor_get(v_r_1207_, 2);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_r_1207_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1217_ = v_r_1207_;
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_mvarIds_1215_);
lean_inc(v_eqProof_1214_);
lean_inc(v_eNew_1213_);
lean_dec(v_r_1207_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_a_1220_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1215_, v___x_1241_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_List_reverse___redArg(v_a_1243_);
v_a_1220_ = v___x_1244_;
goto v___jp_1219_;
}
else
{
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1245_; 
v_a_1245_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1242_, 1);
v_a_1220_ = v_a_1245_;
goto v___jp_1219_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_del_object(v___x_1217_);
lean_dec_ref(v_eqProof_1214_);
lean_dec_ref(v_eNew_1213_);
v_a_1246_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1242_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1242_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
v___jp_1219_:
{
lean_object* v___x_1221_; 
lean_inc(v_a_1220_);
v___x_1221_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1220_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1232_);
v___x_1223_ = v___x_1221_;
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v___x_1221_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 2, v_a_1220_);
v___x_1226_ = v___x_1217_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_eNew_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_eqProof_1214_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_a_1220_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1220_);
lean_del_object(v___x_1217_);
lean_dec_ref(v_eqProof_1214_);
lean_dec_ref(v_eNew_1213_);
v_a_1233_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1221_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1221_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1262_, v___y_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v_mvarId_1269_);
return v_res_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1277_, v_x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1280_, v_x_1281_, v_x_1282_);
lean_dec(v_x_1282_);
lean_dec_ref(v_x_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, size_t v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1286_, v_x_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
size_t v_x_2317__boxed_1294_; uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_x_2317__boxed_1294_ = lean_unbox_usize(v_x_1292_);
lean_dec(v_x_1292_);
v_res_1295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1290_, v_x_1291_, v_x_2317__boxed_1294_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec_ref(v_x_1291_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1297_, lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_heq_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1298_, v_i_1301_, v_k_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_keys_1305_, lean_object* v_vals_1306_, lean_object* v_heq_1307_, lean_object* v_i_1308_, lean_object* v_k_1309_){
_start:
{
uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_res_1310_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1304_, v_keys_1305_, v_vals_1306_, v_heq_1307_, v_i_1308_, v_k_1309_);
lean_dec(v_k_1309_);
lean_dec_ref(v_vals_1306_);
lean_dec_ref(v_keys_1305_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1312_, uint8_t v_symm_1313_, lean_object* v_config_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1316_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1325_, v_a_1327_, v_stx_1312_, v_symm_1313_, v_config_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v___x_1328_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1325_);
lean_dec_ref(v_config_1314_);
lean_dec(v_stx_1312_);
v_a_1329_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1326_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1326_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
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
lean_dec_ref(v_config_1314_);
lean_dec(v_stx_1312_);
v_a_1337_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1324_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1324_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1345_, lean_object* v_symm_1346_, lean_object* v_config_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_symm_boxed_1357_; lean_object* v_res_1358_; 
v_symm_boxed_1357_ = lean_unbox(v_symm_1346_);
v_res_1358_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1345_, v_symm_boxed_1357_, v_config_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1359_, uint8_t v_symm_1360_, lean_object* v_config_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v___f_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1371_ = lean_box(v_symm_1360_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1372_, 0, v_stx_1359_);
lean_closure_set(v___f_1372_, 1, v___x_1371_);
lean_closure_set(v___f_1372_, 2, v_config_1361_);
v___x_1373_ = 1;
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
v___x_1374_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1374_, 0, lean_box(0));
lean_closure_set(v___x_1374_, 1, v___f_1372_);
lean_closure_set(v___x_1374_, 2, v_a_1362_);
lean_closure_set(v___x_1374_, 3, v_a_1363_);
v___x_1375_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1374_, v___x_1373_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1376_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1363_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_eNew_1381_; lean_object* v_eqProof_1382_; lean_object* v_mvarIds_1383_; lean_object* v___x_1384_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v_eNew_1381_ = lean_ctor_get(v_a_1378_, 0);
lean_inc_ref(v_eNew_1381_);
v_eqProof_1382_ = lean_ctor_get(v_a_1378_, 1);
lean_inc_ref(v_eqProof_1382_);
v_mvarIds_1383_ = lean_ctor_get(v_a_1378_, 2);
lean_inc(v_mvarIds_1383_);
lean_dec(v_a_1378_);
v___x_1384_ = l_Lean_MVarId_replaceTargetEq(v_a_1380_, v_eNew_1381_, v_eqProof_1382_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_a_1385_);
lean_ctor_set(v___x_1386_, 1, v_mvarIds_1383_);
v___x_1387_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1386_, v_a_1363_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_mvarIds_1383_);
v_a_1388_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1384_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1384_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_a_1378_);
v_a_1396_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1379_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1379_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1377_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1377_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1375_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1375_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1420_, lean_object* v_symm_1421_, lean_object* v_config_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
uint8_t v_symm_boxed_1432_; lean_object* v_res_1433_; 
v_symm_boxed_1432_ = lean_unbox(v_symm_1421_);
v_res_1433_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1420_, v_symm_boxed_1432_, v_config_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* v_fvarId_1434_, lean_object* v_stx_1435_, uint8_t v_symm_1436_, lean_object* v_config_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1434_, v___y_1442_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1439_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l_Lean_LocalDecl_type(v_a_1448_);
lean_dec(v_a_1448_);
v___x_1452_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1450_, v___x_1451_, v_stx_1435_, v_symm_1436_, v_config_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1452_;
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1448_);
lean_dec_ref(v_config_1437_);
lean_dec(v_stx_1435_);
v_a_1453_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1449_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1449_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_config_1437_);
lean_dec(v_stx_1435_);
v_a_1461_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1447_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1447_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* v_fvarId_1469_, lean_object* v_stx_1470_, lean_object* v_symm_1471_, lean_object* v_config_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_symm_boxed_1482_; lean_object* v_res_1483_; 
v_symm_boxed_1482_ = lean_unbox(v_symm_1471_);
v_res_1483_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(v_fvarId_1469_, v_stx_1470_, v_symm_boxed_1482_, v_config_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* v_eqProof_1484_, lean_object* v___x_1485_, lean_object* v_eNew_1486_, lean_object* v_a_1487_, lean_object* v_fvarId_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Meta_mkEqMP(v_eqProof_1484_, v___x_1485_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_eNew_1486_);
v___x_1497_ = lean_box(0);
v___x_1498_ = l_Lean_MVarId_replace(v_a_1487_, v_fvarId_1488_, v_a_1495_, v___x_1496_, v___x_1497_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1498_;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_fvarId_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_eNew_1486_);
v_a_1499_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1494_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1494_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* v_eqProof_1507_, lean_object* v___x_1508_, lean_object* v_eNew_1509_, lean_object* v_a_1510_, lean_object* v_fvarId_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(v_eqProof_1507_, v___x_1508_, v_eNew_1509_, v_a_1510_, v_fvarId_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(lean_object* v___f_1518_, uint8_t v___x_1519_, lean_object* v_fvarId_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_inc(v___y_1522_);
v___x_1530_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1530_, 0, lean_box(0));
lean_closure_set(v___x_1530_, 1, v___f_1518_);
lean_closure_set(v___x_1530_, 2, v___y_1521_);
lean_closure_set(v___x_1530_, 3, v___y_1522_);
v___x_1531_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1530_, v___x_1519_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1522_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_eNew_1537_; lean_object* v_eqProof_1538_; lean_object* v_mvarIds_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_n(v_a_1536_, 2);
lean_dec_ref_known(v___x_1535_, 1);
v_eNew_1537_ = lean_ctor_get(v_a_1534_, 0);
lean_inc_ref(v_eNew_1537_);
v_eqProof_1538_ = lean_ctor_get(v_a_1534_, 1);
lean_inc_ref(v_eqProof_1538_);
v_mvarIds_1539_ = lean_ctor_get(v_a_1534_, 2);
lean_inc(v_mvarIds_1539_);
lean_dec(v_a_1534_);
lean_inc(v_fvarId_1520_);
v___x_1540_ = l_Lean_mkFVar(v_fvarId_1520_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1541_, 0, v_eqProof_1538_);
lean_closure_set(v___f_1541_, 1, v___x_1540_);
lean_closure_set(v___f_1541_, 2, v_eNew_1537_);
lean_closure_set(v___f_1541_, 3, v_a_1536_);
lean_closure_set(v___f_1541_, 4, v_fvarId_1520_);
v___x_1542_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1536_, v___f_1541_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_mvarId_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_mvarId_1544_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_mvarId_1544_);
lean_dec(v_a_1543_);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_mvarId_1544_);
lean_ctor_set(v___x_1545_, 1, v_mvarIds_1539_);
v___x_1546_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1545_, v___y_1522_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1522_);
return v___x_1546_;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_mvarIds_1539_);
lean_dec(v___y_1522_);
v_a_1547_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1542_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1542_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1534_);
lean_dec(v___y_1522_);
lean_dec(v_fvarId_1520_);
v_a_1555_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1535_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1535_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v___y_1522_);
lean_dec(v_fvarId_1520_);
v_a_1563_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1533_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1533_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v___y_1522_);
lean_dec(v_fvarId_1520_);
v_a_1571_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1531_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1531_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed(lean_object* v___f_1579_, lean_object* v___x_1580_, lean_object* v_fvarId_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v___x_1374__boxed_1591_; lean_object* v_res_1592_; 
v___x_1374__boxed_1591_ = lean_unbox(v___x_1580_);
v_res_1592_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(v___f_1579_, v___x_1374__boxed_1591_, v_fvarId_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1593_, uint8_t v_symm_1594_, lean_object* v_fvarId_1595_, lean_object* v_config_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___f_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; 
v___x_1606_ = lean_box(v_symm_1594_);
lean_inc(v_fvarId_1595_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1607_, 0, v_fvarId_1595_);
lean_closure_set(v___f_1607_, 1, v_stx_1593_);
lean_closure_set(v___f_1607_, 2, v___x_1606_);
lean_closure_set(v___f_1607_, 3, v_config_1596_);
v___x_1608_ = 1;
v___x_1609_ = lean_box(v___x_1608_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1610_, 0, v___f_1607_);
lean_closure_set(v___f_1610_, 1, v___x_1609_);
lean_closure_set(v___f_1610_, 2, v_fvarId_1595_);
v___x_1611_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1610_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1612_, lean_object* v_symm_1613_, lean_object* v_fvarId_1614_, lean_object* v_config_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
uint8_t v_symm_boxed_1625_; lean_object* v_res_1626_; 
v_symm_boxed_1625_ = lean_unbox(v_symm_1613_);
v_res_1626_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1612_, v_symm_boxed_1625_, v_fvarId_1614_, v_config_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* v_x_1633_, uint8_t v_symm_1634_, lean_object* v_id_1635_, lean_object* v_declName_1636_, lean_object* v_hint_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
if (lean_obj_tag(v_a_1638_) == 0)
{
lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v_x_1633_);
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
v___x_1649_ = 0;
v___x_1650_ = l_Lean_MessageData_ofConstName(v_declName_1636_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_hint_1637_);
v___x_1655_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1654_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1655_;
}
else
{
lean_object* v_head_1656_; lean_object* v_tail_1657_; lean_object* v___x_1658_; 
v_head_1656_ = lean_ctor_get(v_a_1638_, 0);
lean_inc(v_head_1656_);
v_tail_1657_ = lean_ctor_get(v_a_1638_, 1);
lean_inc(v_tail_1657_);
lean_dec_ref_known(v_a_1638_, 2);
v___x_1658_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1640_, v_a_1642_, v_a_1644_, v_a_1646_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; uint8_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = 0;
v___x_1661_ = l_Lean_mkCIdentFrom(v_id_1635_, v_head_1656_, v___x_1660_);
v___x_1662_ = lean_box(v_symm_1634_);
lean_inc_ref(v_x_1633_);
v___x_1663_ = lean_apply_2(v_x_1633_, v___x_1662_, v___x_1661_);
v___x_1664_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1663_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_dec(v_a_1659_);
lean_dec(v_tail_1657_);
lean_dec_ref(v_hint_1637_);
lean_dec(v_declName_1636_);
lean_dec_ref(v_x_1633_);
return v___x_1664_;
}
else
{
lean_object* v_a_1665_; uint8_t v___y_1667_; uint8_t v___x_1670_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
v___x_1670_ = l_Lean_Exception_isInterrupt(v_a_1665_);
if (v___x_1670_ == 0)
{
uint8_t v___x_1671_; 
v___x_1671_ = l_Lean_Exception_isRuntime(v_a_1665_);
v___y_1667_ = v___x_1671_;
goto v___jp_1666_;
}
else
{
lean_dec(v_a_1665_);
v___y_1667_ = v___x_1670_;
goto v___jp_1666_;
}
v___jp_1666_:
{
if (v___y_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref_known(v___x_1664_, 1);
v___x_1668_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1659_, v___y_1667_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_dec_ref_known(v___x_1668_, 1);
v_a_1638_ = v_tail_1657_;
goto _start;
}
else
{
lean_dec(v_tail_1657_);
lean_dec_ref(v_hint_1637_);
lean_dec(v_declName_1636_);
lean_dec_ref(v_x_1633_);
return v___x_1668_;
}
}
else
{
lean_dec(v_a_1659_);
lean_dec(v_tail_1657_);
lean_dec_ref(v_hint_1637_);
lean_dec(v_declName_1636_);
lean_dec_ref(v_x_1633_);
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_tail_1657_);
lean_dec(v_head_1656_);
lean_dec_ref(v_hint_1637_);
lean_dec(v_declName_1636_);
lean_dec_ref(v_x_1633_);
v_a_1672_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1658_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1658_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* v_x_1680_, lean_object* v_symm_1681_, lean_object* v_id_1682_, lean_object* v_declName_1683_, lean_object* v_hint_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
uint8_t v_symm_boxed_1695_; lean_object* v_res_1696_; 
v_symm_boxed_1695_ = lean_unbox(v_symm_1681_);
v_res_1696_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1680_, v_symm_boxed_1695_, v_id_1682_, v_declName_1683_, v_hint_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_id_1682_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_a_1697_, lean_object* v_trees_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
v___x_1708_ = lean_apply_9(v_a_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, lean_box(0));
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_a_1709_);
lean_ctor_set(v___x_1713_, 1, v_trees_1698_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_trees_1698_);
v_a_1718_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1708_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1708_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_a_1726_, lean_object* v_trees_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_a_1726_, v_trees_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* v___x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1738_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object* v___x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(v___x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1760_, lean_object* v_mkInfoTree_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v_a_1769_, lean_object* v_a_x3f_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v_infoState_1773_; lean_object* v_trees_1774_; lean_object* v___x_1775_; 
v___x_1772_ = lean_st_ref_get(v___y_1760_);
v_infoState_1773_ = lean_ctor_get(v___x_1772_, 7);
lean_inc_ref(v_infoState_1773_);
lean_dec(v___x_1772_);
v_trees_1774_ = lean_ctor_get(v_infoState_1773_, 2);
lean_inc_ref(v_trees_1774_);
lean_dec_ref(v_infoState_1773_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1768_);
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
v___x_1775_ = lean_apply_10(v_mkInfoTree_1761_, v_trees_1774_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1760_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1814_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1814_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1814_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v_infoState_1781_; lean_object* v_env_1782_; lean_object* v_nextMacroScope_1783_; lean_object* v_ngen_1784_; lean_object* v_auxDeclNGen_1785_; lean_object* v_traceState_1786_; lean_object* v_cache_1787_; lean_object* v_messages_1788_; lean_object* v_snapshotTasks_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1813_; 
v___x_1780_ = lean_st_ref_take(v___y_1760_);
v_infoState_1781_ = lean_ctor_get(v___x_1780_, 7);
v_env_1782_ = lean_ctor_get(v___x_1780_, 0);
v_nextMacroScope_1783_ = lean_ctor_get(v___x_1780_, 1);
v_ngen_1784_ = lean_ctor_get(v___x_1780_, 2);
v_auxDeclNGen_1785_ = lean_ctor_get(v___x_1780_, 3);
v_traceState_1786_ = lean_ctor_get(v___x_1780_, 4);
v_cache_1787_ = lean_ctor_get(v___x_1780_, 5);
v_messages_1788_ = lean_ctor_get(v___x_1780_, 6);
v_snapshotTasks_1789_ = lean_ctor_get(v___x_1780_, 8);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1813_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_snapshotTasks_1789_);
lean_inc(v_infoState_1781_);
lean_inc(v_messages_1788_);
lean_inc(v_cache_1787_);
lean_inc(v_traceState_1786_);
lean_inc(v_auxDeclNGen_1785_);
lean_inc(v_ngen_1784_);
lean_inc(v_nextMacroScope_1783_);
lean_inc(v_env_1782_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1813_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
uint8_t v_enabled_1793_; lean_object* v_assignment_1794_; lean_object* v_lazyAssignment_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1811_; 
v_enabled_1793_ = lean_ctor_get_uint8(v_infoState_1781_, sizeof(void*)*3);
v_assignment_1794_ = lean_ctor_get(v_infoState_1781_, 0);
v_lazyAssignment_1795_ = lean_ctor_get(v_infoState_1781_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_infoState_1781_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; 
v_unused_1812_ = lean_ctor_get(v_infoState_1781_, 2);
lean_dec(v_unused_1812_);
v___x_1797_ = v_infoState_1781_;
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_lazyAssignment_1795_);
lean_inc(v_assignment_1794_);
lean_dec(v_infoState_1781_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = l_Lean_PersistentArray_push___redArg(v_a_1769_, v_a_1776_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 2, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_assignment_1794_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_lazyAssignment_1795_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v___x_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1810_, sizeof(void*)*3, v_enabled_1793_);
v___x_1801_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 7, v___x_1801_);
v___x_1803_ = v___x_1791_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_env_1782_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_nextMacroScope_1783_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_ngen_1784_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_auxDeclNGen_1785_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_traceState_1786_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_cache_1787_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_messages_1788_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_snapshotTasks_1789_);
v___x_1803_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1804_ = lean_st_ref_set(v___y_1760_, v___x_1803_);
v___x_1805_ = lean_box(0);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1805_);
v___x_1807_ = v___x_1778_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v_a_1769_);
v_a_1815_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1775_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1775_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1823_, lean_object* v_mkInfoTree_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v_a_1832_, lean_object* v_a_x3f_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1823_, v_mkInfoTree_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v_a_1832_, v_a_x3f_1833_);
lean_dec(v_a_x3f_1833_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1823_);
return v_res_1835_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_unsigned_to_nat(32u);
v___x_1837_ = lean_mk_empty_array_with_capacity(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1839_ = ((size_t)5ULL);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_unsigned_to_nat(32u);
v___x_1842_ = lean_mk_empty_array_with_capacity(v___x_1841_);
v___x_1843_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1844_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
lean_ctor_set(v___x_1844_, 2, v___x_1840_);
lean_ctor_set(v___x_1844_, 3, v___x_1840_);
lean_ctor_set_usize(v___x_1844_, 4, v___x_1839_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v_infoState_1848_; lean_object* v_trees_1849_; lean_object* v___x_1850_; lean_object* v_infoState_1851_; lean_object* v_env_1852_; lean_object* v_nextMacroScope_1853_; lean_object* v_ngen_1854_; lean_object* v_auxDeclNGen_1855_; lean_object* v_traceState_1856_; lean_object* v_cache_1857_; lean_object* v_messages_1858_; lean_object* v_snapshotTasks_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1880_; 
v___x_1847_ = lean_st_ref_get(v___y_1845_);
v_infoState_1848_ = lean_ctor_get(v___x_1847_, 7);
lean_inc_ref(v_infoState_1848_);
lean_dec(v___x_1847_);
v_trees_1849_ = lean_ctor_get(v_infoState_1848_, 2);
lean_inc_ref(v_trees_1849_);
lean_dec_ref(v_infoState_1848_);
v___x_1850_ = lean_st_ref_take(v___y_1845_);
v_infoState_1851_ = lean_ctor_get(v___x_1850_, 7);
v_env_1852_ = lean_ctor_get(v___x_1850_, 0);
v_nextMacroScope_1853_ = lean_ctor_get(v___x_1850_, 1);
v_ngen_1854_ = lean_ctor_get(v___x_1850_, 2);
v_auxDeclNGen_1855_ = lean_ctor_get(v___x_1850_, 3);
v_traceState_1856_ = lean_ctor_get(v___x_1850_, 4);
v_cache_1857_ = lean_ctor_get(v___x_1850_, 5);
v_messages_1858_ = lean_ctor_get(v___x_1850_, 6);
v_snapshotTasks_1859_ = lean_ctor_get(v___x_1850_, 8);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1880_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_snapshotTasks_1859_);
lean_inc(v_infoState_1851_);
lean_inc(v_messages_1858_);
lean_inc(v_cache_1857_);
lean_inc(v_traceState_1856_);
lean_inc(v_auxDeclNGen_1855_);
lean_inc(v_ngen_1854_);
lean_inc(v_nextMacroScope_1853_);
lean_inc(v_env_1852_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1880_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
uint8_t v_enabled_1863_; lean_object* v_assignment_1864_; lean_object* v_lazyAssignment_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1878_; 
v_enabled_1863_ = lean_ctor_get_uint8(v_infoState_1851_, sizeof(void*)*3);
v_assignment_1864_ = lean_ctor_get(v_infoState_1851_, 0);
v_lazyAssignment_1865_ = lean_ctor_get(v_infoState_1851_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_infoState_1851_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v_infoState_1851_, 2);
lean_dec(v_unused_1879_);
v___x_1867_ = v_infoState_1851_;
v_isShared_1868_ = v_isSharedCheck_1878_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_lazyAssignment_1865_);
lean_inc(v_assignment_1864_);
lean_dec(v_infoState_1851_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1878_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 2, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_assignment_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_lazyAssignment_1865_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v___x_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*3, v_enabled_1863_);
v___x_1871_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 7, v___x_1871_);
v___x_1873_ = v___x_1861_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_env_1852_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_nextMacroScope_1853_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_ngen_1854_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_auxDeclNGen_1855_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_traceState_1856_);
lean_ctor_set(v_reuseFailAlloc_1876_, 5, v_cache_1857_);
lean_ctor_set(v_reuseFailAlloc_1876_, 6, v_messages_1858_);
lean_ctor_set(v_reuseFailAlloc_1876_, 7, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1876_, 8, v_snapshotTasks_1859_);
v___x_1873_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_st_ref_set(v___y_1845_, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_trees_1849_);
return v___x_1875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1881_);
lean_dec(v___y_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* v_x_1884_, lean_object* v_mkInfoTree_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_infoState_1896_; uint8_t v_enabled_1897_; 
v___x_1895_ = lean_st_ref_get(v___y_1893_);
v_infoState_1896_ = lean_ctor_get(v___x_1895_, 7);
lean_inc_ref(v_infoState_1896_);
lean_dec(v___x_1895_);
v_enabled_1897_ = lean_ctor_get_uint8(v_infoState_1896_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1896_);
if (v_enabled_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_mkInfoTree_1885_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___x_1898_ = lean_apply_9(v_x_1884_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; lean_object* v_a_1900_; lean_object* v_r_1901_; 
v___x_1899_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1893_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v_r_1901_ = lean_apply_9(v_x_1884_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
if (lean_obj_tag(v_r_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1926_; 
v_a_1902_ = lean_ctor_get(v_r_1901_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_r_1901_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1904_ = v_r_1901_;
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v_r_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
lean_inc(v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 1);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1893_, v_mkInfoTree_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v_a_1900_, v___x_1907_);
lean_dec_ref(v___x_1907_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1908_, 0);
lean_dec(v_unused_1916_);
v___x_1910_ = v___x_1908_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v___x_1908_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_a_1902_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1902_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1902_);
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1927_ = lean_ctor_get(v_r_1901_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v_r_1901_, 1);
v___x_1928_ = lean_box(0);
v___x_1929_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1893_, v_mkInfoTree_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v_a_1900_, v___x_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1929_, 0);
lean_dec(v_unused_1937_);
v___x_1931_ = v___x_1929_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v___x_1929_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 0, v_a_1927_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1927_);
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
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1927_);
v_a_1938_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1929_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1929_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_1946_, lean_object* v_mkInfoTree_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_1946_, v_mkInfoTree_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_1967_, uint8_t v___x_1968_, lean_object* v___x_1969_, lean_object* v_x_1970_, uint8_t v___y_1971_, lean_object* v___x_1972_, lean_object* v___x_1973_, lean_object* v___f_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_fileName_1984_; lean_object* v_fileMap_1985_; lean_object* v_options_1986_; lean_object* v_currRecDepth_1987_; lean_object* v_maxRecDepth_1988_; lean_object* v_ref_1989_; lean_object* v_currNamespace_1990_; lean_object* v_openDecls_1991_; lean_object* v_initHeartbeats_1992_; lean_object* v_maxHeartbeats_1993_; lean_object* v_quotContext_1994_; lean_object* v_currMacroScope_1995_; uint8_t v_diag_1996_; lean_object* v_cancelTk_x3f_1997_; uint8_t v_suppressElabErrors_1998_; lean_object* v_inheritedTraceOptions_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2017_; 
v_fileName_1984_ = lean_ctor_get(v___y_1981_, 0);
v_fileMap_1985_ = lean_ctor_get(v___y_1981_, 1);
v_options_1986_ = lean_ctor_get(v___y_1981_, 2);
v_currRecDepth_1987_ = lean_ctor_get(v___y_1981_, 3);
v_maxRecDepth_1988_ = lean_ctor_get(v___y_1981_, 4);
v_ref_1989_ = lean_ctor_get(v___y_1981_, 5);
v_currNamespace_1990_ = lean_ctor_get(v___y_1981_, 6);
v_openDecls_1991_ = lean_ctor_get(v___y_1981_, 7);
v_initHeartbeats_1992_ = lean_ctor_get(v___y_1981_, 8);
v_maxHeartbeats_1993_ = lean_ctor_get(v___y_1981_, 9);
v_quotContext_1994_ = lean_ctor_get(v___y_1981_, 10);
v_currMacroScope_1995_ = lean_ctor_get(v___y_1981_, 11);
v_diag_1996_ = lean_ctor_get_uint8(v___y_1981_, sizeof(void*)*14);
v_cancelTk_x3f_1997_ = lean_ctor_get(v___y_1981_, 12);
v_suppressElabErrors_1998_ = lean_ctor_get_uint8(v___y_1981_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1999_ = lean_ctor_get(v___y_1981_, 13);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___y_1981_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2001_ = v___y_1981_;
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_inheritedTraceOptions_1999_);
lean_inc(v_cancelTk_x3f_1997_);
lean_inc(v_currMacroScope_1995_);
lean_inc(v_quotContext_1994_);
lean_inc(v_maxHeartbeats_1993_);
lean_inc(v_initHeartbeats_1992_);
lean_inc(v_openDecls_1991_);
lean_inc(v_currNamespace_1990_);
lean_inc(v_ref_1989_);
lean_inc(v_maxRecDepth_1988_);
lean_inc(v_currRecDepth_1987_);
lean_inc(v_options_1986_);
lean_inc(v_fileMap_1985_);
lean_inc(v_fileName_1984_);
lean_dec(v___y_1981_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_ref_2003_; lean_object* v___x_2005_; 
v_ref_2003_ = l_Lean_replaceRef(v___x_1967_, v_ref_1989_);
lean_dec(v_ref_1989_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 5, v_ref_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_fileName_1984_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_fileMap_1985_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_options_1986_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_currRecDepth_1987_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_maxRecDepth_1988_);
lean_ctor_set(v_reuseFailAlloc_2016_, 5, v_ref_2003_);
lean_ctor_set(v_reuseFailAlloc_2016_, 6, v_currNamespace_1990_);
lean_ctor_set(v_reuseFailAlloc_2016_, 7, v_openDecls_1991_);
lean_ctor_set(v_reuseFailAlloc_2016_, 8, v_initHeartbeats_1992_);
lean_ctor_set(v_reuseFailAlloc_2016_, 9, v_maxHeartbeats_1993_);
lean_ctor_set(v_reuseFailAlloc_2016_, 10, v_quotContext_1994_);
lean_ctor_set(v_reuseFailAlloc_2016_, 11, v_currMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2016_, 12, v_cancelTk_x3f_1997_);
lean_ctor_set(v_reuseFailAlloc_2016_, 13, v_inheritedTraceOptions_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*14, v_diag_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*14 + 1, v_suppressElabErrors_1998_);
v___x_2005_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
if (v___x_1968_ == 0)
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_1969_);
v___x_2007_ = l_Lean_Syntax_isOfKind(v___x_1969_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec_ref(v___f_1974_);
v___x_2008_ = lean_box(v___y_1971_);
v___x_2009_ = lean_apply_11(v_x_1970_, v___x_2008_, v___x_1969_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___x_2005_, v___y_1982_, lean_box(0));
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = l_Lean_Syntax_getArg(v___x_1969_, v___x_1972_);
lean_inc(v___x_2010_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v___x_2010_, v___x_1973_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v___x_2010_);
lean_dec_ref(v___f_1974_);
v___x_2012_ = lean_box(v___y_1971_);
v___x_2013_ = lean_apply_11(v_x_1970_, v___x_2012_, v___x_1969_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___x_2005_, v___y_1982_, lean_box(0));
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; 
lean_dec_ref(v_x_1970_);
lean_dec(v___x_1969_);
v___x_2014_ = lean_apply_10(v___f_1974_, v___x_2010_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___x_2005_, v___y_1982_, lean_box(0));
return v___x_2014_;
}
}
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref(v_x_1970_);
v___x_2015_ = lean_apply_10(v___f_1974_, v___x_1969_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___x_2005_, v___y_1982_, lean_box(0));
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2018_ = _args[0];
lean_object* v___x_2019_ = _args[1];
lean_object* v___x_2020_ = _args[2];
lean_object* v_x_2021_ = _args[3];
lean_object* v___y_2022_ = _args[4];
lean_object* v___x_2023_ = _args[5];
lean_object* v___x_2024_ = _args[6];
lean_object* v___f_2025_ = _args[7];
lean_object* v___y_2026_ = _args[8];
lean_object* v___y_2027_ = _args[9];
lean_object* v___y_2028_ = _args[10];
lean_object* v___y_2029_ = _args[11];
lean_object* v___y_2030_ = _args[12];
lean_object* v___y_2031_ = _args[13];
lean_object* v___y_2032_ = _args[14];
lean_object* v___y_2033_ = _args[15];
lean_object* v___y_2034_ = _args[16];
_start:
{
uint8_t v___x_16685__boxed_2035_; uint8_t v___y_16687__boxed_2036_; lean_object* v_res_2037_; 
v___x_16685__boxed_2035_ = lean_unbox(v___x_2019_);
v___y_16687__boxed_2036_ = lean_unbox(v___y_2022_);
v_res_2037_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_2018_, v___x_16685__boxed_2035_, v___x_2020_, v_x_2021_, v___y_16687__boxed_2036_, v___x_2023_, v___x_2024_, v___f_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___x_2024_);
lean_dec(v___x_2023_);
lean_dec(v___x_2018_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_2038_, lean_object* v_trees_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
v___x_2049_ = lean_apply_9(v_a_2038_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2058_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_a_2050_);
lean_ctor_set(v___x_2054_, 1, v_trees_2039_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_trees_2039_);
v_a_2059_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2049_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2049_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_2067_, lean_object* v_trees_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_2067_, v_trees_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2079_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2100_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_2107_, uint8_t v___y_2108_, lean_object* v___x_2109_, lean_object* v___x_2110_, lean_object* v_id_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___f_2121_; lean_object* v___x_2122_; 
lean_inc(v_id_2111_);
v___f_2121_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2121_, 0, v_id_2111_);
v___x_2122_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2121_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
if (lean_obj_tag(v_a_2123_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2113_, v___y_2115_, v___y_2117_, v___y_2119_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
lean_inc(v_id_2111_);
v___x_2126_ = l_Lean_realizeGlobalConstNoOverload(v_id_2111_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
lean_dec(v_a_2125_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc_n(v_a_2127_, 2);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2127_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
if (lean_obj_tag(v_a_2129_) == 1)
{
lean_object* v_val_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v___x_2110_);
v_val_2130_ = lean_ctor_get(v_a_2129_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2132_ = v_a_2129_;
v_isShared_2133_ = v_isSharedCheck_2174_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_val_2130_);
lean_dec(v_a_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2174_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; lean_object* v___y_2136_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2134_ = 0;
v___x_2163_ = lean_array_get_size(v_val_2130_);
v___x_2164_ = lean_nat_dec_eq(v___x_2163_, v___x_2109_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2165_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_2166_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2127_);
v___x_2167_ = l_Lean_Name_str___override(v_a_2127_, v___x_2166_);
v___x_2168_ = l_Lean_MessageData_ofName(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2165_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_MessageData_hint_x27(v___x_2171_);
v___y_2136_ = v___x_2172_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2136_ = v___x_2173_;
goto v___jp_2135_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; 
lean_inc(v_a_2127_);
v___x_2137_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2127_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_lctx_2139_; lean_object* v___x_2141_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_lctx_2139_ = lean_ctor_get(v___y_2116_, 2);
lean_inc_ref(v_lctx_2139_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v_lctx_2139_);
v___x_2141_ = v___x_2132_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_lctx_2139_);
v___x_2141_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_box(0);
lean_inc(v_id_2111_);
v___x_2143_ = l_Lean_Elab_Term_addTermInfo(v_id_2111_, v_a_2138_, v_a_2123_, v___x_2141_, v___x_2142_, v___x_2134_, v___x_2134_, v___x_2134_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref_known(v___x_2143_, 1);
v___x_2144_ = lean_array_to_list(v_val_2130_);
v___x_2145_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_2107_, v___y_2108_, v_id_2111_, v_a_2127_, v___y_2136_, v___x_2144_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v_id_2111_);
return v___x_2145_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v___y_2136_);
lean_dec(v_val_2130_);
lean_dec(v_a_2127_);
lean_dec(v_id_2111_);
lean_dec_ref(v_x_2107_);
v_a_2146_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2143_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2143_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v___y_2136_);
lean_del_object(v___x_2132_);
lean_dec(v_val_2130_);
lean_dec(v_a_2127_);
lean_dec(v_id_2111_);
lean_dec_ref(v_x_2107_);
v_a_2155_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2137_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2137_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v_a_2129_);
lean_dec(v_a_2127_);
lean_dec(v_id_2111_);
v___x_2175_ = lean_box(v___y_2108_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
v___x_2176_ = lean_apply_11(v_x_2107_, v___x_2175_, v___x_2110_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, lean_box(0));
return v___x_2176_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_a_2127_);
lean_dec(v_id_2111_);
lean_dec(v___x_2110_);
lean_dec_ref(v_x_2107_);
v_a_2177_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2128_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2128_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_id_2111_);
v_a_2185_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2187_ = v___x_2126_;
v_isShared_2188_ = v_isSharedCheck_2199_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2126_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2199_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
uint8_t v___y_2190_; uint8_t v___x_2197_; 
v___x_2197_ = l_Lean_Exception_isInterrupt(v_a_2185_);
if (v___x_2197_ == 0)
{
uint8_t v___x_2198_; 
lean_inc(v_a_2185_);
v___x_2198_ = l_Lean_Exception_isRuntime(v_a_2185_);
v___y_2190_ = v___x_2198_;
goto v___jp_2189_;
}
else
{
v___y_2190_ = v___x_2197_;
goto v___jp_2189_;
}
v___jp_2189_:
{
if (v___y_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_del_object(v___x_2187_);
lean_dec(v_a_2185_);
v___x_2191_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2125_, v___y_2190_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec_ref_known(v___x_2191_, 1);
v___x_2192_ = lean_box(v___y_2108_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
v___x_2193_ = lean_apply_11(v_x_2107_, v___x_2192_, v___x_2110_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, lean_box(0));
return v___x_2193_;
}
else
{
lean_dec(v___x_2110_);
lean_dec_ref(v_x_2107_);
return v___x_2191_;
}
}
else
{
lean_object* v___x_2195_; 
lean_dec(v_a_2125_);
lean_dec(v___x_2110_);
lean_dec_ref(v_x_2107_);
if (v_isShared_2188_ == 0)
{
v___x_2195_ = v___x_2187_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2185_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_id_2111_);
lean_dec(v___x_2110_);
lean_dec_ref(v_x_2107_);
v_a_2200_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2124_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2124_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref_known(v_a_2123_, 1);
lean_dec(v_id_2111_);
v___x_2208_ = lean_box(v___y_2108_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
v___x_2209_ = lean_apply_11(v_x_2107_, v___x_2208_, v___x_2110_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, lean_box(0));
return v___x_2209_;
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_id_2111_);
lean_dec(v___x_2110_);
lean_dec_ref(v_x_2107_);
v_a_2210_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2122_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2122_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2218_, lean_object* v___y_2219_, lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v_id_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v___y_16885__boxed_2232_; lean_object* v_res_2233_; 
v___y_16885__boxed_2232_ = lean_unbox(v___y_2219_);
v_res_2233_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_2218_, v___y_16885__boxed_2232_, v___x_2220_, v___x_2221_, v_id_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___x_2220_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2240_, lean_object* v_rules_2241_, lean_object* v_x_2242_, lean_object* v_a_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_nat_dec_lt(v_a_2243_, v_upperBound_2240_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_a_2243_);
lean_dec_ref(v_x_2242_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_b_2244_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___y_2264_; uint8_t v___y_2265_; lean_object* v___y_2289_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_nat_mul(v_a_2243_, v___x_2256_);
v___x_2262_ = lean_array_get_borrowed(v___x_2257_, v_rules_2241_, v___x_2261_);
v___x_2299_ = lean_nat_add(v___x_2261_, v___x_2258_);
lean_dec(v___x_2261_);
v___x_2300_ = lean_array_get_size(v_rules_2241_);
v___x_2301_ = lean_nat_dec_lt(v___x_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_dec(v___x_2299_);
v___y_2289_ = v___x_2257_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_array_fget_borrowed(v_rules_2241_, v___x_2299_);
lean_dec(v___x_2299_);
lean_inc(v___x_2302_);
v___y_2289_ = v___x_2302_;
goto v___jp_2288_;
}
v___jp_2263_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2264_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___f_2268_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2268_, 0, v_a_2267_);
v___x_2269_ = l_Lean_Syntax_getArg(v___x_2262_, v___x_2258_);
v___x_2270_ = lean_box(v___y_2265_);
lean_inc_n(v___x_2269_, 2);
lean_inc_ref_n(v_x_2242_, 2);
v___f_2271_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2271_, 0, v_x_2242_);
lean_closure_set(v___f_2271_, 1, v___x_2270_);
lean_closure_set(v___f_2271_, 2, v___x_2258_);
lean_closure_set(v___f_2271_, 3, v___x_2269_);
v___x_2272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
v___x_2273_ = l_Lean_Syntax_isOfKind(v___x_2269_, v___x_2272_);
v___x_2274_ = lean_box(v___x_2273_);
v___x_2275_ = lean_box(v___y_2265_);
lean_inc(v___x_2262_);
v___f_2276_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed), 17, 8);
lean_closure_set(v___f_2276_, 0, v___x_2262_);
lean_closure_set(v___f_2276_, 1, v___x_2274_);
lean_closure_set(v___f_2276_, 2, v___x_2269_);
lean_closure_set(v___f_2276_, 3, v_x_2242_);
lean_closure_set(v___f_2276_, 4, v___x_2275_);
lean_closure_set(v___f_2276_, 5, v___x_2258_);
lean_closure_set(v___f_2276_, 6, v___x_2272_);
lean_closure_set(v___f_2276_, 7, v___f_2271_);
v___x_2277_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2276_, v___f_2268_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; 
lean_dec_ref_known(v___x_2277_, 1);
v___x_2278_ = lean_nat_add(v_a_2243_, v___x_2258_);
lean_dec(v_a_2243_);
v_a_2243_ = v___x_2278_;
v_b_2244_ = v___x_2259_;
goto _start;
}
else
{
lean_dec(v_a_2243_);
lean_dec_ref(v_x_2242_);
return v___x_2277_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2243_);
lean_dec_ref(v_x_2242_);
v_a_2280_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2266_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2266_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2290_ = lean_mk_empty_array_with_capacity(v___x_2256_);
lean_inc(v___x_2262_);
v___x_2291_ = lean_array_push(v___x_2290_, v___x_2262_);
v___x_2292_ = lean_array_push(v___x_2291_, v___y_2289_);
v___x_2293_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2294_ = lean_box(2);
v___x_2295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_2293_);
lean_ctor_set(v___x_2295_, 2, v___x_2292_);
v___x_2296_ = l_Lean_Syntax_getArg(v___x_2262_, v___x_2260_);
v___x_2297_ = l_Lean_Syntax_isNone(v___x_2296_);
lean_dec(v___x_2296_);
if (v___x_2297_ == 0)
{
v___y_2264_ = v___x_2295_;
v___y_2265_ = v___x_2254_;
goto v___jp_2263_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = 0;
v___y_2264_ = v___x_2295_;
v___y_2265_ = v___x_2298_;
goto v___jp_2263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2303_, lean_object* v_rules_2304_, lean_object* v_x_2305_, lean_object* v_a_2306_, lean_object* v_b_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2303_, v_rules_2304_, v_x_2305_, v_a_2306_, v_b_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_rules_2304_);
lean_dec(v_upperBound_2303_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2320_, lean_object* v_rwRulesSeqStx_2321_, lean_object* v_x_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v_lbrak_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2332_ = lean_unsigned_to_nat(0u);
v_lbrak_2333_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2321_, v___x_2332_);
v___x_2334_ = lean_unsigned_to_nat(2u);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2334_);
v___x_2336_ = lean_array_push(v___x_2335_, v_token_2320_);
v___x_2337_ = lean_array_push(v___x_2336_, v_lbrak_2333_);
v___x_2338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2339_ = lean_box(2);
v___x_2340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___x_2338_);
lean_ctor_set(v___x_2340_, 2, v___x_2337_);
v___x_2341_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2340_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2343_, 0, v_a_2342_);
v___x_2344_ = lean_box(0);
v___f_2345_ = ((lean_object*)(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0));
v___x_2346_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2345_, v___f_2343_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_rules_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2346_, 1);
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2321_, v___x_2347_);
v_rules_2349_ = l_Lean_Syntax_getArgs(v___x_2348_);
lean_dec(v___x_2348_);
v___x_2350_ = lean_array_get_size(v_rules_2349_);
v___x_2351_ = lean_nat_add(v___x_2350_, v___x_2347_);
v___x_2352_ = lean_nat_shiftr(v___x_2351_, v___x_2347_);
lean_dec(v___x_2351_);
v___x_2353_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_2352_, v_rules_2349_, v_x_2322_, v___x_2332_, v___x_2344_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v_rules_2349_);
lean_dec(v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2353_, 0);
lean_dec(v_unused_2361_);
v___x_2355_ = v___x_2353_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v___x_2353_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2344_);
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2344_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
return v___x_2353_;
}
}
else
{
lean_dec_ref(v_x_2322_);
return v___x_2346_;
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_x_2322_);
v_a_2362_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2341_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2341_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2370_, lean_object* v_rwRulesSeqStx_2371_, lean_object* v_x_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2370_, v_rwRulesSeqStx_2371_, v_x_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_rwRulesSeqStx_2371_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* v_00_u03b1_2403_, lean_object* v_x_2404_, lean_object* v_mkInfoTree_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_2404_, v_mkInfoTree_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_x_2417_, lean_object* v_mkInfoTree_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(v_00_u03b1_2416_, v_x_2417_, v_mkInfoTree_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object* v_upperBound_2429_, lean_object* v_rules_2430_, lean_object* v_x_2431_, lean_object* v_inst_2432_, lean_object* v_R_2433_, lean_object* v_a_2434_, lean_object* v_b_2435_, lean_object* v_c_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2429_, v_rules_2430_, v_x_2431_, v_a_2434_, v_b_2435_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2447_ = _args[0];
lean_object* v_rules_2448_ = _args[1];
lean_object* v_x_2449_ = _args[2];
lean_object* v_inst_2450_ = _args[3];
lean_object* v_R_2451_ = _args[4];
lean_object* v_a_2452_ = _args[5];
lean_object* v_b_2453_ = _args[6];
lean_object* v_c_2454_ = _args[7];
lean_object* v___y_2455_ = _args[8];
lean_object* v___y_2456_ = _args[9];
lean_object* v___y_2457_ = _args[10];
lean_object* v___y_2458_ = _args[11];
lean_object* v___y_2459_ = _args[12];
lean_object* v___y_2460_ = _args[13];
lean_object* v___y_2461_ = _args[14];
lean_object* v___y_2462_ = _args[15];
lean_object* v___y_2463_ = _args[16];
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(v_upperBound_2447_, v_rules_2448_, v_x_2449_, v_inst_2450_, v_R_2451_, v_a_2452_, v_b_2453_, v_c_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec_ref(v_rules_2448_);
lean_dec(v_upperBound_2447_);
return v_res_2464_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_ref_2493_; lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2503_; 
v_ref_2493_ = lean_ctor_get(v___y_2490_, 5);
v___x_2494_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_inc(v_ref_2493_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_ref_2493_);
lean_ctor_set(v___x_2499_, 1, v_a_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 1);
lean_ctor_set(v___x_2497_, 0, v___x_2499_);
v___x_2501_ = v___x_2497_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v_ctor_2515_, lean_object* v_args_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2584_ = lean_string_dec_eq(v_ctor_2515_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2586_ = lean_array_get_size(v_args_2516_);
v___x_2587_ = lean_unsigned_to_nat(4u);
v___x_2588_ = lean_nat_dec_eq(v___x_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v___x_2589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2590_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2589_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
goto v___jp_2522_;
}
}
v___jp_2522_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = l_Lean_instInhabitedExpr;
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = lean_array_get_borrowed(v___x_2523_, v_args_2516_, v___x_2524_);
lean_inc(v___x_2525_);
v___x_2526_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2525_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_array_get_borrowed(v___x_2523_, v_args_2516_, v___x_2528_);
lean_inc(v___x_2529_);
v___x_2530_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2529_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = lean_unsigned_to_nat(2u);
v___x_2533_ = lean_array_get_borrowed(v___x_2523_, v_args_2516_, v___x_2532_);
lean_inc(v___x_2533_);
v___x_2534_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2533_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = lean_unsigned_to_nat(3u);
v___x_2537_ = lean_array_get_borrowed(v___x_2523_, v_args_2516_, v___x_2536_);
lean_inc(v___x_2537_);
v___x_2538_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2537_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2550_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2550_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2550_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; uint8_t v___x_2544_; uint8_t v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2548_; 
v___x_2543_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2543_, 0, v_a_2535_);
v___x_2544_ = lean_unbox(v_a_2527_);
lean_dec(v_a_2527_);
lean_ctor_set_uint8(v___x_2543_, sizeof(void*)*1, v___x_2544_);
v___x_2545_ = lean_unbox(v_a_2531_);
lean_dec(v_a_2531_);
lean_ctor_set_uint8(v___x_2543_, sizeof(void*)*1 + 1, v___x_2545_);
v___x_2546_ = lean_unbox(v_a_2539_);
lean_dec(v_a_2539_);
lean_ctor_set_uint8(v___x_2543_, sizeof(void*)*1 + 2, v___x_2546_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2548_ = v___x_2541_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2535_);
lean_dec(v_a_2531_);
lean_dec(v_a_2527_);
v_a_2551_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2538_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2538_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_a_2531_);
lean_dec(v_a_2527_);
v_a_2559_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2534_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2534_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_a_2527_);
v_a_2567_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2530_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2530_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2526_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2526_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_2599_, lean_object* v_args_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v_ctor_2599_, v_args_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_args_2600_);
lean_dec_ref(v_ctor_2599_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___f_2622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0));
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2624_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2623_, v___f_2622_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2632_, lean_object* v_msg_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_msg_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2640_, v_msg_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_box(0);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2651_ = l_Lean_Expr_const___override(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2657_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(1);
v___x_2659_ = l_Lean_MessageData_ofFormat(v___x_2658_);
return v___x_2659_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2664_ = l_Lean_MessageData_ofFormat(v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
if (lean_obj_tag(v_x_2666_) == 0)
{
return v_x_2665_;
}
else
{
lean_object* v_head_2667_; lean_object* v_tail_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2690_; 
v_head_2667_ = lean_ctor_get(v_x_2666_, 0);
v_tail_2668_ = lean_ctor_get(v_x_2666_, 1);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_x_2666_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2670_ = v_x_2666_;
v_isShared_2671_ = v_isSharedCheck_2690_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_tail_2668_);
lean_inc(v_head_2667_);
lean_dec(v_x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2690_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_before_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2688_; 
v_before_2672_ = lean_ctor_get(v_head_2667_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_head_2667_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_head_2667_, 1);
lean_dec(v_unused_2689_);
v___x_2674_ = v_head_2667_;
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_before_2672_);
lean_dec(v_head_2667_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 7);
lean_ctor_set(v___x_2674_, 1, v___x_2676_);
lean_ctor_set(v___x_2674_, 0, v_x_2665_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_x_2665_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2679_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 7);
lean_ctor_set(v___x_2670_, 1, v___x_2679_);
lean_ctor_set(v___x_2670_, 0, v___x_2678_);
v___x_2681_ = v___x_2670_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = l_Lean_MessageData_ofSyntax(v_before_2672_);
v___x_2683_ = l_Lean_indentD(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v_x_2665_ = v___x_2684_;
v_x_2666_ = v_tail_2668_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2691_, lean_object* v_opt_2692_){
_start:
{
lean_object* v_name_2693_; lean_object* v_defValue_2694_; lean_object* v_map_2695_; lean_object* v___x_2696_; 
v_name_2693_ = lean_ctor_get(v_opt_2692_, 0);
v_defValue_2694_ = lean_ctor_get(v_opt_2692_, 1);
v_map_2695_ = lean_ctor_get(v_opts_2691_, 0);
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2695_, v_name_2693_);
if (lean_obj_tag(v___x_2696_) == 0)
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_unbox(v_defValue_2694_);
return v___x_2697_;
}
else
{
lean_object* v_val_2698_; 
v_val_2698_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v___x_2696_, 1);
if (lean_obj_tag(v_val_2698_) == 1)
{
uint8_t v_v_2699_; 
v_v_2699_ = lean_ctor_get_uint8(v_val_2698_, 0);
lean_dec_ref_known(v_val_2698_, 0);
return v_v_2699_;
}
else
{
uint8_t v___x_2700_; 
lean_dec(v_val_2698_);
v___x_2700_ = lean_unbox(v_defValue_2694_);
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2701_, lean_object* v_opt_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2701_, v_opt_2702_);
lean_dec_ref(v_opt_2702_);
lean_dec_ref(v_opts_2701_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2710_, lean_object* v_macroStack_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_options_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_options_2714_ = lean_ctor_get(v___y_2712_, 2);
v___x_2715_ = l_Lean_Elab_pp_macroStack;
v___x_2716_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; 
lean_dec(v_macroStack_2711_);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v_msgData_2710_);
return v___x_2717_;
}
else
{
if (lean_obj_tag(v_macroStack_2711_) == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_msgData_2710_);
return v___x_2718_;
}
else
{
lean_object* v_head_2719_; lean_object* v_after_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2735_; 
v_head_2719_ = lean_ctor_get(v_macroStack_2711_, 0);
lean_inc(v_head_2719_);
v_after_2720_ = lean_ctor_get(v_head_2719_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_head_2719_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v_head_2719_, 0);
lean_dec(v_unused_2736_);
v___x_2722_ = v_head_2719_;
v_isShared_2723_ = v_isSharedCheck_2735_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_after_2720_);
lean_dec(v_head_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2735_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 7);
lean_ctor_set(v___x_2722_, 1, v___x_2724_);
lean_ctor_set(v___x_2722_, 0, v_msgData_2710_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_msgData_2710_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v_msgData_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2727_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Lean_MessageData_ofSyntax(v_after_2720_);
v___x_2730_ = l_Lean_indentD(v___x_2729_);
v_msgData_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2731_, 0, v___x_2728_);
lean_ctor_set(v_msgData_2731_, 1, v___x_2730_);
v___x_2732_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_2731_, v_macroStack_2711_);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_2737_, lean_object* v_macroStack_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2737_, v_macroStack_2738_, v___y_2739_);
lean_dec_ref(v___y_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_ref_2750_; lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v_macroStack_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2764_; 
v_ref_2750_ = lean_ctor_get(v___y_2747_, 5);
v___x_2751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2742_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2751_);
v_macroStack_2753_ = lean_ctor_get(v___y_2743_, 1);
v___x_2754_ = l_Lean_Elab_getBetterRef(v_ref_2750_, v_macroStack_2753_);
lean_inc(v_macroStack_2753_);
v___x_2755_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_2752_, v_macroStack_2753_, v___y_2747_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2754_);
lean_ctor_set(v___x_2760_, 1, v_a_2756_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 1);
lean_ctor_set(v___x_2758_, 0, v___x_2760_);
v___x_2762_ = v___x_2758_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = l_Lean_Expr_hasMVar(v_e_2774_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_e_2774_);
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; lean_object* v_mctx_2780_; lean_object* v___x_2781_; lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2784_; lean_object* v_cache_2785_; lean_object* v_zetaDeltaFVarIds_2786_; lean_object* v_postponed_2787_; lean_object* v_diag_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2797_; 
v___x_2779_ = lean_st_ref_get(v___y_2775_);
v_mctx_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_ref(v_mctx_2780_);
lean_dec(v___x_2779_);
v___x_2781_ = l_Lean_instantiateMVarsCore(v_mctx_2780_, v_e_2774_);
v_fst_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_fst_2782_);
v_snd_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_snd_2783_);
lean_dec_ref(v___x_2781_);
v___x_2784_ = lean_st_ref_take(v___y_2775_);
v_cache_2785_ = lean_ctor_get(v___x_2784_, 1);
v_zetaDeltaFVarIds_2786_ = lean_ctor_get(v___x_2784_, 2);
v_postponed_2787_ = lean_ctor_get(v___x_2784_, 3);
v_diag_2788_ = lean_ctor_get(v___x_2784_, 4);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2798_);
v___x_2790_ = v___x_2784_;
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_diag_2788_);
lean_inc(v_postponed_2787_);
lean_inc(v_zetaDeltaFVarIds_2786_);
lean_inc(v_cache_2785_);
lean_dec(v___x_2784_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_snd_2783_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_snd_2783_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_cache_2785_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_zetaDeltaFVarIds_2786_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_postponed_2787_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_diag_2788_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_st_ref_set(v___y_2775_, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_fst_2782_);
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_2799_, v___y_2800_);
lean_dec(v___y_2800_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lean_Elab_abortTermExceptionId;
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_2810_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_2818_ = l_Lean_Expr_const___override(v___x_2817_, v___x_2816_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2819_; lean_object* v_ty_x3f_2820_; 
v___x_2819_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_2820_, 0, v___x_2819_);
return v_ty_x3f_2820_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
return v___x_2823_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_2825_ = l_Lean_MessageData_ofExpr(v___x_2824_);
return v___x_2825_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_2827_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v___x_2826_);
return v___x_2828_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2830_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2829_);
return v___x_2831_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
return v___x_2834_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_2837_ = l_Lean_stringToMessageData(v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_ty_x3f_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v_fileName_2852_; lean_object* v_fileMap_2853_; lean_object* v_options_2854_; lean_object* v_currRecDepth_2855_; lean_object* v_maxRecDepth_2856_; lean_object* v_ref_2857_; lean_object* v_currNamespace_2858_; lean_object* v_openDecls_2859_; lean_object* v_initHeartbeats_2860_; lean_object* v_maxHeartbeats_2861_; lean_object* v_quotContext_2862_; lean_object* v_currMacroScope_2863_; uint8_t v_diag_2864_; lean_object* v_cancelTk_x3f_2865_; uint8_t v_suppressElabErrors_2866_; lean_object* v_inheritedTraceOptions_2867_; uint8_t v___x_2868_; lean_object* v_ref_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_ty_x3f_2846_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_2847_ = 1;
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_box(v___x_2847_);
v___x_2850_ = lean_box(v___x_2847_);
lean_inc(v_stx_2838_);
v___x_2851_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2851_, 0, v_stx_2838_);
lean_closure_set(v___x_2851_, 1, v_ty_x3f_2846_);
lean_closure_set(v___x_2851_, 2, v___x_2849_);
lean_closure_set(v___x_2851_, 3, v___x_2850_);
lean_closure_set(v___x_2851_, 4, v___x_2848_);
v_fileName_2852_ = lean_ctor_get(v_a_2843_, 0);
v_fileMap_2853_ = lean_ctor_get(v_a_2843_, 1);
v_options_2854_ = lean_ctor_get(v_a_2843_, 2);
v_currRecDepth_2855_ = lean_ctor_get(v_a_2843_, 3);
v_maxRecDepth_2856_ = lean_ctor_get(v_a_2843_, 4);
v_ref_2857_ = lean_ctor_get(v_a_2843_, 5);
v_currNamespace_2858_ = lean_ctor_get(v_a_2843_, 6);
v_openDecls_2859_ = lean_ctor_get(v_a_2843_, 7);
v_initHeartbeats_2860_ = lean_ctor_get(v_a_2843_, 8);
v_maxHeartbeats_2861_ = lean_ctor_get(v_a_2843_, 9);
v_quotContext_2862_ = lean_ctor_get(v_a_2843_, 10);
v_currMacroScope_2863_ = lean_ctor_get(v_a_2843_, 11);
v_diag_2864_ = lean_ctor_get_uint8(v_a_2843_, sizeof(void*)*14);
v_cancelTk_x3f_2865_ = lean_ctor_get(v_a_2843_, 12);
v_suppressElabErrors_2866_ = lean_ctor_get_uint8(v_a_2843_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2867_ = lean_ctor_get(v_a_2843_, 13);
v___x_2868_ = 1;
v_ref_2869_ = l_Lean_replaceRef(v_stx_2838_, v_ref_2857_);
lean_dec(v_stx_2838_);
lean_inc_ref(v_inheritedTraceOptions_2867_);
lean_inc(v_cancelTk_x3f_2865_);
lean_inc(v_currMacroScope_2863_);
lean_inc(v_quotContext_2862_);
lean_inc(v_maxHeartbeats_2861_);
lean_inc(v_initHeartbeats_2860_);
lean_inc(v_openDecls_2859_);
lean_inc(v_currNamespace_2858_);
lean_inc(v_maxRecDepth_2856_);
lean_inc(v_currRecDepth_2855_);
lean_inc_ref(v_options_2854_);
lean_inc_ref(v_fileMap_2853_);
lean_inc_ref(v_fileName_2852_);
v___x_2870_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2870_, 0, v_fileName_2852_);
lean_ctor_set(v___x_2870_, 1, v_fileMap_2853_);
lean_ctor_set(v___x_2870_, 2, v_options_2854_);
lean_ctor_set(v___x_2870_, 3, v_currRecDepth_2855_);
lean_ctor_set(v___x_2870_, 4, v_maxRecDepth_2856_);
lean_ctor_set(v___x_2870_, 5, v_ref_2869_);
lean_ctor_set(v___x_2870_, 6, v_currNamespace_2858_);
lean_ctor_set(v___x_2870_, 7, v_openDecls_2859_);
lean_ctor_set(v___x_2870_, 8, v_initHeartbeats_2860_);
lean_ctor_set(v___x_2870_, 9, v_maxHeartbeats_2861_);
lean_ctor_set(v___x_2870_, 10, v_quotContext_2862_);
lean_ctor_set(v___x_2870_, 11, v_currMacroScope_2863_);
lean_ctor_set(v___x_2870_, 12, v_cancelTk_x3f_2865_);
lean_ctor_set(v___x_2870_, 13, v_inheritedTraceOptions_2867_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14, v_diag_2864_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14 + 1, v_suppressElabErrors_2866_);
v___x_2871_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2851_, v___x_2868_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v___x_2870_, v_a_2844_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v_a_2874_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; uint8_t v___y_2885_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; uint8_t v___x_2969_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_2872_, v_a_2842_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
v___x_2969_ = l_Lean_Expr_hasSorry(v_a_2874_);
if (v___x_2969_ == 0)
{
v___y_2914_ = v_a_2839_;
v___y_2915_ = v_a_2840_;
v___y_2916_ = v_a_2841_;
v___y_2917_ = v_a_2842_;
v___y_2918_ = v___x_2870_;
v___y_2919_ = v_a_2844_;
goto v___jp_2913_;
}
else
{
uint8_t v___x_2970_; 
v___x_2970_ = l_Lean_Expr_hasSyntheticSorry(v_a_2874_);
if (v___x_2970_ == 0)
{
v___y_2951_ = v_a_2839_;
v___y_2952_ = v_a_2840_;
v___y_2953_ = v_a_2841_;
v___y_2954_ = v_a_2842_;
v___y_2955_ = v___x_2870_;
v___y_2956_ = v_a_2844_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2971_; lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_a_2874_);
lean_dec_ref_known(v___x_2870_, 14);
v___x_2971_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
v___jp_2875_:
{
if (v___y_2885_ == 0)
{
if (lean_obj_tag(v___y_2881_) == 0)
{
lean_dec_ref_known(v___y_2881_, 2);
lean_dec_ref(v___y_2883_);
lean_dec(v_a_2874_);
return v___y_2878_;
}
else
{
lean_object* v_id_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2899_; 
v_id_2886_ = lean_ctor_get(v___y_2881_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___y_2881_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___y_2881_, 1);
lean_dec(v_unused_2900_);
v___x_2888_ = v___y_2881_;
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_id_2886_);
lean_dec(v___y_2881_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint8_t v___x_2890_; 
v___x_2890_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2880_, v_id_2886_);
lean_dec(v_id_2886_);
if (v___x_2890_ == 0)
{
lean_del_object(v___x_2888_);
lean_dec_ref(v___y_2883_);
lean_dec(v_a_2874_);
return v___y_2878_;
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec_ref(v___y_2878_);
v___x_2891_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_2892_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_2893_ = l_Lean_indentExpr(v_a_2874_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set_tag(v___x_2888_, 7);
lean_ctor_set(v___x_2888_, 1, v___x_2893_);
lean_ctor_set(v___x_2888_, 0, v___x_2892_);
v___x_2895_ = v___x_2888_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___x_2891_);
v___x_2897_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2896_, v___y_2884_, v___y_2876_, v___y_2879_, v___y_2877_, v___y_2883_, v___y_2882_);
lean_dec_ref(v___y_2883_);
return v___x_2897_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2881_);
lean_dec(v_a_2874_);
return v___y_2878_;
}
}
v___jp_2901_:
{
lean_object* v___x_2908_; 
lean_inc(v_a_2874_);
v___x_2908_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_2874_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref(v___y_2906_);
lean_dec(v_a_2874_);
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
v___x_2910_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2911_ = l_Lean_Exception_isInterrupt(v_a_2909_);
if (v___x_2911_ == 0)
{
uint8_t v___x_2912_; 
lean_inc(v_a_2909_);
v___x_2912_ = l_Lean_Exception_isRuntime(v_a_2909_);
v___y_2876_ = v___y_2903_;
v___y_2877_ = v___y_2905_;
v___y_2878_ = v___x_2908_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2910_;
v___y_2881_ = v_a_2909_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2906_;
v___y_2884_ = v___y_2902_;
v___y_2885_ = v___x_2912_;
goto v___jp_2875_;
}
else
{
v___y_2876_ = v___y_2903_;
v___y_2877_ = v___y_2905_;
v___y_2878_ = v___x_2908_;
v___y_2879_ = v___y_2904_;
v___y_2880_ = v___x_2910_;
v___y_2881_ = v_a_2909_;
v___y_2882_ = v___y_2907_;
v___y_2883_ = v___y_2906_;
v___y_2884_ = v___y_2902_;
v___y_2885_ = v___x_2911_;
goto v___jp_2875_;
}
}
}
v___jp_2913_:
{
lean_object* v___x_2920_; 
lean_inc(v_a_2874_);
v___x_2920_ = l_Lean_Meta_getMVars(v_a_2874_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2921_, v___x_2848_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v_a_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; uint8_t v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = lean_unbox(v_a_2923_);
lean_dec(v_a_2923_);
if (v___x_2924_ == 0)
{
v___y_2902_ = v___y_2914_;
v___y_2903_ = v___y_2915_;
v___y_2904_ = v___y_2916_;
v___y_2905_ = v___y_2917_;
v___y_2906_ = v___y_2918_;
v___y_2907_ = v___y_2919_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2925_; lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___y_2918_);
lean_dec(v_a_2874_);
v___x_2925_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___y_2918_);
lean_dec(v_a_2874_);
v_a_2934_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2922_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2922_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v___y_2918_);
lean_dec(v_a_2874_);
v_a_2942_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2920_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2920_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
v___jp_2950_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v___x_2957_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_2958_ = l_Lean_indentExpr(v_a_2874_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2959_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec_ref(v___y_2955_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref_known(v___x_2870_, 14);
v_a_2980_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2871_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2871_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_fileName_3005_; lean_object* v_fileMap_3006_; lean_object* v_options_3007_; lean_object* v_currRecDepth_3008_; lean_object* v_maxRecDepth_3009_; lean_object* v_ref_3010_; lean_object* v_currNamespace_3011_; lean_object* v_openDecls_3012_; lean_object* v_initHeartbeats_3013_; lean_object* v_maxHeartbeats_3014_; lean_object* v_quotContext_3015_; lean_object* v_currMacroScope_3016_; uint8_t v_diag_3017_; lean_object* v_cancelTk_x3f_3018_; uint8_t v_suppressElabErrors_3019_; lean_object* v_inheritedTraceOptions_3020_; lean_object* v_ref_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_fileName_3005_ = lean_ctor_get(v_a_3002_, 0);
v_fileMap_3006_ = lean_ctor_get(v_a_3002_, 1);
v_options_3007_ = lean_ctor_get(v_a_3002_, 2);
v_currRecDepth_3008_ = lean_ctor_get(v_a_3002_, 3);
v_maxRecDepth_3009_ = lean_ctor_get(v_a_3002_, 4);
v_ref_3010_ = lean_ctor_get(v_a_3002_, 5);
v_currNamespace_3011_ = lean_ctor_get(v_a_3002_, 6);
v_openDecls_3012_ = lean_ctor_get(v_a_3002_, 7);
v_initHeartbeats_3013_ = lean_ctor_get(v_a_3002_, 8);
v_maxHeartbeats_3014_ = lean_ctor_get(v_a_3002_, 9);
v_quotContext_3015_ = lean_ctor_get(v_a_3002_, 10);
v_currMacroScope_3016_ = lean_ctor_get(v_a_3002_, 11);
v_diag_3017_ = lean_ctor_get_uint8(v_a_3002_, sizeof(void*)*14);
v_cancelTk_x3f_3018_ = lean_ctor_get(v_a_3002_, 12);
v_suppressElabErrors_3019_ = lean_ctor_get_uint8(v_a_3002_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3020_ = lean_ctor_get(v_a_3002_, 13);
v_ref_3021_ = l_Lean_replaceRef(v_stx_2997_, v_ref_3010_);
lean_inc_ref(v_inheritedTraceOptions_3020_);
lean_inc(v_cancelTk_x3f_3018_);
lean_inc(v_currMacroScope_3016_);
lean_inc(v_quotContext_3015_);
lean_inc(v_maxHeartbeats_3014_);
lean_inc(v_initHeartbeats_3013_);
lean_inc(v_openDecls_3012_);
lean_inc(v_currNamespace_3011_);
lean_inc(v_maxRecDepth_3009_);
lean_inc(v_currRecDepth_3008_);
lean_inc_ref(v_options_3007_);
lean_inc_ref(v_fileMap_3006_);
lean_inc_ref(v_fileName_3005_);
v___x_3022_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3022_, 0, v_fileName_3005_);
lean_ctor_set(v___x_3022_, 1, v_fileMap_3006_);
lean_ctor_set(v___x_3022_, 2, v_options_3007_);
lean_ctor_set(v___x_3022_, 3, v_currRecDepth_3008_);
lean_ctor_set(v___x_3022_, 4, v_maxRecDepth_3009_);
lean_ctor_set(v___x_3022_, 5, v_ref_3021_);
lean_ctor_set(v___x_3022_, 6, v_currNamespace_3011_);
lean_ctor_set(v___x_3022_, 7, v_openDecls_3012_);
lean_ctor_set(v___x_3022_, 8, v_initHeartbeats_3013_);
lean_ctor_set(v___x_3022_, 9, v_maxHeartbeats_3014_);
lean_ctor_set(v___x_3022_, 10, v_quotContext_3015_);
lean_ctor_set(v___x_3022_, 11, v_currMacroScope_3016_);
lean_ctor_set(v___x_3022_, 12, v_cancelTk_x3f_3018_);
lean_ctor_set(v___x_3022_, 13, v_inheritedTraceOptions_3020_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*14, v_diag_3017_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*14 + 1, v_suppressElabErrors_3019_);
lean_inc(v_stx_2997_);
v___x_3023_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v___x_3022_, v_a_3003_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref_known(v___x_3022_, 14);
lean_dec(v_stx_2997_);
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_fst_3028_; lean_object* v___x_3030_; 
v_fst_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_fst_3028_);
lean_dec(v_a_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_fst_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_fst_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3048_; 
v_a_3033_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3035_ = v___x_3023_;
v_isShared_3036_ = v_isSharedCheck_3048_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3023_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3048_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3033_);
if (v_isShared_3036_ == 0)
{
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3033_);
v___x_3039_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
uint8_t v___y_3041_; uint8_t v___x_3045_; 
v___x_3045_ = l_Lean_Exception_isInterrupt(v_a_3033_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
lean_inc(v_a_3033_);
v___x_3046_ = l_Lean_Exception_isRuntime(v_a_3033_);
v___y_3041_ = v___x_3046_;
goto v___jp_3040_;
}
else
{
v___y_3041_ = v___x_3045_;
goto v___jp_3040_;
}
v___jp_3040_:
{
if (v___y_3041_ == 0)
{
if (lean_obj_tag(v_a_3033_) == 0)
{
lean_dec_ref_known(v_a_3033_, 2);
lean_dec_ref_known(v___x_3022_, 14);
lean_dec(v_stx_2997_);
return v___x_3039_;
}
else
{
lean_object* v_id_3042_; uint8_t v___x_3043_; 
v_id_3042_ = lean_ctor_get(v_a_3033_, 0);
lean_inc(v_id_3042_);
lean_dec_ref_known(v_a_3033_, 2);
v___x_3043_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3037_, v_id_3042_);
lean_dec(v_id_3042_);
if (v___x_3043_ == 0)
{
lean_dec_ref_known(v___x_3022_, 14);
lean_dec(v_stx_2997_);
return v___x_3039_;
}
else
{
lean_object* v___x_3044_; 
lean_dec_ref(v___x_3039_);
v___x_3044_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v___x_3022_, v_a_3003_);
lean_dec_ref_known(v___x_3022_, 14);
return v___x_3044_;
}
}
}
else
{
lean_dec(v_a_3033_);
lean_dec_ref_known(v___x_3022_, 14);
lean_dec(v_stx_2997_);
return v___x_3039_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
return v_res_3057_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(0);
v___x_3064_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3065_ = l_Lean_Expr_const___override(v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3066_; lean_object* v_ty_x3f_3067_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3067_, 0, v___x_3066_);
return v_ty_x3f_3067_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3069_ = l_Lean_MessageData_ofExpr(v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3071_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3074_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_ty_x3f_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_fileName_3090_; lean_object* v_fileMap_3091_; lean_object* v_options_3092_; lean_object* v_currRecDepth_3093_; lean_object* v_maxRecDepth_3094_; lean_object* v_ref_3095_; lean_object* v_currNamespace_3096_; lean_object* v_openDecls_3097_; lean_object* v_initHeartbeats_3098_; lean_object* v_maxHeartbeats_3099_; lean_object* v_quotContext_3100_; lean_object* v_currMacroScope_3101_; uint8_t v_diag_3102_; lean_object* v_cancelTk_x3f_3103_; uint8_t v_suppressElabErrors_3104_; lean_object* v_inheritedTraceOptions_3105_; uint8_t v___x_3106_; lean_object* v_ref_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_ty_x3f_3084_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3085_ = 1;
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_box(v___x_3085_);
v___x_3088_ = lean_box(v___x_3085_);
lean_inc(v_stx_3076_);
v___x_3089_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3089_, 0, v_stx_3076_);
lean_closure_set(v___x_3089_, 1, v_ty_x3f_3084_);
lean_closure_set(v___x_3089_, 2, v___x_3087_);
lean_closure_set(v___x_3089_, 3, v___x_3088_);
lean_closure_set(v___x_3089_, 4, v___x_3086_);
v_fileName_3090_ = lean_ctor_get(v_a_3081_, 0);
v_fileMap_3091_ = lean_ctor_get(v_a_3081_, 1);
v_options_3092_ = lean_ctor_get(v_a_3081_, 2);
v_currRecDepth_3093_ = lean_ctor_get(v_a_3081_, 3);
v_maxRecDepth_3094_ = lean_ctor_get(v_a_3081_, 4);
v_ref_3095_ = lean_ctor_get(v_a_3081_, 5);
v_currNamespace_3096_ = lean_ctor_get(v_a_3081_, 6);
v_openDecls_3097_ = lean_ctor_get(v_a_3081_, 7);
v_initHeartbeats_3098_ = lean_ctor_get(v_a_3081_, 8);
v_maxHeartbeats_3099_ = lean_ctor_get(v_a_3081_, 9);
v_quotContext_3100_ = lean_ctor_get(v_a_3081_, 10);
v_currMacroScope_3101_ = lean_ctor_get(v_a_3081_, 11);
v_diag_3102_ = lean_ctor_get_uint8(v_a_3081_, sizeof(void*)*14);
v_cancelTk_x3f_3103_ = lean_ctor_get(v_a_3081_, 12);
v_suppressElabErrors_3104_ = lean_ctor_get_uint8(v_a_3081_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3105_ = lean_ctor_get(v_a_3081_, 13);
v___x_3106_ = 1;
v_ref_3107_ = l_Lean_replaceRef(v_stx_3076_, v_ref_3095_);
lean_dec(v_stx_3076_);
lean_inc_ref(v_inheritedTraceOptions_3105_);
lean_inc(v_cancelTk_x3f_3103_);
lean_inc(v_currMacroScope_3101_);
lean_inc(v_quotContext_3100_);
lean_inc(v_maxHeartbeats_3099_);
lean_inc(v_initHeartbeats_3098_);
lean_inc(v_openDecls_3097_);
lean_inc(v_currNamespace_3096_);
lean_inc(v_maxRecDepth_3094_);
lean_inc(v_currRecDepth_3093_);
lean_inc_ref(v_options_3092_);
lean_inc_ref(v_fileMap_3091_);
lean_inc_ref(v_fileName_3090_);
v___x_3108_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3108_, 0, v_fileName_3090_);
lean_ctor_set(v___x_3108_, 1, v_fileMap_3091_);
lean_ctor_set(v___x_3108_, 2, v_options_3092_);
lean_ctor_set(v___x_3108_, 3, v_currRecDepth_3093_);
lean_ctor_set(v___x_3108_, 4, v_maxRecDepth_3094_);
lean_ctor_set(v___x_3108_, 5, v_ref_3107_);
lean_ctor_set(v___x_3108_, 6, v_currNamespace_3096_);
lean_ctor_set(v___x_3108_, 7, v_openDecls_3097_);
lean_ctor_set(v___x_3108_, 8, v_initHeartbeats_3098_);
lean_ctor_set(v___x_3108_, 9, v_maxHeartbeats_3099_);
lean_ctor_set(v___x_3108_, 10, v_quotContext_3100_);
lean_ctor_set(v___x_3108_, 11, v_currMacroScope_3101_);
lean_ctor_set(v___x_3108_, 12, v_cancelTk_x3f_3103_);
lean_ctor_set(v___x_3108_, 13, v_inheritedTraceOptions_3105_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*14, v_diag_3102_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*14 + 1, v_suppressElabErrors_3104_);
v___x_3109_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3089_, v___x_3106_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v___x_3108_, v_a_3082_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v_a_3112_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; uint8_t v___x_3207_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3110_, v_a_3080_);
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref(v___x_3111_);
v___x_3207_ = l_Lean_Expr_hasSorry(v_a_3112_);
if (v___x_3207_ == 0)
{
v___y_3152_ = v_a_3077_;
v___y_3153_ = v_a_3078_;
v___y_3154_ = v_a_3079_;
v___y_3155_ = v_a_3080_;
v___y_3156_ = v___x_3108_;
v___y_3157_ = v_a_3082_;
goto v___jp_3151_;
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = l_Lean_Expr_hasSyntheticSorry(v_a_3112_);
if (v___x_3208_ == 0)
{
v___y_3189_ = v_a_3077_;
v___y_3190_ = v_a_3078_;
v___y_3191_ = v_a_3079_;
v___y_3192_ = v_a_3080_;
v___y_3193_ = v___x_3108_;
v___y_3194_ = v_a_3082_;
goto v___jp_3188_;
}
else
{
lean_object* v___x_3209_; lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_a_3112_);
lean_dec_ref_known(v___x_3108_, 14);
v___x_3209_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
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
v___jp_3113_:
{
if (v___y_3123_ == 0)
{
if (lean_obj_tag(v___y_3121_) == 0)
{
lean_dec_ref_known(v___y_3121_, 2);
lean_dec_ref(v___y_3120_);
lean_dec(v_a_3112_);
return v___y_3114_;
}
else
{
lean_object* v_id_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3137_; 
v_id_3124_ = lean_ctor_get(v___y_3121_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___y_3121_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___y_3121_, 1);
lean_dec(v_unused_3138_);
v___x_3126_ = v___y_3121_;
v_isShared_3127_ = v_isSharedCheck_3137_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_id_3124_);
lean_dec(v___y_3121_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3137_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
uint8_t v___x_3128_; 
v___x_3128_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3117_, v_id_3124_);
lean_dec(v_id_3124_);
if (v___x_3128_ == 0)
{
lean_del_object(v___x_3126_);
lean_dec_ref(v___y_3120_);
lean_dec(v_a_3112_);
return v___y_3114_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec_ref(v___y_3114_);
v___x_3129_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3130_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3131_ = l_Lean_indentExpr(v_a_3112_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set_tag(v___x_3126_, 7);
lean_ctor_set(v___x_3126_, 1, v___x_3131_);
lean_ctor_set(v___x_3126_, 0, v___x_3130_);
v___x_3133_ = v___x_3126_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3129_);
v___x_3135_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3134_, v___y_3116_, v___y_3115_, v___y_3119_, v___y_3118_, v___y_3120_, v___y_3122_);
lean_dec_ref(v___y_3120_);
return v___x_3135_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v_a_3112_);
return v___y_3114_;
}
}
v___jp_3139_:
{
lean_object* v___x_3146_; 
lean_inc(v_a_3112_);
v___x_3146_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3112_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_dec_ref(v___y_3144_);
lean_dec(v_a_3112_);
return v___x_3146_;
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v___x_3148_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3149_ = l_Lean_Exception_isInterrupt(v_a_3147_);
if (v___x_3149_ == 0)
{
uint8_t v___x_3150_; 
lean_inc(v_a_3147_);
v___x_3150_ = l_Lean_Exception_isRuntime(v_a_3147_);
v___y_3114_ = v___x_3146_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v___x_3148_;
v___y_3118_ = v___y_3143_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3144_;
v___y_3121_ = v_a_3147_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v___x_3150_;
goto v___jp_3113_;
}
else
{
v___y_3114_ = v___x_3146_;
v___y_3115_ = v___y_3141_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v___x_3148_;
v___y_3118_ = v___y_3143_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3144_;
v___y_3121_ = v_a_3147_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v___x_3149_;
goto v___jp_3113_;
}
}
}
v___jp_3151_:
{
lean_object* v___x_3158_; 
lean_inc(v_a_3112_);
v___x_3158_ = l_Lean_Meta_getMVars(v_a_3112_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3159_, v___x_3086_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v_a_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; uint8_t v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = lean_unbox(v_a_3161_);
lean_dec(v_a_3161_);
if (v___x_3162_ == 0)
{
v___y_3140_ = v___y_3152_;
v___y_3141_ = v___y_3153_;
v___y_3142_ = v___y_3154_;
v___y_3143_ = v___y_3155_;
v___y_3144_ = v___y_3156_;
v___y_3145_ = v___y_3157_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3163_; lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v___y_3156_);
lean_dec(v_a_3112_);
v___x_3163_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v___y_3156_);
lean_dec(v_a_3112_);
v_a_3172_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3160_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3160_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v___y_3156_);
lean_dec(v_a_3112_);
v_a_3180_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3158_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3158_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
v___jp_3188_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
v___x_3195_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3196_ = l_Lean_indentExpr(v_a_3112_);
v___x_3197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3197_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec_ref(v___y_3193_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref_known(v___x_3108_, 14);
v_a_3218_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3109_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3109_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_fileName_3243_; lean_object* v_fileMap_3244_; lean_object* v_options_3245_; lean_object* v_currRecDepth_3246_; lean_object* v_maxRecDepth_3247_; lean_object* v_ref_3248_; lean_object* v_currNamespace_3249_; lean_object* v_openDecls_3250_; lean_object* v_initHeartbeats_3251_; lean_object* v_maxHeartbeats_3252_; lean_object* v_quotContext_3253_; lean_object* v_currMacroScope_3254_; uint8_t v_diag_3255_; lean_object* v_cancelTk_x3f_3256_; uint8_t v_suppressElabErrors_3257_; lean_object* v_inheritedTraceOptions_3258_; lean_object* v_ref_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_fileName_3243_ = lean_ctor_get(v_a_3240_, 0);
v_fileMap_3244_ = lean_ctor_get(v_a_3240_, 1);
v_options_3245_ = lean_ctor_get(v_a_3240_, 2);
v_currRecDepth_3246_ = lean_ctor_get(v_a_3240_, 3);
v_maxRecDepth_3247_ = lean_ctor_get(v_a_3240_, 4);
v_ref_3248_ = lean_ctor_get(v_a_3240_, 5);
v_currNamespace_3249_ = lean_ctor_get(v_a_3240_, 6);
v_openDecls_3250_ = lean_ctor_get(v_a_3240_, 7);
v_initHeartbeats_3251_ = lean_ctor_get(v_a_3240_, 8);
v_maxHeartbeats_3252_ = lean_ctor_get(v_a_3240_, 9);
v_quotContext_3253_ = lean_ctor_get(v_a_3240_, 10);
v_currMacroScope_3254_ = lean_ctor_get(v_a_3240_, 11);
v_diag_3255_ = lean_ctor_get_uint8(v_a_3240_, sizeof(void*)*14);
v_cancelTk_x3f_3256_ = lean_ctor_get(v_a_3240_, 12);
v_suppressElabErrors_3257_ = lean_ctor_get_uint8(v_a_3240_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3258_ = lean_ctor_get(v_a_3240_, 13);
v_ref_3259_ = l_Lean_replaceRef(v_stx_3235_, v_ref_3248_);
lean_inc_ref(v_inheritedTraceOptions_3258_);
lean_inc(v_cancelTk_x3f_3256_);
lean_inc(v_currMacroScope_3254_);
lean_inc(v_quotContext_3253_);
lean_inc(v_maxHeartbeats_3252_);
lean_inc(v_initHeartbeats_3251_);
lean_inc(v_openDecls_3250_);
lean_inc(v_currNamespace_3249_);
lean_inc(v_maxRecDepth_3247_);
lean_inc(v_currRecDepth_3246_);
lean_inc_ref(v_options_3245_);
lean_inc_ref(v_fileMap_3244_);
lean_inc_ref(v_fileName_3243_);
v___x_3260_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3260_, 0, v_fileName_3243_);
lean_ctor_set(v___x_3260_, 1, v_fileMap_3244_);
lean_ctor_set(v___x_3260_, 2, v_options_3245_);
lean_ctor_set(v___x_3260_, 3, v_currRecDepth_3246_);
lean_ctor_set(v___x_3260_, 4, v_maxRecDepth_3247_);
lean_ctor_set(v___x_3260_, 5, v_ref_3259_);
lean_ctor_set(v___x_3260_, 6, v_currNamespace_3249_);
lean_ctor_set(v___x_3260_, 7, v_openDecls_3250_);
lean_ctor_set(v___x_3260_, 8, v_initHeartbeats_3251_);
lean_ctor_set(v___x_3260_, 9, v_maxHeartbeats_3252_);
lean_ctor_set(v___x_3260_, 10, v_quotContext_3253_);
lean_ctor_set(v___x_3260_, 11, v_currMacroScope_3254_);
lean_ctor_set(v___x_3260_, 12, v_cancelTk_x3f_3256_);
lean_ctor_set(v___x_3260_, 13, v_inheritedTraceOptions_3258_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*14, v_diag_3255_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*14 + 1, v_suppressElabErrors_3257_);
lean_inc(v_stx_3235_);
v___x_3261_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v___x_3260_, v_a_3241_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref_known(v___x_3260_, 14);
lean_dec(v_stx_3235_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v_fst_3266_; lean_object* v___x_3268_; 
v_fst_3266_ = lean_ctor_get(v_a_3262_, 0);
lean_inc(v_fst_3266_);
lean_dec(v_a_3262_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v_fst_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_fst_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3286_; 
v_a_3271_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3273_ = v___x_3261_;
v_isShared_3274_ = v_isSharedCheck_3286_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3261_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3286_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3271_);
if (v_isShared_3274_ == 0)
{
v___x_3277_ = v___x_3273_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3271_);
v___x_3277_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
uint8_t v___y_3279_; uint8_t v___x_3283_; 
v___x_3283_ = l_Lean_Exception_isInterrupt(v_a_3271_);
if (v___x_3283_ == 0)
{
uint8_t v___x_3284_; 
lean_inc(v_a_3271_);
v___x_3284_ = l_Lean_Exception_isRuntime(v_a_3271_);
v___y_3279_ = v___x_3284_;
goto v___jp_3278_;
}
else
{
v___y_3279_ = v___x_3283_;
goto v___jp_3278_;
}
v___jp_3278_:
{
if (v___y_3279_ == 0)
{
if (lean_obj_tag(v_a_3271_) == 0)
{
lean_dec_ref_known(v_a_3271_, 2);
lean_dec_ref_known(v___x_3260_, 14);
lean_dec(v_stx_3235_);
return v___x_3277_;
}
else
{
lean_object* v_id_3280_; uint8_t v___x_3281_; 
v_id_3280_ = lean_ctor_get(v_a_3271_, 0);
lean_inc(v_id_3280_);
lean_dec_ref_known(v_a_3271_, 2);
v___x_3281_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3275_, v_id_3280_);
lean_dec(v_id_3280_);
if (v___x_3281_ == 0)
{
lean_dec_ref_known(v___x_3260_, 14);
lean_dec(v_stx_3235_);
return v___x_3277_;
}
else
{
lean_object* v___x_3282_; 
lean_dec_ref(v___x_3277_);
v___x_3282_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v___x_3260_, v_a_3241_);
lean_dec_ref_known(v___x_3260_, 14);
return v___x_3282_;
}
}
}
else
{
lean_dec(v_a_3271_);
lean_dec_ref_known(v___x_3260_, 14);
lean_dec(v_stx_3235_);
return v___x_3277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3297_ = l_Lean_MessageData_ofExpr(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3299_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3298_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3302_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_ty_x3f_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_fileName_3318_; lean_object* v_fileMap_3319_; lean_object* v_options_3320_; lean_object* v_currRecDepth_3321_; lean_object* v_maxRecDepth_3322_; lean_object* v_ref_3323_; lean_object* v_currNamespace_3324_; lean_object* v_openDecls_3325_; lean_object* v_initHeartbeats_3326_; lean_object* v_maxHeartbeats_3327_; lean_object* v_quotContext_3328_; lean_object* v_currMacroScope_3329_; uint8_t v_diag_3330_; lean_object* v_cancelTk_x3f_3331_; uint8_t v_suppressElabErrors_3332_; lean_object* v_inheritedTraceOptions_3333_; uint8_t v___x_3334_; lean_object* v_ref_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_ty_x3f_3312_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3313_ = 1;
v___x_3314_ = lean_box(0);
v___x_3315_ = lean_box(v___x_3313_);
v___x_3316_ = lean_box(v___x_3313_);
lean_inc(v_stx_3304_);
v___x_3317_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3317_, 0, v_stx_3304_);
lean_closure_set(v___x_3317_, 1, v_ty_x3f_3312_);
lean_closure_set(v___x_3317_, 2, v___x_3315_);
lean_closure_set(v___x_3317_, 3, v___x_3316_);
lean_closure_set(v___x_3317_, 4, v___x_3314_);
v_fileName_3318_ = lean_ctor_get(v_a_3309_, 0);
v_fileMap_3319_ = lean_ctor_get(v_a_3309_, 1);
v_options_3320_ = lean_ctor_get(v_a_3309_, 2);
v_currRecDepth_3321_ = lean_ctor_get(v_a_3309_, 3);
v_maxRecDepth_3322_ = lean_ctor_get(v_a_3309_, 4);
v_ref_3323_ = lean_ctor_get(v_a_3309_, 5);
v_currNamespace_3324_ = lean_ctor_get(v_a_3309_, 6);
v_openDecls_3325_ = lean_ctor_get(v_a_3309_, 7);
v_initHeartbeats_3326_ = lean_ctor_get(v_a_3309_, 8);
v_maxHeartbeats_3327_ = lean_ctor_get(v_a_3309_, 9);
v_quotContext_3328_ = lean_ctor_get(v_a_3309_, 10);
v_currMacroScope_3329_ = lean_ctor_get(v_a_3309_, 11);
v_diag_3330_ = lean_ctor_get_uint8(v_a_3309_, sizeof(void*)*14);
v_cancelTk_x3f_3331_ = lean_ctor_get(v_a_3309_, 12);
v_suppressElabErrors_3332_ = lean_ctor_get_uint8(v_a_3309_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3333_ = lean_ctor_get(v_a_3309_, 13);
v___x_3334_ = 1;
v_ref_3335_ = l_Lean_replaceRef(v_stx_3304_, v_ref_3323_);
lean_dec(v_stx_3304_);
lean_inc_ref(v_inheritedTraceOptions_3333_);
lean_inc(v_cancelTk_x3f_3331_);
lean_inc(v_currMacroScope_3329_);
lean_inc(v_quotContext_3328_);
lean_inc(v_maxHeartbeats_3327_);
lean_inc(v_initHeartbeats_3326_);
lean_inc(v_openDecls_3325_);
lean_inc(v_currNamespace_3324_);
lean_inc(v_maxRecDepth_3322_);
lean_inc(v_currRecDepth_3321_);
lean_inc_ref(v_options_3320_);
lean_inc_ref(v_fileMap_3319_);
lean_inc_ref(v_fileName_3318_);
v___x_3336_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3336_, 0, v_fileName_3318_);
lean_ctor_set(v___x_3336_, 1, v_fileMap_3319_);
lean_ctor_set(v___x_3336_, 2, v_options_3320_);
lean_ctor_set(v___x_3336_, 3, v_currRecDepth_3321_);
lean_ctor_set(v___x_3336_, 4, v_maxRecDepth_3322_);
lean_ctor_set(v___x_3336_, 5, v_ref_3335_);
lean_ctor_set(v___x_3336_, 6, v_currNamespace_3324_);
lean_ctor_set(v___x_3336_, 7, v_openDecls_3325_);
lean_ctor_set(v___x_3336_, 8, v_initHeartbeats_3326_);
lean_ctor_set(v___x_3336_, 9, v_maxHeartbeats_3327_);
lean_ctor_set(v___x_3336_, 10, v_quotContext_3328_);
lean_ctor_set(v___x_3336_, 11, v_currMacroScope_3329_);
lean_ctor_set(v___x_3336_, 12, v_cancelTk_x3f_3331_);
lean_ctor_set(v___x_3336_, 13, v_inheritedTraceOptions_3333_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*14, v_diag_3330_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*14 + 1, v_suppressElabErrors_3332_);
v___x_3337_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3317_, v___x_3334_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v___x_3336_, v_a_3310_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v_a_3340_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; uint8_t v___y_3351_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___x_3435_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3338_, v_a_3308_);
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3339_);
v___x_3435_ = l_Lean_Expr_hasSorry(v_a_3340_);
if (v___x_3435_ == 0)
{
v___y_3380_ = v_a_3305_;
v___y_3381_ = v_a_3306_;
v___y_3382_ = v_a_3307_;
v___y_3383_ = v_a_3308_;
v___y_3384_ = v___x_3336_;
v___y_3385_ = v_a_3310_;
goto v___jp_3379_;
}
else
{
uint8_t v___x_3436_; 
v___x_3436_ = l_Lean_Expr_hasSyntheticSorry(v_a_3340_);
if (v___x_3436_ == 0)
{
v___y_3417_ = v_a_3305_;
v___y_3418_ = v_a_3306_;
v___y_3419_ = v_a_3307_;
v___y_3420_ = v_a_3308_;
v___y_3421_ = v___x_3336_;
v___y_3422_ = v_a_3310_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3437_; lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_a_3340_);
lean_dec_ref_known(v___x_3336_, 14);
v___x_3437_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
v___jp_3341_:
{
if (v___y_3351_ == 0)
{
if (lean_obj_tag(v___y_3345_) == 0)
{
lean_dec_ref_known(v___y_3345_, 2);
lean_dec_ref(v___y_3350_);
lean_dec(v_a_3340_);
return v___y_3344_;
}
else
{
lean_object* v_id_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3365_; 
v_id_3352_ = lean_ctor_get(v___y_3345_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___y_3345_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v___y_3345_, 1);
lean_dec(v_unused_3366_);
v___x_3354_ = v___y_3345_;
v_isShared_3355_ = v_isSharedCheck_3365_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_id_3352_);
lean_dec(v___y_3345_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3365_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v___x_3356_; 
v___x_3356_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3343_, v_id_3352_);
lean_dec(v_id_3352_);
if (v___x_3356_ == 0)
{
lean_del_object(v___x_3354_);
lean_dec_ref(v___y_3350_);
lean_dec(v_a_3340_);
return v___y_3344_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_dec_ref(v___y_3344_);
v___x_3357_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3358_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3359_ = l_Lean_indentExpr(v_a_3340_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set_tag(v___x_3354_, 7);
lean_ctor_set(v___x_3354_, 1, v___x_3359_);
lean_ctor_set(v___x_3354_, 0, v___x_3358_);
v___x_3361_ = v___x_3354_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v___x_3357_);
v___x_3363_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3362_, v___y_3348_, v___y_3349_, v___y_3346_, v___y_3347_, v___y_3350_, v___y_3342_);
lean_dec_ref(v___y_3350_);
return v___x_3363_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3345_);
lean_dec(v_a_3340_);
return v___y_3344_;
}
}
v___jp_3367_:
{
lean_object* v___x_3374_; 
lean_inc(v_a_3340_);
v___x_3374_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3340_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_dec_ref(v___y_3372_);
lean_dec(v_a_3340_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
v___x_3376_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3377_ = l_Lean_Exception_isInterrupt(v_a_3375_);
if (v___x_3377_ == 0)
{
uint8_t v___x_3378_; 
lean_inc(v_a_3375_);
v___x_3378_ = l_Lean_Exception_isRuntime(v_a_3375_);
v___y_3342_ = v___y_3373_;
v___y_3343_ = v___x_3376_;
v___y_3344_ = v___x_3374_;
v___y_3345_ = v_a_3375_;
v___y_3346_ = v___y_3370_;
v___y_3347_ = v___y_3371_;
v___y_3348_ = v___y_3368_;
v___y_3349_ = v___y_3369_;
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___x_3378_;
goto v___jp_3341_;
}
else
{
v___y_3342_ = v___y_3373_;
v___y_3343_ = v___x_3376_;
v___y_3344_ = v___x_3374_;
v___y_3345_ = v_a_3375_;
v___y_3346_ = v___y_3370_;
v___y_3347_ = v___y_3371_;
v___y_3348_ = v___y_3368_;
v___y_3349_ = v___y_3369_;
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___x_3377_;
goto v___jp_3341_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3386_; 
lean_inc(v_a_3340_);
v___x_3386_ = l_Lean_Meta_getMVars(v_a_3340_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3387_, v___x_3314_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v_a_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; uint8_t v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = lean_unbox(v_a_3389_);
lean_dec(v_a_3389_);
if (v___x_3390_ == 0)
{
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3381_;
v___y_3370_ = v___y_3382_;
v___y_3371_ = v___y_3383_;
v___y_3372_ = v___y_3384_;
v___y_3373_ = v___y_3385_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3391_; lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v___y_3384_);
lean_dec(v_a_3340_);
v___x_3391_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec_ref(v___y_3384_);
lean_dec(v_a_3340_);
v_a_3400_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3388_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3388_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v___y_3384_);
lean_dec(v_a_3340_);
v_a_3408_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3386_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3386_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
v___jp_3416_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v___x_3423_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3424_ = l_Lean_indentExpr(v_a_3340_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3425_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec_ref(v___y_3421_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref_known(v___x_3336_, 14);
v_a_3446_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3337_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3337_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
return v_res_3462_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_box(0);
v___x_3469_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3470_ = l_Lean_Expr_const___override(v___x_3469_, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3471_; lean_object* v_ty_x3f_3472_; 
v___x_3471_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3472_, 0, v___x_3471_);
return v_ty_x3f_3472_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3474_ = l_Lean_MessageData_ofExpr(v___x_3473_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3476_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3479_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v___x_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_ty_x3f_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v_fileName_3495_; lean_object* v_fileMap_3496_; lean_object* v_options_3497_; lean_object* v_currRecDepth_3498_; lean_object* v_maxRecDepth_3499_; lean_object* v_ref_3500_; lean_object* v_currNamespace_3501_; lean_object* v_openDecls_3502_; lean_object* v_initHeartbeats_3503_; lean_object* v_maxHeartbeats_3504_; lean_object* v_quotContext_3505_; lean_object* v_currMacroScope_3506_; uint8_t v_diag_3507_; lean_object* v_cancelTk_x3f_3508_; uint8_t v_suppressElabErrors_3509_; lean_object* v_inheritedTraceOptions_3510_; uint8_t v___x_3511_; lean_object* v_ref_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_ty_x3f_3489_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3490_ = 1;
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_box(v___x_3490_);
v___x_3493_ = lean_box(v___x_3490_);
lean_inc(v_stx_3481_);
v___x_3494_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3494_, 0, v_stx_3481_);
lean_closure_set(v___x_3494_, 1, v_ty_x3f_3489_);
lean_closure_set(v___x_3494_, 2, v___x_3492_);
lean_closure_set(v___x_3494_, 3, v___x_3493_);
lean_closure_set(v___x_3494_, 4, v___x_3491_);
v_fileName_3495_ = lean_ctor_get(v_a_3486_, 0);
v_fileMap_3496_ = lean_ctor_get(v_a_3486_, 1);
v_options_3497_ = lean_ctor_get(v_a_3486_, 2);
v_currRecDepth_3498_ = lean_ctor_get(v_a_3486_, 3);
v_maxRecDepth_3499_ = lean_ctor_get(v_a_3486_, 4);
v_ref_3500_ = lean_ctor_get(v_a_3486_, 5);
v_currNamespace_3501_ = lean_ctor_get(v_a_3486_, 6);
v_openDecls_3502_ = lean_ctor_get(v_a_3486_, 7);
v_initHeartbeats_3503_ = lean_ctor_get(v_a_3486_, 8);
v_maxHeartbeats_3504_ = lean_ctor_get(v_a_3486_, 9);
v_quotContext_3505_ = lean_ctor_get(v_a_3486_, 10);
v_currMacroScope_3506_ = lean_ctor_get(v_a_3486_, 11);
v_diag_3507_ = lean_ctor_get_uint8(v_a_3486_, sizeof(void*)*14);
v_cancelTk_x3f_3508_ = lean_ctor_get(v_a_3486_, 12);
v_suppressElabErrors_3509_ = lean_ctor_get_uint8(v_a_3486_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3510_ = lean_ctor_get(v_a_3486_, 13);
v___x_3511_ = 1;
v_ref_3512_ = l_Lean_replaceRef(v_stx_3481_, v_ref_3500_);
lean_dec(v_stx_3481_);
lean_inc_ref(v_inheritedTraceOptions_3510_);
lean_inc(v_cancelTk_x3f_3508_);
lean_inc(v_currMacroScope_3506_);
lean_inc(v_quotContext_3505_);
lean_inc(v_maxHeartbeats_3504_);
lean_inc(v_initHeartbeats_3503_);
lean_inc(v_openDecls_3502_);
lean_inc(v_currNamespace_3501_);
lean_inc(v_maxRecDepth_3499_);
lean_inc(v_currRecDepth_3498_);
lean_inc_ref(v_options_3497_);
lean_inc_ref(v_fileMap_3496_);
lean_inc_ref(v_fileName_3495_);
v___x_3513_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3513_, 0, v_fileName_3495_);
lean_ctor_set(v___x_3513_, 1, v_fileMap_3496_);
lean_ctor_set(v___x_3513_, 2, v_options_3497_);
lean_ctor_set(v___x_3513_, 3, v_currRecDepth_3498_);
lean_ctor_set(v___x_3513_, 4, v_maxRecDepth_3499_);
lean_ctor_set(v___x_3513_, 5, v_ref_3512_);
lean_ctor_set(v___x_3513_, 6, v_currNamespace_3501_);
lean_ctor_set(v___x_3513_, 7, v_openDecls_3502_);
lean_ctor_set(v___x_3513_, 8, v_initHeartbeats_3503_);
lean_ctor_set(v___x_3513_, 9, v_maxHeartbeats_3504_);
lean_ctor_set(v___x_3513_, 10, v_quotContext_3505_);
lean_ctor_set(v___x_3513_, 11, v_currMacroScope_3506_);
lean_ctor_set(v___x_3513_, 12, v_cancelTk_x3f_3508_);
lean_ctor_set(v___x_3513_, 13, v_inheritedTraceOptions_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*14, v_diag_3507_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*14 + 1, v_suppressElabErrors_3509_);
v___x_3514_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3494_, v___x_3511_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v___x_3513_, v_a_3487_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v_a_3517_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; uint8_t v___y_3528_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; uint8_t v___x_3612_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3515_, v_a_3485_);
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref(v___x_3516_);
v___x_3612_ = l_Lean_Expr_hasSorry(v_a_3517_);
if (v___x_3612_ == 0)
{
v___y_3557_ = v_a_3482_;
v___y_3558_ = v_a_3483_;
v___y_3559_ = v_a_3484_;
v___y_3560_ = v_a_3485_;
v___y_3561_ = v___x_3513_;
v___y_3562_ = v_a_3487_;
goto v___jp_3556_;
}
else
{
uint8_t v___x_3613_; 
v___x_3613_ = l_Lean_Expr_hasSyntheticSorry(v_a_3517_);
if (v___x_3613_ == 0)
{
v___y_3594_ = v_a_3482_;
v___y_3595_ = v_a_3483_;
v___y_3596_ = v_a_3484_;
v___y_3597_ = v_a_3485_;
v___y_3598_ = v___x_3513_;
v___y_3599_ = v_a_3487_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_a_3517_);
lean_dec_ref_known(v___x_3513_, 14);
v___x_3614_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
v___jp_3518_:
{
if (v___y_3528_ == 0)
{
if (lean_obj_tag(v___y_3524_) == 0)
{
lean_dec_ref_known(v___y_3524_, 2);
lean_dec_ref(v___y_3522_);
lean_dec(v_a_3517_);
return v___y_3519_;
}
else
{
lean_object* v_id_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3542_; 
v_id_3529_ = lean_ctor_get(v___y_3524_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___y_3524_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___y_3524_, 1);
lean_dec(v_unused_3543_);
v___x_3531_ = v___y_3524_;
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_id_3529_);
lean_dec(v___y_3524_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
uint8_t v___x_3533_; 
v___x_3533_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3526_, v_id_3529_);
lean_dec(v_id_3529_);
if (v___x_3533_ == 0)
{
lean_del_object(v___x_3531_);
lean_dec_ref(v___y_3522_);
lean_dec(v_a_3517_);
return v___y_3519_;
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
lean_dec_ref(v___y_3519_);
v___x_3534_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3535_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3536_ = l_Lean_indentExpr(v_a_3517_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 7);
lean_ctor_set(v___x_3531_, 1, v___x_3536_);
lean_ctor_set(v___x_3531_, 0, v___x_3535_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v___x_3534_);
v___x_3540_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3539_, v___y_3527_, v___y_3525_, v___y_3521_, v___y_3520_, v___y_3522_, v___y_3523_);
lean_dec_ref(v___y_3522_);
return v___x_3540_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3522_);
lean_dec(v_a_3517_);
return v___y_3519_;
}
}
v___jp_3544_:
{
lean_object* v___x_3551_; 
lean_inc(v_a_3517_);
v___x_3551_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3517_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_dec_ref(v___y_3549_);
lean_dec(v_a_3517_);
return v___x_3551_;
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
v___x_3553_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3554_ = l_Lean_Exception_isInterrupt(v_a_3552_);
if (v___x_3554_ == 0)
{
uint8_t v___x_3555_; 
lean_inc(v_a_3552_);
v___x_3555_ = l_Lean_Exception_isRuntime(v_a_3552_);
v___y_3519_ = v___x_3551_;
v___y_3520_ = v___y_3548_;
v___y_3521_ = v___y_3547_;
v___y_3522_ = v___y_3549_;
v___y_3523_ = v___y_3550_;
v___y_3524_ = v_a_3552_;
v___y_3525_ = v___y_3546_;
v___y_3526_ = v___x_3553_;
v___y_3527_ = v___y_3545_;
v___y_3528_ = v___x_3555_;
goto v___jp_3518_;
}
else
{
v___y_3519_ = v___x_3551_;
v___y_3520_ = v___y_3548_;
v___y_3521_ = v___y_3547_;
v___y_3522_ = v___y_3549_;
v___y_3523_ = v___y_3550_;
v___y_3524_ = v_a_3552_;
v___y_3525_ = v___y_3546_;
v___y_3526_ = v___x_3553_;
v___y_3527_ = v___y_3545_;
v___y_3528_ = v___x_3554_;
goto v___jp_3518_;
}
}
}
v___jp_3556_:
{
lean_object* v___x_3563_; 
lean_inc(v_a_3517_);
v___x_3563_ = l_Lean_Meta_getMVars(v_a_3517_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3564_, v___x_3491_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v_a_3564_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; uint8_t v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_unbox(v_a_3566_);
lean_dec(v_a_3566_);
if (v___x_3567_ == 0)
{
v___y_3545_ = v___y_3557_;
v___y_3546_ = v___y_3558_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v___y_3560_;
v___y_3549_ = v___y_3561_;
v___y_3550_ = v___y_3562_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3568_; lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___y_3561_);
lean_dec(v_a_3517_);
v___x_3568_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___y_3561_);
lean_dec(v_a_3517_);
v_a_3577_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3565_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3565_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v___y_3561_);
lean_dec(v_a_3517_);
v_a_3585_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3563_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3563_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
v___jp_3593_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v___x_3600_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3601_ = l_Lean_indentExpr(v_a_3517_);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3602_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec_ref(v___y_3598_);
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
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
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref_known(v___x_3513_, 14);
v_a_3623_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3514_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3514_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_fileName_3648_; lean_object* v_fileMap_3649_; lean_object* v_options_3650_; lean_object* v_currRecDepth_3651_; lean_object* v_maxRecDepth_3652_; lean_object* v_ref_3653_; lean_object* v_currNamespace_3654_; lean_object* v_openDecls_3655_; lean_object* v_initHeartbeats_3656_; lean_object* v_maxHeartbeats_3657_; lean_object* v_quotContext_3658_; lean_object* v_currMacroScope_3659_; uint8_t v_diag_3660_; lean_object* v_cancelTk_x3f_3661_; uint8_t v_suppressElabErrors_3662_; lean_object* v_inheritedTraceOptions_3663_; lean_object* v_ref_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_fileName_3648_ = lean_ctor_get(v_a_3645_, 0);
v_fileMap_3649_ = lean_ctor_get(v_a_3645_, 1);
v_options_3650_ = lean_ctor_get(v_a_3645_, 2);
v_currRecDepth_3651_ = lean_ctor_get(v_a_3645_, 3);
v_maxRecDepth_3652_ = lean_ctor_get(v_a_3645_, 4);
v_ref_3653_ = lean_ctor_get(v_a_3645_, 5);
v_currNamespace_3654_ = lean_ctor_get(v_a_3645_, 6);
v_openDecls_3655_ = lean_ctor_get(v_a_3645_, 7);
v_initHeartbeats_3656_ = lean_ctor_get(v_a_3645_, 8);
v_maxHeartbeats_3657_ = lean_ctor_get(v_a_3645_, 9);
v_quotContext_3658_ = lean_ctor_get(v_a_3645_, 10);
v_currMacroScope_3659_ = lean_ctor_get(v_a_3645_, 11);
v_diag_3660_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*14);
v_cancelTk_x3f_3661_ = lean_ctor_get(v_a_3645_, 12);
v_suppressElabErrors_3662_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3663_ = lean_ctor_get(v_a_3645_, 13);
v_ref_3664_ = l_Lean_replaceRef(v_stx_3640_, v_ref_3653_);
lean_inc_ref(v_inheritedTraceOptions_3663_);
lean_inc(v_cancelTk_x3f_3661_);
lean_inc(v_currMacroScope_3659_);
lean_inc(v_quotContext_3658_);
lean_inc(v_maxHeartbeats_3657_);
lean_inc(v_initHeartbeats_3656_);
lean_inc(v_openDecls_3655_);
lean_inc(v_currNamespace_3654_);
lean_inc(v_maxRecDepth_3652_);
lean_inc(v_currRecDepth_3651_);
lean_inc_ref(v_options_3650_);
lean_inc_ref(v_fileMap_3649_);
lean_inc_ref(v_fileName_3648_);
v___x_3665_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3665_, 0, v_fileName_3648_);
lean_ctor_set(v___x_3665_, 1, v_fileMap_3649_);
lean_ctor_set(v___x_3665_, 2, v_options_3650_);
lean_ctor_set(v___x_3665_, 3, v_currRecDepth_3651_);
lean_ctor_set(v___x_3665_, 4, v_maxRecDepth_3652_);
lean_ctor_set(v___x_3665_, 5, v_ref_3664_);
lean_ctor_set(v___x_3665_, 6, v_currNamespace_3654_);
lean_ctor_set(v___x_3665_, 7, v_openDecls_3655_);
lean_ctor_set(v___x_3665_, 8, v_initHeartbeats_3656_);
lean_ctor_set(v___x_3665_, 9, v_maxHeartbeats_3657_);
lean_ctor_set(v___x_3665_, 10, v_quotContext_3658_);
lean_ctor_set(v___x_3665_, 11, v_currMacroScope_3659_);
lean_ctor_set(v___x_3665_, 12, v_cancelTk_x3f_3661_);
lean_ctor_set(v___x_3665_, 13, v_inheritedTraceOptions_3663_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*14, v_diag_3660_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*14 + 1, v_suppressElabErrors_3662_);
lean_inc(v_stx_3640_);
v___x_3666_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v___x_3665_, v_a_3646_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref_known(v___x_3665_, 14);
lean_dec(v_stx_3640_);
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_fst_3671_; lean_object* v___x_3673_; 
v_fst_3671_ = lean_ctor_get(v_a_3667_, 0);
lean_inc(v_fst_3671_);
lean_dec(v_a_3667_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_fst_3671_);
v___x_3673_ = v___x_3669_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_fst_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3691_; 
v_a_3676_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3678_ = v___x_3666_;
v_isShared_3679_ = v_isSharedCheck_3691_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3666_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3691_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3676_);
if (v_isShared_3679_ == 0)
{
v___x_3682_ = v___x_3678_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3676_);
v___x_3682_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
uint8_t v___y_3684_; uint8_t v___x_3688_; 
v___x_3688_ = l_Lean_Exception_isInterrupt(v_a_3676_);
if (v___x_3688_ == 0)
{
uint8_t v___x_3689_; 
lean_inc(v_a_3676_);
v___x_3689_ = l_Lean_Exception_isRuntime(v_a_3676_);
v___y_3684_ = v___x_3689_;
goto v___jp_3683_;
}
else
{
v___y_3684_ = v___x_3688_;
goto v___jp_3683_;
}
v___jp_3683_:
{
if (v___y_3684_ == 0)
{
if (lean_obj_tag(v_a_3676_) == 0)
{
lean_dec_ref_known(v_a_3676_, 2);
lean_dec_ref_known(v___x_3665_, 14);
lean_dec(v_stx_3640_);
return v___x_3682_;
}
else
{
lean_object* v_id_3685_; uint8_t v___x_3686_; 
v_id_3685_ = lean_ctor_get(v_a_3676_, 0);
lean_inc(v_id_3685_);
lean_dec_ref_known(v_a_3676_, 2);
v___x_3686_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3680_, v_id_3685_);
lean_dec(v_id_3685_);
if (v___x_3686_ == 0)
{
lean_dec_ref_known(v___x_3665_, 14);
lean_dec(v_stx_3640_);
return v___x_3682_;
}
else
{
lean_object* v___x_3687_; 
lean_dec_ref(v___x_3682_);
v___x_3687_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v___x_3665_, v_a_3646_);
lean_dec_ref_known(v___x_3665_, 14);
return v___x_3687_;
}
}
}
else
{
lean_dec(v_a_3676_);
lean_dec_ref_known(v___x_3665_, 14);
lean_dec(v_stx_3640_);
return v___x_3682_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3732_, lean_object* v_item_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_item_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3752_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3733_, v___x_3751_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3752_) == 0)
{
uint8_t v___x_3753_; 
lean_dec_ref_known(v___x_3752_, 1);
v___x_3753_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3733_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3754_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3733_);
lean_inc_ref(v_item_3733_);
v___x_3755_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3733_);
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3757_ = lean_string_dec_eq(v___x_3754_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3759_ = lean_string_dec_eq(v___x_3754_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3761_ = lean_string_dec_eq(v___x_3754_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3763_ = lean_string_dec_eq(v___x_3754_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3765_ = lean_string_dec_eq(v___x_3754_, v___x_3764_);
lean_dec_ref(v___x_3754_);
if (v___x_3765_ == 0)
{
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3767_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3733_, v___x_3766_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3767_) == 0)
{
uint8_t v___x_3768_; 
lean_dec_ref_known(v___x_3767_, 1);
v___x_3768_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3755_);
if (v___x_3768_ == 0)
{
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3769_; 
lean_dec_ref(v___x_3755_);
lean_inc_ref(v_item_3733_);
v___x_3769_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_value_3770_; lean_object* v___x_3771_; 
lean_dec_ref_known(v___x_3769_, 1);
v_value_3770_ = lean_ctor_get(v_item_3733_, 2);
lean_inc(v_value_3770_);
lean_dec_ref(v_item_3733_);
v___x_3771_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3770_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3790_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3774_ = v___x_3771_;
v_isShared_3775_ = v_isSharedCheck_3790_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3790_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
uint8_t v_offsetCnstrs_3776_; lean_object* v_occs_3777_; uint8_t v_newGoals_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3789_; 
v_offsetCnstrs_3776_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 1);
v_occs_3777_ = lean_ctor_get(v_config_3732_, 0);
v_newGoals_3778_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 2);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_config_3732_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3780_ = v_config_3732_;
v_isShared_3781_ = v_isSharedCheck_3789_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_occs_3777_);
lean_dec(v_config_3732_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3789_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_occs_3777_);
v___x_3783_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
uint8_t v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_unbox(v_a_3772_);
lean_dec(v_a_3772_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*1, v___x_3784_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*1 + 1, v_offsetCnstrs_3776_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*1 + 2, v_newGoals_3778_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3783_);
v___x_3786_ = v___x_3774_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3783_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v_config_3732_);
v_a_3791_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3771_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3771_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3799_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3769_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3769_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v___x_3755_);
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3807_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3767_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3767_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec_ref(v___x_3754_);
v___x_3815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_3816_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3733_, v___x_3815_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3816_) == 0)
{
uint8_t v___x_3817_; 
lean_dec_ref_known(v___x_3816_, 1);
v___x_3817_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3755_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3818_; 
lean_dec_ref(v___x_3755_);
v___x_3818_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3837_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3821_ = v___x_3818_;
v_isShared_3822_ = v_isSharedCheck_3837_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3837_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
uint8_t v_transparency_3823_; lean_object* v_occs_3824_; uint8_t v_newGoals_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3836_; 
v_transparency_3823_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1);
v_occs_3824_ = lean_ctor_get(v_config_3732_, 0);
v_newGoals_3825_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 2);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_config_3732_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3827_ = v_config_3732_;
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_occs_3824_);
lean_dec(v_config_3732_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_occs_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3835_, sizeof(void*)*1, v_transparency_3823_);
v___x_3830_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
uint8_t v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = lean_unbox(v_a_3819_);
lean_dec(v_a_3819_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*1 + 1, v___x_3831_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*1 + 2, v_newGoals_3825_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3830_);
v___x_3833_ = v___x_3821_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3830_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_config_3732_);
v_a_3838_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3818_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3818_);
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
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v___x_3755_);
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3846_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3816_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3816_);
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
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec_ref(v___x_3754_);
v___x_3854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_3855_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3733_, v___x_3854_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3855_) == 0)
{
uint8_t v___x_3856_; 
lean_dec_ref_known(v___x_3855_, 1);
v___x_3856_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3755_);
if (v___x_3856_ == 0)
{
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3857_; 
lean_dec_ref(v___x_3755_);
lean_inc_ref(v_item_3733_);
v___x_3857_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_value_3858_; lean_object* v___x_3859_; 
lean_dec_ref_known(v___x_3857_, 1);
v_value_3858_ = lean_ctor_get(v_item_3733_, 2);
lean_inc(v_value_3858_);
lean_dec_ref(v_item_3733_);
v___x_3859_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_3858_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3878_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3878_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3878_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
uint8_t v_transparency_3864_; uint8_t v_offsetCnstrs_3865_; uint8_t v_newGoals_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3876_; 
v_transparency_3864_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1);
v_offsetCnstrs_3865_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 1);
v_newGoals_3866_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 2);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_config_3732_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v_config_3732_, 0);
lean_dec(v_unused_3877_);
v___x_3868_ = v_config_3732_;
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
else
{
lean_dec(v_config_3732_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3876_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v_a_3860_);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3860_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*1, v_transparency_3864_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*1 + 1, v_offsetCnstrs_3865_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*1 + 2, v_newGoals_3866_);
v___x_3871_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3873_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3871_);
v___x_3873_ = v___x_3862_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_config_3732_);
v_a_3879_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3859_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3859_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3887_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3857_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3857_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec_ref(v___x_3755_);
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3895_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3855_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3855_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec_ref(v___x_3754_);
v___x_3903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_3904_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3733_, v___x_3903_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3904_) == 0)
{
uint8_t v___x_3905_; 
lean_dec_ref_known(v___x_3904_, 1);
v___x_3905_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3755_);
if (v___x_3905_ == 0)
{
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3906_; 
lean_dec_ref(v___x_3755_);
lean_inc_ref(v_item_3733_);
v___x_3906_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_value_3907_; lean_object* v___x_3908_; 
lean_dec_ref_known(v___x_3906_, 1);
v_value_3907_ = lean_ctor_get(v_item_3733_, 2);
lean_inc(v_value_3907_);
lean_dec_ref(v_item_3733_);
v___x_3908_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_3907_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3927_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3927_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3927_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
uint8_t v_transparency_3913_; uint8_t v_offsetCnstrs_3914_; lean_object* v_occs_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3926_; 
v_transparency_3913_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1);
v_offsetCnstrs_3914_ = lean_ctor_get_uint8(v_config_3732_, sizeof(void*)*1 + 1);
v_occs_3915_ = lean_ctor_get(v_config_3732_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_config_3732_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3917_ = v_config_3732_;
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_occs_3915_);
lean_dec(v_config_3732_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_occs_3915_);
lean_ctor_set_uint8(v_reuseFailAlloc_3925_, sizeof(void*)*1, v_transparency_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3925_, sizeof(void*)*1 + 1, v_offsetCnstrs_3914_);
v___x_3920_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
uint8_t v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = lean_unbox(v_a_3909_);
lean_dec(v_a_3909_);
lean_ctor_set_uint8(v___x_3920_, sizeof(void*)*1 + 2, v___x_3921_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3920_);
v___x_3923_ = v___x_3911_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3920_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v_config_3732_);
v_a_3928_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3908_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3908_);
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
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3936_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3906_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3906_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v___x_3755_);
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3944_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3904_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3904_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
else
{
uint8_t v___x_3952_; 
lean_dec_ref(v___x_3754_);
lean_dec_ref(v_config_3732_);
v___x_3952_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3755_);
if (v___x_3952_ == 0)
{
lean_dec_ref(v_item_3733_);
v_item_3742_ = v___x_3755_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
else
{
lean_object* v_value_3953_; lean_object* v___x_3954_; 
lean_dec_ref(v___x_3755_);
v_value_3953_ = lean_ctor_get(v_item_3733_, 2);
lean_inc(v_value_3953_);
lean_dec_ref(v_item_3733_);
v___x_3954_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_3953_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3954_;
}
}
}
else
{
lean_dec_ref(v_config_3732_);
v_item_3742_ = v_item_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
v___y_3747_ = v___y_3738_;
v___y_3748_ = v___y_3739_;
goto v___jp_3741_;
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_item_3733_);
lean_dec_ref(v_config_3732_);
v_a_3955_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3752_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3752_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
v___jp_3741_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3750_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3742_, v___x_3749_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3963_, lean_object* v_item_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_3963_, v_item_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_3975_, v___y_3979_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4011_, lean_object* v_msg_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4021_, lean_object* v_msg_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4021_, v_msg_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4031_, lean_object* v_macroStack_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4031_, v_macroStack_4032_, v___y_4037_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4041_, lean_object* v_macroStack_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4041_, v_macroStack_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4050_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = lean_box(0);
v___x_4052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4053_ = l_Lean_mkConst(v___x_4052_, v___x_4051_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4056_, lean_object* v_cfgItem_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4066_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4056_, v_cfgItem_4057_, v___x_4065_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4067_, lean_object* v_cfgItem_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4067_, v_cfgItem_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v_cfgItem_4068_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4078_, lean_object* v_init_4079_, uint8_t v_logExceptions_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_onErr_4085_; lean_object* v_eval_4086_; 
v_onErr_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4080_ == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4086_, v_init_4079_, v_cfg_4078_, v_onErr_4085_, v_logExceptions_4080_, v_a_4082_, v_a_4083_);
return v___x_4087_;
}
else
{
uint8_t v_recover_4088_; lean_object* v___x_4089_; 
v_recover_4088_ = lean_ctor_get_uint8(v_a_4081_, sizeof(void*)*1);
v___x_4089_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4086_, v_init_4079_, v_cfg_4078_, v_onErr_4085_, v_recover_4088_, v_a_4082_, v_a_4083_);
return v___x_4089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4090_, lean_object* v_init_4091_, lean_object* v_logExceptions_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
uint8_t v_logExceptions_boxed_4097_; lean_object* v_res_4098_; 
v_logExceptions_boxed_4097_ = lean_unbox(v_logExceptions_4092_);
v_res_4098_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4090_, v_init_4091_, v_logExceptions_boxed_4097_, v_a_4093_, v_a_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec_ref(v_a_4093_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4099_, lean_object* v_init_4100_, uint8_t v_logExceptions_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4099_, v_init_4100_, v_logExceptions_4101_, v_a_4102_, v_a_4108_, v_a_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4112_, lean_object* v_init_4113_, lean_object* v_logExceptions_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
uint8_t v_logExceptions_boxed_4124_; lean_object* v_res_4125_; 
v_logExceptions_boxed_4124_ = lean_unbox(v_logExceptions_4114_);
v_res_4125_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4112_, v_init_4113_, v_logExceptions_boxed_4124_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_a_4116_);
lean_dec_ref(v_a_4115_);
return v_res_4125_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4133_ = l_Lean_MessageData_ofFormat(v___x_4132_);
return v___x_4133_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4147_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4148_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4146_, v_x_4136_, v___x_4147_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4160_, uint8_t v_symm_4161_, lean_object* v_a_4162_, lean_object* v_x_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4160_, v_symm_4161_, v_x_4163_, v_a_4162_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4174_, lean_object* v_symm_4175_, lean_object* v_a_4176_, lean_object* v_x_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v_symm_boxed_4187_; lean_object* v_res_4188_; 
v_symm_boxed_4187_ = lean_unbox(v_symm_4175_);
v_res_4188_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4174_, v_symm_boxed_4187_, v_a_4176_, v_x_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4189_, lean_object* v___x_4190_, lean_object* v___f_4191_, uint8_t v_symm_4192_, lean_object* v_term_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4203_ = lean_box(v_symm_4192_);
lean_inc_ref(v_a_4189_);
lean_inc(v_term_4193_);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4204_, 0, v_term_4193_);
lean_closure_set(v___f_4204_, 1, v___x_4203_);
lean_closure_set(v___f_4204_, 2, v_a_4189_);
v___x_4205_ = lean_box(v_symm_4192_);
v___x_4206_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4206_, 0, v_term_4193_);
lean_closure_set(v___x_4206_, 1, v___x_4205_);
lean_closure_set(v___x_4206_, 2, v_a_4189_);
v___x_4207_ = l_Lean_Elab_Tactic_withLocation(v___x_4190_, v___f_4204_, v___x_4206_, v___f_4191_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4208_, lean_object* v___x_4209_, lean_object* v___f_4210_, lean_object* v_symm_4211_, lean_object* v_term_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
uint8_t v_symm_boxed_4222_; lean_object* v_res_4223_; 
v_symm_boxed_4222_ = lean_unbox(v_symm_4211_);
v_res_4223_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4208_, v___x_4209_, v___f_4210_, v_symm_boxed_4222_, v_term_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___x_4209_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4240_ = lean_unsigned_to_nat(1u);
v___x_4241_ = l_Lean_Syntax_getArg(v_stx_4230_, v___x_4240_);
v___x_4242_ = 1;
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4244_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4241_, v___x_4243_, v___x_4242_, v_a_4231_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___f_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___f_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___f_4246_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4247_ = lean_unsigned_to_nat(3u);
v___x_4248_ = l_Lean_Syntax_getArg(v_stx_4230_, v___x_4247_);
v___x_4249_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4248_);
lean_dec(v___x_4248_);
v___f_4250_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4250_, 0, v_a_4245_);
lean_closure_set(v___f_4250_, 1, v___x_4249_);
lean_closure_set(v___f_4250_, 2, v___f_4246_);
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = l_Lean_Syntax_getArg(v_stx_4230_, v___x_4251_);
v___x_4253_ = lean_unsigned_to_nat(2u);
v___x_4254_ = l_Lean_Syntax_getArg(v_stx_4230_, v___x_4253_);
v___x_4255_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4252_, v___x_4254_, v___f_4250_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec(v___x_4254_);
return v___x_4255_;
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4244_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4244_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_stx_4264_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4290_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4293_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4294_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4290_, v___x_4291_, v___x_4292_, v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4325_ = l_Lean_addBuiltinDeclarationRanges(v___x_4323_, v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4327_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
