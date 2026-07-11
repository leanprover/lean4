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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Syntax_isNone(lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
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
uint8_t v___x_12856__boxed_70_; lean_object* v_res_71_; 
v___x_12856__boxed_70_ = lean_unbox(v___x_64_);
v_res_71_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_63_, v___x_12856__boxed_70_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
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
lean_object* v_d_374_; lean_object* v_b_375_; lean_object* v___y_376_; uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = l_Lean_Expr_hasExprMVar(v_e_362_);
v___x_383_ = lean_bool_not(v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_363_, v_e_362_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_box(0);
lean_inc_ref(v_e_362_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_363_, v_e_362_, v___x_385_);
switch(lean_obj_tag(v_e_362_))
{
case 11:
{
lean_object* v_struct_387_; 
v_struct_387_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_struct_387_);
lean_dec_ref_known(v_e_362_, 3);
v_e_362_ = v_struct_387_;
v_a_363_ = v___x_386_;
goto _start;
}
case 7:
{
lean_object* v_binderType_389_; lean_object* v_body_390_; 
v_binderType_389_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_binderType_389_);
v_body_390_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_390_);
lean_dec_ref_known(v_e_362_, 3);
v_d_374_ = v_binderType_389_;
v_b_375_ = v_body_390_;
v___y_376_ = v___x_386_;
goto v___jp_373_;
}
case 6:
{
lean_object* v_binderType_391_; lean_object* v_body_392_; 
v_binderType_391_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_binderType_391_);
v_body_392_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_392_);
lean_dec_ref_known(v_e_362_, 3);
v_d_374_ = v_binderType_391_;
v_b_375_ = v_body_392_;
v___y_376_ = v___x_386_;
goto v___jp_373_;
}
case 8:
{
lean_object* v_type_393_; lean_object* v_value_394_; lean_object* v_body_395_; lean_object* v___x_396_; 
v_type_393_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_type_393_);
v_value_394_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_value_394_);
v_body_395_ = lean_ctor_get(v_e_362_, 3);
lean_inc_ref(v_body_395_);
lean_dec_ref_known(v_e_362_, 4);
v___x_396_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_type_393_, v___x_386_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_fst_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
v_fst_398_ = lean_ctor_get(v_a_397_, 0);
if (lean_obj_tag(v_fst_398_) == 0)
{
lean_dec(v_a_397_);
lean_dec_ref(v_body_395_);
lean_dec_ref(v_value_394_);
return v___x_396_;
}
else
{
lean_object* v_snd_399_; lean_object* v___x_400_; 
lean_dec_ref_known(v___x_396_, 1);
v_snd_399_ = lean_ctor_get(v_a_397_, 1);
lean_inc(v_snd_399_);
lean_dec(v_a_397_);
v___x_400_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_value_394_, v_snd_399_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_fst_402_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
v_fst_402_ = lean_ctor_get(v_a_401_, 0);
if (lean_obj_tag(v_fst_402_) == 0)
{
lean_dec(v_a_401_);
lean_dec_ref(v_body_395_);
return v___x_400_;
}
else
{
lean_object* v_snd_403_; 
lean_dec_ref_known(v___x_400_, 1);
v_snd_403_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_snd_403_);
lean_dec(v_a_401_);
v_e_362_ = v_body_395_;
v_a_363_ = v_snd_403_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_395_);
return v___x_400_;
}
}
}
else
{
lean_dec_ref(v_body_395_);
lean_dec_ref(v_value_394_);
return v___x_396_;
}
}
case 10:
{
lean_object* v_expr_405_; 
v_expr_405_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_expr_405_);
lean_dec_ref_known(v_e_362_, 2);
v_e_362_ = v_expr_405_;
v_a_363_ = v___x_386_;
goto _start;
}
case 5:
{
lean_object* v_fn_407_; lean_object* v_arg_408_; lean_object* v___x_409_; 
v_fn_407_ = lean_ctor_get(v_e_362_, 0);
lean_inc_ref(v_fn_407_);
v_arg_408_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_arg_408_);
lean_dec_ref_known(v_e_362_, 2);
v___x_409_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_361_, v_fn_407_, v___x_386_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v_fst_411_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
v_fst_411_ = lean_ctor_get(v_a_410_, 0);
if (lean_obj_tag(v_fst_411_) == 0)
{
lean_dec(v_a_410_);
lean_dec_ref(v_arg_408_);
return v___x_409_;
}
else
{
lean_object* v_snd_412_; 
lean_dec_ref_known(v___x_409_, 1);
v_snd_412_ = lean_ctor_get(v_a_410_, 1);
lean_inc(v_snd_412_);
lean_dec(v_a_410_);
v_e_362_ = v_arg_408_;
v_a_363_ = v_snd_412_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_408_);
return v___x_409_;
}
}
case 2:
{
lean_object* v_mvarId_414_; lean_object* v___x_415_; 
v_mvarId_414_ = lean_ctor_get(v_e_362_, 0);
lean_inc(v_mvarId_414_);
lean_dec_ref_known(v_e_362_, 1);
v___x_415_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_361_, v_mvarId_414_, v___x_386_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_415_;
}
default: 
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_e_362_);
v___x_416_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_386_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_e_362_);
v___x_419_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_a_363_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_e_362_);
v___x_422_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_363_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
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
uint8_t v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_577_ = l_Lean_Expr_hasExprMVar(v_e_567_);
v___x_578_ = lean_bool_not(v___x_577_);
v___x_579_ = 1;
if (v___x_578_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
v___x_581_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_566_, v_e_567_, v___x_580_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_595_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_595_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_595_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_595_;
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
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec_ref_known(v_fst_586_, 1);
v___x_587_ = lean_box(v___x_578_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec_ref_known(v_fst_586_, 1);
v___x_591_ = lean_box(v___x_579_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_591_);
v___x_593_ = v___x_584_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_581_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_581_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref(v_e_567_);
v___x_604_ = lean_box(v___x_579_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
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
lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_mctx_651_; lean_object* v_lctx_652_; lean_object* v_options_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_648_ = lean_st_ref_get(v___y_646_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = lean_st_ref_get(v___y_644_);
v_mctx_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_mctx_651_);
lean_dec(v___x_650_);
v_lctx_652_ = lean_ctor_get(v___y_643_, 2);
v_options_653_ = lean_ctor_get(v___y_645_, 2);
lean_inc_ref(v_options_653_);
lean_inc_ref(v_lctx_652_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_649_);
lean_ctor_set(v___x_654_, 1, v_mctx_651_);
lean_ctor_set(v___x_654_, 2, v_lctx_652_);
lean_ctor_set(v___x_654_, 3, v_options_653_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_642_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object* v_msgData_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_ref_670_ = lean_ctor_get(v___y_667_, 5);
v___x_671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_ref_670_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_ref_670_);
lean_ctor_set(v___x_676_, 1, v_a_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 1);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object* v_ref_688_, lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_fileName_699_; lean_object* v_fileMap_700_; lean_object* v_options_701_; lean_object* v_currRecDepth_702_; lean_object* v_maxRecDepth_703_; lean_object* v_ref_704_; lean_object* v_currNamespace_705_; lean_object* v_openDecls_706_; lean_object* v_initHeartbeats_707_; lean_object* v_maxHeartbeats_708_; lean_object* v_quotContext_709_; lean_object* v_currMacroScope_710_; uint8_t v_diag_711_; lean_object* v_cancelTk_x3f_712_; uint8_t v_suppressElabErrors_713_; lean_object* v_inheritedTraceOptions_714_; lean_object* v_ref_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_fileName_699_ = lean_ctor_get(v___y_696_, 0);
v_fileMap_700_ = lean_ctor_get(v___y_696_, 1);
v_options_701_ = lean_ctor_get(v___y_696_, 2);
v_currRecDepth_702_ = lean_ctor_get(v___y_696_, 3);
v_maxRecDepth_703_ = lean_ctor_get(v___y_696_, 4);
v_ref_704_ = lean_ctor_get(v___y_696_, 5);
v_currNamespace_705_ = lean_ctor_get(v___y_696_, 6);
v_openDecls_706_ = lean_ctor_get(v___y_696_, 7);
v_initHeartbeats_707_ = lean_ctor_get(v___y_696_, 8);
v_maxHeartbeats_708_ = lean_ctor_get(v___y_696_, 9);
v_quotContext_709_ = lean_ctor_get(v___y_696_, 10);
v_currMacroScope_710_ = lean_ctor_get(v___y_696_, 11);
v_diag_711_ = lean_ctor_get_uint8(v___y_696_, sizeof(void*)*14);
v_cancelTk_x3f_712_ = lean_ctor_get(v___y_696_, 12);
v_suppressElabErrors_713_ = lean_ctor_get_uint8(v___y_696_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_714_ = lean_ctor_get(v___y_696_, 13);
v_ref_715_ = l_Lean_replaceRef(v_ref_688_, v_ref_704_);
lean_inc_ref(v_inheritedTraceOptions_714_);
lean_inc(v_cancelTk_x3f_712_);
lean_inc(v_currMacroScope_710_);
lean_inc(v_quotContext_709_);
lean_inc(v_maxHeartbeats_708_);
lean_inc(v_initHeartbeats_707_);
lean_inc(v_openDecls_706_);
lean_inc(v_currNamespace_705_);
lean_inc(v_maxRecDepth_703_);
lean_inc(v_currRecDepth_702_);
lean_inc_ref(v_options_701_);
lean_inc_ref(v_fileMap_700_);
lean_inc_ref(v_fileName_699_);
v___x_716_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_716_, 0, v_fileName_699_);
lean_ctor_set(v___x_716_, 1, v_fileMap_700_);
lean_ctor_set(v___x_716_, 2, v_options_701_);
lean_ctor_set(v___x_716_, 3, v_currRecDepth_702_);
lean_ctor_set(v___x_716_, 4, v_maxRecDepth_703_);
lean_ctor_set(v___x_716_, 5, v_ref_715_);
lean_ctor_set(v___x_716_, 6, v_currNamespace_705_);
lean_ctor_set(v___x_716_, 7, v_openDecls_706_);
lean_ctor_set(v___x_716_, 8, v_initHeartbeats_707_);
lean_ctor_set(v___x_716_, 9, v_maxHeartbeats_708_);
lean_ctor_set(v___x_716_, 10, v_quotContext_709_);
lean_ctor_set(v___x_716_, 11, v_currMacroScope_710_);
lean_ctor_set(v___x_716_, 12, v_cancelTk_x3f_712_);
lean_ctor_set(v___x_716_, 13, v_inheritedTraceOptions_714_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*14, v_diag_711_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*14 + 1, v_suppressElabErrors_713_);
v___x_717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_689_, v___y_694_, v___y_695_, v___x_716_, v___y_697_);
lean_dec_ref_known(v___x_716_, 14);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_718_, v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_ref_718_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_732_ = l_Lean_stringToMessageData(v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_736_, lean_object* v_e_737_, lean_object* v_stx_738_, uint8_t v_symm_739_, lean_object* v_config_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_st_ref_get(v_a_746_);
v___x_751_ = lean_box(0);
v___x_752_ = 1;
lean_inc(v_stx_738_);
v___x_753_ = l_Lean_Elab_Tactic_elabTerm(v_stx_738_, v___x_751_, v___x_752_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_mctx_754_; lean_object* v_a_755_; lean_object* v_mvarCounter_756_; lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___x_828_; 
v_mctx_754_ = lean_ctor_get(v___x_750_, 0);
lean_inc_ref(v_mctx_754_);
lean_dec(v___x_750_);
v_a_755_ = lean_ctor_get(v___x_753_, 0);
lean_inc_n(v_a_755_, 2);
lean_dec_ref_known(v___x_753_, 1);
v_mvarCounter_756_ = lean_ctor_get(v_mctx_754_, 3);
lean_inc(v_mvarCounter_756_);
lean_dec_ref(v_mctx_754_);
v___x_757_ = lean_box(v_symm_739_);
lean_inc_ref(v_e_737_);
lean_inc(v_mvarId_736_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_758_, 0, v_mvarId_736_);
lean_closure_set(v___f_758_, 1, v_e_737_);
lean_closure_set(v___f_758_, 2, v_a_755_);
lean_closure_set(v___f_758_, 3, v___x_757_);
lean_closure_set(v___f_758_, 4, v_config_740_);
v___x_828_ = l_Lean_Expr_hasSyntheticSorry(v_a_755_);
if (v___x_828_ == 0)
{
v___y_792_ = v_a_741_;
v___y_793_ = v_a_742_;
v___y_794_ = v_a_743_;
v___y_795_ = v_a_744_;
v___y_796_ = v_a_745_;
v___y_797_ = v_a_746_;
v___y_798_ = v_a_747_;
v___y_799_ = v_a_748_;
goto v___jp_791_;
}
else
{
lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___f_758_);
lean_dec(v_mvarCounter_756_);
lean_dec(v_a_755_);
lean_dec(v_stx_738_);
lean_dec_ref(v_e_737_);
lean_dec(v_mvarId_736_);
v___x_829_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
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
v___jp_759_:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_737_, v___f_758_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_790_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_790_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_790_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_790_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v_mctx_774_; lean_object* v_eNew_775_; lean_object* v_eqProof_776_; lean_object* v_mvarIds_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_789_; 
v___x_773_ = lean_st_ref_get(v___y_765_);
v_mctx_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc_ref(v_mctx_774_);
lean_dec(v___x_773_);
v_eNew_775_ = lean_ctor_get(v_a_769_, 0);
v_eqProof_776_ = lean_ctor_get(v_a_769_, 1);
v_mvarIds_777_ = lean_ctor_get(v_a_769_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_769_);
if (v_isSharedCheck_789_ == 0)
{
v___x_779_ = v_a_769_;
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_mvarIds_777_);
lean_inc(v_eqProof_776_);
lean_inc(v_eNew_775_);
lean_dec(v_a_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = lean_box(0);
v___x_782_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_774_, v_mvarCounter_756_, v_mvarIds_777_, v___x_781_);
lean_dec(v_mvarCounter_756_);
lean_dec_ref(v_mctx_774_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 2, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_eNew_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_eqProof_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v___x_782_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_784_);
v___x_786_ = v___x_771_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_756_);
return v___x_768_;
}
}
v___jp_791_:
{
lean_object* v___x_800_; 
lean_inc(v_a_755_);
v___x_800_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_736_, v_a_755_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; uint8_t v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v___f_758_);
lean_dec(v_mvarCounter_756_);
lean_dec_ref(v_e_737_);
v___x_803_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_804_ = l_Lean_indentExpr(v_a_755_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_Expr_mvar___override(v_mvarId_736_);
v___x_809_ = l_Lean_MessageData_ofExpr(v___x_808_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_807_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_738_, v___x_810_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v_stx_738_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_dec(v_a_755_);
lean_dec(v_stx_738_);
lean_dec(v_mvarId_736_);
v___y_760_ = v___y_792_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
v___y_763_ = v___y_795_;
v___y_764_ = v___y_796_;
v___y_765_ = v___y_797_;
v___y_766_ = v___y_798_;
v___y_767_ = v___y_799_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v___f_758_);
lean_dec(v_mvarCounter_756_);
lean_dec(v_a_755_);
lean_dec(v_stx_738_);
lean_dec_ref(v_e_737_);
lean_dec(v_mvarId_736_);
v_a_820_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_800_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_800_);
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
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v___x_750_);
lean_dec_ref(v_config_740_);
lean_dec(v_stx_738_);
lean_dec_ref(v_e_737_);
lean_dec(v_mvarId_736_);
v_a_838_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_753_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_753_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_846_, lean_object* v_e_847_, lean_object* v_stx_848_, lean_object* v_symm_849_, lean_object* v_config_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v_symm_boxed_860_; lean_object* v_res_861_; 
v_symm_boxed_860_ = lean_unbox(v_symm_849_);
v_res_861_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_846_, v_e_847_, v_stx_848_, v_symm_boxed_860_, v_config_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_862_, lean_object* v_ref_863_, lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_863_, v_msg_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_875_, lean_object* v_ref_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_875_, v_ref_876_, v_msg_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_ref_876_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_889_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_900_, v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_912_, lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_913_, v_a_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_916_, lean_object* v_m_917_, lean_object* v_a_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_916_, v_m_917_, v_a_918_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_m_917_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_921_, lean_object* v_m_922_, lean_object* v_a_923_, lean_object* v_b_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_922_, v_a_923_, v_b_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_926_, v___y_927_, v___y_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v_mvarId_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_950_, v___y_951_, v___y_957_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_mvarId_962_);
return v_res_973_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_974_, lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_975_, v_x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_978_, lean_object* v_a_979_, lean_object* v_x_980_){
_start:
{
uint8_t v_res_981_; lean_object* v_r_982_; 
v_res_981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_978_, v_a_979_, v_x_980_);
lean_dec(v_x_980_);
lean_dec_ref(v_a_979_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_983_, lean_object* v_data_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_986_, lean_object* v_i_987_, lean_object* v_source_988_, lean_object* v_target_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_987_, v_source_988_, v_target_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1019_, v_x_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1027_, lean_object* v_mvarId_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1028_, v_x_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_mvarId_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1036_, v_mvarId_1037_, v_x_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_keys_1045_);
v___x_1049_ = lean_nat_dec_lt(v_i_1046_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec(v_i_1046_);
return v___x_1049_;
}
else
{
lean_object* v_k_x27_1050_; uint8_t v___x_1051_; 
v_k_x27_1050_ = lean_array_fget_borrowed(v_keys_1045_, v_i_1046_);
v___x_1051_ = l_Lean_instBEqMVarId_beq(v_k_1047_, v_k_x27_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_i_1046_, v___x_1052_);
lean_dec(v_i_1046_);
v_i_1046_ = v___x_1053_;
goto _start;
}
else
{
lean_dec(v_i_1046_);
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1055_, lean_object* v_i_1056_, lean_object* v_k_1057_){
_start:
{
uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_res_1058_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1055_, v_i_1056_, v_k_1057_);
lean_dec(v_k_1057_);
lean_dec_ref(v_keys_1055_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1060_, size_t v_x_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
lean_object* v_es_1063_; lean_object* v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v_j_1067_; lean_object* v___x_1068_; 
v_es_1063_ = lean_ctor_get(v_x_1060_, 0);
v___x_1064_ = lean_box(2);
v___x_1065_ = ((size_t)31ULL);
v___x_1066_ = lean_usize_land(v_x_1061_, v___x_1065_);
v_j_1067_ = lean_usize_to_nat(v___x_1066_);
v___x_1068_ = lean_array_get_borrowed(v___x_1064_, v_es_1063_, v_j_1067_);
lean_dec(v_j_1067_);
switch(lean_obj_tag(v___x_1068_))
{
case 0:
{
lean_object* v_key_1069_; uint8_t v___x_1070_; 
v_key_1069_ = lean_ctor_get(v___x_1068_, 0);
v___x_1070_ = l_Lean_instBEqMVarId_beq(v_x_1062_, v_key_1069_);
return v___x_1070_;
}
case 1:
{
lean_object* v_node_1071_; size_t v___x_1072_; size_t v___x_1073_; 
v_node_1071_ = lean_ctor_get(v___x_1068_, 0);
v___x_1072_ = ((size_t)5ULL);
v___x_1073_ = lean_usize_shift_right(v_x_1061_, v___x_1072_);
v_x_1060_ = v_node_1071_;
v_x_1061_ = v___x_1073_;
goto _start;
}
default: 
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
return v___x_1075_;
}
}
}
else
{
lean_object* v_ks_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_ks_1076_ = lean_ctor_get(v_x_1060_, 0);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1076_, v___x_1077_, v_x_1062_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
size_t v_x_1931__boxed_1082_; uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_x_1931__boxed_1082_ = lean_unbox_usize(v_x_1080_);
lean_dec(v_x_1080_);
v_res_1083_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1079_, v_x_1931__boxed_1082_, v_x_1081_);
lean_dec(v_x_1081_);
lean_dec_ref(v_x_1079_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
uint64_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = l_Lean_instHashableMVarId_hash(v_x_1086_);
v___x_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1085_, v___x_1088_, v_x_1086_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1090_, v_x_1091_);
lean_dec(v_x_1091_);
lean_dec_ref(v_x_1090_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v_mctx_1098_; lean_object* v_eAssignment_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1097_ = lean_st_ref_get(v___y_1095_);
v_mctx_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_mctx_1098_);
lean_dec(v___x_1097_);
v_eAssignment_1099_ = lean_ctor_get(v_mctx_1098_, 8);
lean_inc_ref(v_eAssignment_1099_);
lean_dec_ref(v_mctx_1098_);
v___x_1100_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1099_, v_mvarId_1094_);
lean_dec_ref(v_eAssignment_1099_);
v___x_1101_ = lean_box(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec(v_mvarId_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_x_1108_);
return v___x_1114_;
}
else
{
lean_object* v_head_1115_; lean_object* v_tail_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1131_; 
v_head_1115_ = lean_ctor_get(v_x_1107_, 0);
v_tail_1116_ = lean_ctor_get(v_x_1107_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1118_ = v_x_1107_;
v_isShared_1119_ = v_isSharedCheck_1131_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_tail_1116_);
lean_inc(v_head_1115_);
lean_dec(v_x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1131_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
uint8_t v_a_1121_; lean_object* v___x_1127_; lean_object* v_a_1128_; uint8_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1115_, v___y_1110_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
v___x_1130_ = lean_bool_not(v___x_1129_);
v_a_1121_ = v___x_1130_;
goto v___jp_1120_;
v___jp_1120_:
{
if (v_a_1121_ == 0)
{
lean_del_object(v___x_1118_);
lean_dec(v_head_1115_);
v_x_1107_ = v_tail_1116_;
goto _start;
}
else
{
lean_object* v___x_1124_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_x_1108_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_head_1115_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_x_1108_);
v___x_1124_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_x_1107_ = v_tail_1116_;
v_x_1108_ = v___x_1124_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1132_, v_x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
lean_inc(v_head_1140_);
v___x_1146_ = l_Lean_MVarId_getType(v_head_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = l_Lean_Meta_isProp(v_a_1147_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1160_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec(v_head_1140_);
v___x_1154_ = lean_box(0);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
uint8_t v___x_1158_; lean_object* v___x_1159_; 
lean_del_object(v___x_1151_);
v___x_1158_ = 2;
v___x_1159_ = l_Lean_MVarId_setKind___redArg(v_head_1140_, v___x_1158_, v___y_1142_);
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_head_1140_);
v_a_1161_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1148_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_head_1140_);
v_a_1169_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1146_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1146_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
if (lean_obj_tag(v_as_1184_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v_head_1192_; lean_object* v_tail_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v_head_1192_ = lean_ctor_get(v_as_1184_, 0);
lean_inc_n(v_head_1192_, 2);
v_tail_1193_ = lean_ctor_get(v_as_1184_, 1);
lean_inc(v_tail_1193_);
lean_dec_ref_known(v_as_1184_, 2);
v___f_1194_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1194_, 0, v_head_1192_);
v___x_1195_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1192_, v___f_1194_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec_ref_known(v___x_1195_, 1);
v_as_1184_ = v_tail_1193_;
goto _start;
}
else
{
lean_dec(v_tail_1193_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_eNew_1210_; lean_object* v_eqProof_1211_; lean_object* v_mvarIds_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1251_; 
v_eNew_1210_ = lean_ctor_get(v_r_1204_, 0);
v_eqProof_1211_ = lean_ctor_get(v_r_1204_, 1);
v_mvarIds_1212_ = lean_ctor_get(v_r_1204_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_r_1204_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1214_ = v_r_1204_;
v_isShared_1215_ = v_isSharedCheck_1251_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_mvarIds_1212_);
lean_inc(v_eqProof_1211_);
lean_inc(v_eNew_1210_);
lean_dec(v_r_1204_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1251_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_a_1217_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1212_, v___x_1238_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_List_reverse___redArg(v_a_1240_);
v_a_1217_ = v___x_1241_;
goto v___jp_1216_;
}
else
{
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1242_; 
v_a_1242_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1239_, 1);
v_a_1217_ = v_a_1242_;
goto v___jp_1216_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_del_object(v___x_1214_);
lean_dec_ref(v_eqProof_1211_);
lean_dec_ref(v_eNew_1210_);
v_a_1243_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1239_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
v___jp_1216_:
{
lean_object* v___x_1218_; 
lean_inc(v_a_1217_);
v___x_1218_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1217_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1228_; 
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1229_);
v___x_1220_ = v___x_1218_;
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1218_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 2, v_a_1217_);
v___x_1223_ = v___x_1214_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_eNew_1210_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_eqProof_1211_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_a_1217_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1223_);
v___x_1225_ = v___x_1220_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_a_1217_);
lean_del_object(v___x_1214_);
lean_dec_ref(v_eqProof_1211_);
lean_dec_ref(v_eNew_1210_);
v_a_1230_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1218_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1218_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1259_, v___y_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v_mvarId_1266_);
return v_res_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1274_, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1277_, v_x_1278_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec_ref(v_x_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1282_, lean_object* v_x_1283_, size_t v_x_1284_, lean_object* v_x_1285_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1283_, v_x_1284_, v_x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
size_t v_x_2274__boxed_1291_; uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_x_2274__boxed_1291_ = lean_unbox_usize(v_x_1289_);
lean_dec(v_x_1289_);
v_res_1292_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1287_, v_x_1288_, v_x_2274__boxed_1291_, v_x_1290_);
lean_dec(v_x_1290_);
lean_dec_ref(v_x_1288_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1294_, lean_object* v_keys_1295_, lean_object* v_vals_1296_, lean_object* v_heq_1297_, lean_object* v_i_1298_, lean_object* v_k_1299_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1295_, v_i_1298_, v_k_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_keys_1302_, lean_object* v_vals_1303_, lean_object* v_heq_1304_, lean_object* v_i_1305_, lean_object* v_k_1306_){
_start:
{
uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_res_1307_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1301_, v_keys_1302_, v_vals_1303_, v_heq_1304_, v_i_1305_, v_k_1306_);
lean_dec(v_k_1306_);
lean_dec_ref(v_vals_1303_);
lean_dec_ref(v_keys_1302_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1309_, uint8_t v_symm_1310_, lean_object* v_config_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1313_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1322_, v_a_1324_, v_stx_1309_, v_symm_1310_, v_config_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1325_;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_a_1322_);
lean_dec_ref(v_config_1311_);
lean_dec(v_stx_1309_);
v_a_1326_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1323_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1323_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_config_1311_);
lean_dec(v_stx_1309_);
v_a_1334_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1321_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1321_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1342_, lean_object* v_symm_1343_, lean_object* v_config_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_symm_boxed_1354_; lean_object* v_res_1355_; 
v_symm_boxed_1354_ = lean_unbox(v_symm_1343_);
v_res_1355_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1342_, v_symm_boxed_1354_, v_config_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1356_, uint8_t v_symm_1357_, lean_object* v_config_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v___f_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = lean_box(v_symm_1357_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1369_, 0, v_stx_1356_);
lean_closure_set(v___f_1369_, 1, v___x_1368_);
lean_closure_set(v___f_1369_, 2, v_config_1358_);
v___x_1370_ = 1;
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1371_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1371_, 0, lean_box(0));
lean_closure_set(v___x_1371_, 1, v___f_1369_);
lean_closure_set(v___x_1371_, 2, v_a_1359_);
lean_closure_set(v___x_1371_, 3, v_a_1360_);
v___x_1372_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1371_, v___x_1370_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1373_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1360_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v_eNew_1378_; lean_object* v_eqProof_1379_; lean_object* v_mvarIds_1380_; lean_object* v___x_1381_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_eNew_1378_ = lean_ctor_get(v_a_1375_, 0);
lean_inc_ref(v_eNew_1378_);
v_eqProof_1379_ = lean_ctor_get(v_a_1375_, 1);
lean_inc_ref(v_eqProof_1379_);
v_mvarIds_1380_ = lean_ctor_get(v_a_1375_, 2);
lean_inc(v_mvarIds_1380_);
lean_dec(v_a_1375_);
v___x_1381_ = l_Lean_MVarId_replaceTargetEq(v_a_1377_, v_eNew_1378_, v_eqProof_1379_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1382_);
lean_ctor_set(v___x_1383_, 1, v_mvarIds_1380_);
v___x_1384_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1383_, v_a_1360_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1384_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_mvarIds_1380_);
v_a_1385_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1381_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_a_1375_);
v_a_1393_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1376_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1376_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1374_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1374_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1372_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1372_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1417_, lean_object* v_symm_1418_, lean_object* v_config_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v_symm_boxed_1429_; lean_object* v_res_1430_; 
v_symm_boxed_1429_ = lean_unbox(v_symm_1418_);
v_res_1430_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1417_, v_symm_boxed_1429_, v_config_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* v_fvarId_1431_, lean_object* v_stx_1432_, uint8_t v_symm_1433_, lean_object* v_config_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1431_, v___y_1439_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = l_Lean_LocalDecl_type(v_a_1445_);
lean_dec(v_a_1445_);
v___x_1449_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1447_, v___x_1448_, v_stx_1432_, v_symm_1433_, v_config_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1445_);
lean_dec_ref(v_config_1434_);
lean_dec(v_stx_1432_);
v_a_1450_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1446_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1446_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_config_1434_);
lean_dec(v_stx_1432_);
v_a_1458_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1444_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1444_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* v_fvarId_1466_, lean_object* v_stx_1467_, lean_object* v_symm_1468_, lean_object* v_config_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v_symm_boxed_1479_; lean_object* v_res_1480_; 
v_symm_boxed_1479_ = lean_unbox(v_symm_1468_);
v_res_1480_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(v_fvarId_1466_, v_stx_1467_, v_symm_boxed_1479_, v_config_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* v_eqProof_1481_, lean_object* v___x_1482_, lean_object* v_eNew_1483_, lean_object* v_a_1484_, lean_object* v_fvarId_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Meta_mkEqMP(v_eqProof_1481_, v___x_1482_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_eNew_1483_);
v___x_1494_ = lean_box(0);
v___x_1495_ = l_Lean_MVarId_replace(v_a_1484_, v_fvarId_1485_, v_a_1492_, v___x_1493_, v___x_1494_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1495_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_fvarId_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_eNew_1483_);
v_a_1496_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1491_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1491_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* v_eqProof_1504_, lean_object* v___x_1505_, lean_object* v_eNew_1506_, lean_object* v_a_1507_, lean_object* v_fvarId_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(v_eqProof_1504_, v___x_1505_, v_eNew_1506_, v_a_1507_, v_fvarId_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(lean_object* v___f_1515_, uint8_t v___x_1516_, lean_object* v_fvarId_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_inc(v___y_1519_);
v___x_1527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1527_, 0, lean_box(0));
lean_closure_set(v___x_1527_, 1, v___f_1515_);
lean_closure_set(v___x_1527_, 2, v___y_1518_);
lean_closure_set(v___x_1527_, 3, v___y_1519_);
v___x_1528_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1527_, v___x_1516_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1529_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1519_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_eNew_1534_; lean_object* v_eqProof_1535_; lean_object* v_mvarIds_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc_n(v_a_1533_, 2);
lean_dec_ref_known(v___x_1532_, 1);
v_eNew_1534_ = lean_ctor_get(v_a_1531_, 0);
lean_inc_ref(v_eNew_1534_);
v_eqProof_1535_ = lean_ctor_get(v_a_1531_, 1);
lean_inc_ref(v_eqProof_1535_);
v_mvarIds_1536_ = lean_ctor_get(v_a_1531_, 2);
lean_inc(v_mvarIds_1536_);
lean_dec(v_a_1531_);
lean_inc(v_fvarId_1517_);
v___x_1537_ = l_Lean_mkFVar(v_fvarId_1517_);
v___f_1538_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1538_, 0, v_eqProof_1535_);
lean_closure_set(v___f_1538_, 1, v___x_1537_);
lean_closure_set(v___f_1538_, 2, v_eNew_1534_);
lean_closure_set(v___f_1538_, 3, v_a_1533_);
lean_closure_set(v___f_1538_, 4, v_fvarId_1517_);
v___x_1539_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1533_, v___f_1538_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v_mvarId_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v_mvarId_1541_ = lean_ctor_get(v_a_1540_, 1);
lean_inc(v_mvarId_1541_);
lean_dec(v_a_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_mvarId_1541_);
lean_ctor_set(v___x_1542_, 1, v_mvarIds_1536_);
v___x_1543_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1542_, v___y_1519_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1519_);
return v___x_1543_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_mvarIds_1536_);
lean_dec(v___y_1519_);
v_a_1544_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1539_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1539_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1531_);
lean_dec(v___y_1519_);
lean_dec(v_fvarId_1517_);
v_a_1552_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1532_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1532_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v___y_1519_);
lean_dec(v_fvarId_1517_);
v_a_1560_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1530_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1530_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v___y_1519_);
lean_dec(v_fvarId_1517_);
v_a_1568_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1528_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1528_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed(lean_object* v___f_1576_, lean_object* v___x_1577_, lean_object* v_fvarId_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v___x_1374__boxed_1588_; lean_object* v_res_1589_; 
v___x_1374__boxed_1588_ = lean_unbox(v___x_1577_);
v_res_1589_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(v___f_1576_, v___x_1374__boxed_1588_, v_fvarId_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1590_, uint8_t v_symm_1591_, lean_object* v_fvarId_1592_, lean_object* v_config_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___f_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v___x_1603_ = lean_box(v_symm_1591_);
lean_inc(v_fvarId_1592_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1604_, 0, v_fvarId_1592_);
lean_closure_set(v___f_1604_, 1, v_stx_1590_);
lean_closure_set(v___f_1604_, 2, v___x_1603_);
lean_closure_set(v___f_1604_, 3, v_config_1593_);
v___x_1605_ = 1;
v___x_1606_ = lean_box(v___x_1605_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1607_, 0, v___f_1604_);
lean_closure_set(v___f_1607_, 1, v___x_1606_);
lean_closure_set(v___f_1607_, 2, v_fvarId_1592_);
v___x_1608_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1607_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1609_, lean_object* v_symm_1610_, lean_object* v_fvarId_1611_, lean_object* v_config_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
uint8_t v_symm_boxed_1622_; lean_object* v_res_1623_; 
v_symm_boxed_1622_ = lean_unbox(v_symm_1610_);
v_res_1623_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1609_, v_symm_boxed_1622_, v_fvarId_1611_, v_config_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1623_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* v_x_1630_, uint8_t v_symm_1631_, lean_object* v_id_1632_, lean_object* v_declName_1633_, lean_object* v_hint_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
if (lean_obj_tag(v_a_1635_) == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_x_1630_);
v___x_1645_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_MessageData_ofConstName(v_declName_1633_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1645_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_hint_1634_);
v___x_1652_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1651_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1652_;
}
else
{
lean_object* v_head_1653_; lean_object* v_tail_1654_; lean_object* v___x_1655_; 
v_head_1653_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_head_1653_);
v_tail_1654_ = lean_ctor_get(v_a_1635_, 1);
lean_inc(v_tail_1654_);
lean_dec_ref_known(v_a_1635_, 2);
v___x_1655_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1637_, v_a_1639_, v_a_1641_, v_a_1643_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = 0;
v___x_1658_ = l_Lean_mkCIdentFrom(v_id_1632_, v_head_1653_, v___x_1657_);
v___x_1659_ = lean_box(v_symm_1631_);
lean_inc_ref(v_x_1630_);
v___x_1660_ = lean_apply_2(v_x_1630_, v___x_1659_, v___x_1658_);
v___x_1661_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1660_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_a_1656_);
lean_dec(v_tail_1654_);
lean_dec_ref(v_hint_1634_);
lean_dec(v_declName_1633_);
lean_dec_ref(v_x_1630_);
return v___x_1661_;
}
else
{
lean_object* v_a_1662_; uint8_t v___y_1664_; uint8_t v___x_1667_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
v___x_1667_ = l_Lean_Exception_isInterrupt(v_a_1662_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = l_Lean_Exception_isRuntime(v_a_1662_);
v___y_1664_ = v___x_1668_;
goto v___jp_1663_;
}
else
{
lean_dec(v_a_1662_);
v___y_1664_ = v___x_1667_;
goto v___jp_1663_;
}
v___jp_1663_:
{
if (v___y_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref_known(v___x_1661_, 1);
v___x_1665_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1656_, v___y_1664_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_dec_ref_known(v___x_1665_, 1);
v_a_1635_ = v_tail_1654_;
goto _start;
}
else
{
lean_dec(v_tail_1654_);
lean_dec_ref(v_hint_1634_);
lean_dec(v_declName_1633_);
lean_dec_ref(v_x_1630_);
return v___x_1665_;
}
}
else
{
lean_dec(v_a_1656_);
lean_dec(v_tail_1654_);
lean_dec_ref(v_hint_1634_);
lean_dec(v_declName_1633_);
lean_dec_ref(v_x_1630_);
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_tail_1654_);
lean_dec(v_head_1653_);
lean_dec_ref(v_hint_1634_);
lean_dec(v_declName_1633_);
lean_dec_ref(v_x_1630_);
v_a_1669_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1655_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1655_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* v_x_1677_, lean_object* v_symm_1678_, lean_object* v_id_1679_, lean_object* v_declName_1680_, lean_object* v_hint_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
uint8_t v_symm_boxed_1692_; lean_object* v_res_1693_; 
v_symm_boxed_1692_ = lean_unbox(v_symm_1678_);
v_res_1693_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1677_, v_symm_boxed_1692_, v_id_1679_, v_declName_1680_, v_hint_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_id_1679_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_a_1694_, lean_object* v_trees_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
v___x_1705_ = lean_apply_9(v_a_1694_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, lean_box(0));
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1714_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1706_);
lean_ctor_set(v___x_1710_, 1, v_trees_1695_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_trees_1695_);
v_a_1715_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1705_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1705_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_a_1723_, lean_object* v_trees_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_a_1723_, v_trees_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* v___x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1735_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object* v___x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(v___x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1757_, lean_object* v_mkInfoTree_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v_a_1766_, lean_object* v_a_x3f_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_infoState_1770_; lean_object* v_trees_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_st_ref_get(v___y_1757_);
v_infoState_1770_ = lean_ctor_get(v___x_1769_, 7);
lean_inc_ref(v_infoState_1770_);
lean_dec(v___x_1769_);
v_trees_1771_ = lean_ctor_get(v_infoState_1770_, 2);
lean_inc_ref(v_trees_1771_);
lean_dec_ref(v_infoState_1770_);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1765_);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
v___x_1772_ = lean_apply_10(v_mkInfoTree_1758_, v_trees_1771_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1757_, lean_box(0));
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1811_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1811_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1811_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v_infoState_1778_; lean_object* v_env_1779_; lean_object* v_nextMacroScope_1780_; lean_object* v_ngen_1781_; lean_object* v_auxDeclNGen_1782_; lean_object* v_traceState_1783_; lean_object* v_cache_1784_; lean_object* v_messages_1785_; lean_object* v_snapshotTasks_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1810_; 
v___x_1777_ = lean_st_ref_take(v___y_1757_);
v_infoState_1778_ = lean_ctor_get(v___x_1777_, 7);
v_env_1779_ = lean_ctor_get(v___x_1777_, 0);
v_nextMacroScope_1780_ = lean_ctor_get(v___x_1777_, 1);
v_ngen_1781_ = lean_ctor_get(v___x_1777_, 2);
v_auxDeclNGen_1782_ = lean_ctor_get(v___x_1777_, 3);
v_traceState_1783_ = lean_ctor_get(v___x_1777_, 4);
v_cache_1784_ = lean_ctor_get(v___x_1777_, 5);
v_messages_1785_ = lean_ctor_get(v___x_1777_, 6);
v_snapshotTasks_1786_ = lean_ctor_get(v___x_1777_, 8);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1788_ = v___x_1777_;
v_isShared_1789_ = v_isSharedCheck_1810_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snapshotTasks_1786_);
lean_inc(v_infoState_1778_);
lean_inc(v_messages_1785_);
lean_inc(v_cache_1784_);
lean_inc(v_traceState_1783_);
lean_inc(v_auxDeclNGen_1782_);
lean_inc(v_ngen_1781_);
lean_inc(v_nextMacroScope_1780_);
lean_inc(v_env_1779_);
lean_dec(v___x_1777_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1810_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
uint8_t v_enabled_1790_; lean_object* v_assignment_1791_; lean_object* v_lazyAssignment_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1808_; 
v_enabled_1790_ = lean_ctor_get_uint8(v_infoState_1778_, sizeof(void*)*3);
v_assignment_1791_ = lean_ctor_get(v_infoState_1778_, 0);
v_lazyAssignment_1792_ = lean_ctor_get(v_infoState_1778_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_infoState_1778_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v_infoState_1778_, 2);
lean_dec(v_unused_1809_);
v___x_1794_ = v_infoState_1778_;
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_lazyAssignment_1792_);
lean_inc(v_assignment_1791_);
lean_dec(v_infoState_1778_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = l_Lean_PersistentArray_push___redArg(v_a_1766_, v_a_1773_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 2, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_assignment_1791_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_lazyAssignment_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v___x_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*3, v_enabled_1790_);
v___x_1798_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 7, v___x_1798_);
v___x_1800_ = v___x_1788_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_env_1779_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_nextMacroScope_1780_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_ngen_1781_);
lean_ctor_set(v_reuseFailAlloc_1806_, 3, v_auxDeclNGen_1782_);
lean_ctor_set(v_reuseFailAlloc_1806_, 4, v_traceState_1783_);
lean_ctor_set(v_reuseFailAlloc_1806_, 5, v_cache_1784_);
lean_ctor_set(v_reuseFailAlloc_1806_, 6, v_messages_1785_);
lean_ctor_set(v_reuseFailAlloc_1806_, 7, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1806_, 8, v_snapshotTasks_1786_);
v___x_1800_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1801_ = lean_st_ref_set(v___y_1757_, v___x_1800_);
v___x_1802_ = lean_box(0);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1802_);
v___x_1804_ = v___x_1775_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_a_1766_);
v_a_1812_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1772_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1772_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1820_, lean_object* v_mkInfoTree_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v_a_1829_, lean_object* v_a_x3f_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1820_, v_mkInfoTree_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v_a_1829_, v_a_x3f_1830_);
lean_dec(v_a_x3f_1830_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1820_);
return v_res_1832_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(32u);
v___x_1834_ = lean_mk_empty_array_with_capacity(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1836_ = ((size_t)5ULL);
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_unsigned_to_nat(32u);
v___x_1839_ = lean_mk_empty_array_with_capacity(v___x_1838_);
v___x_1840_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1841_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1839_);
lean_ctor_set(v___x_1841_, 2, v___x_1837_);
lean_ctor_set(v___x_1841_, 3, v___x_1837_);
lean_ctor_set_usize(v___x_1841_, 4, v___x_1836_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_infoState_1845_; lean_object* v_trees_1846_; lean_object* v___x_1847_; lean_object* v_infoState_1848_; lean_object* v_env_1849_; lean_object* v_nextMacroScope_1850_; lean_object* v_ngen_1851_; lean_object* v_auxDeclNGen_1852_; lean_object* v_traceState_1853_; lean_object* v_cache_1854_; lean_object* v_messages_1855_; lean_object* v_snapshotTasks_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1877_; 
v___x_1844_ = lean_st_ref_get(v___y_1842_);
v_infoState_1845_ = lean_ctor_get(v___x_1844_, 7);
lean_inc_ref(v_infoState_1845_);
lean_dec(v___x_1844_);
v_trees_1846_ = lean_ctor_get(v_infoState_1845_, 2);
lean_inc_ref(v_trees_1846_);
lean_dec_ref(v_infoState_1845_);
v___x_1847_ = lean_st_ref_take(v___y_1842_);
v_infoState_1848_ = lean_ctor_get(v___x_1847_, 7);
v_env_1849_ = lean_ctor_get(v___x_1847_, 0);
v_nextMacroScope_1850_ = lean_ctor_get(v___x_1847_, 1);
v_ngen_1851_ = lean_ctor_get(v___x_1847_, 2);
v_auxDeclNGen_1852_ = lean_ctor_get(v___x_1847_, 3);
v_traceState_1853_ = lean_ctor_get(v___x_1847_, 4);
v_cache_1854_ = lean_ctor_get(v___x_1847_, 5);
v_messages_1855_ = lean_ctor_get(v___x_1847_, 6);
v_snapshotTasks_1856_ = lean_ctor_get(v___x_1847_, 8);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1858_ = v___x_1847_;
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snapshotTasks_1856_);
lean_inc(v_infoState_1848_);
lean_inc(v_messages_1855_);
lean_inc(v_cache_1854_);
lean_inc(v_traceState_1853_);
lean_inc(v_auxDeclNGen_1852_);
lean_inc(v_ngen_1851_);
lean_inc(v_nextMacroScope_1850_);
lean_inc(v_env_1849_);
lean_dec(v___x_1847_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1877_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v_enabled_1860_; lean_object* v_assignment_1861_; lean_object* v_lazyAssignment_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1875_; 
v_enabled_1860_ = lean_ctor_get_uint8(v_infoState_1848_, sizeof(void*)*3);
v_assignment_1861_ = lean_ctor_get(v_infoState_1848_, 0);
v_lazyAssignment_1862_ = lean_ctor_get(v_infoState_1848_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_infoState_1848_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_infoState_1848_, 2);
lean_dec(v_unused_1876_);
v___x_1864_ = v_infoState_1848_;
v_isShared_1865_ = v_isSharedCheck_1875_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_lazyAssignment_1862_);
lean_inc(v_assignment_1861_);
lean_dec(v_infoState_1848_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1875_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 2, v___x_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_assignment_1861_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_lazyAssignment_1862_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v___x_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*3, v_enabled_1860_);
v___x_1868_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 7, v___x_1868_);
v___x_1870_ = v___x_1858_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_env_1849_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_nextMacroScope_1850_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_ngen_1851_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_auxDeclNGen_1852_);
lean_ctor_set(v_reuseFailAlloc_1873_, 4, v_traceState_1853_);
lean_ctor_set(v_reuseFailAlloc_1873_, 5, v_cache_1854_);
lean_ctor_set(v_reuseFailAlloc_1873_, 6, v_messages_1855_);
lean_ctor_set(v_reuseFailAlloc_1873_, 7, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1873_, 8, v_snapshotTasks_1856_);
v___x_1870_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_st_ref_set(v___y_1842_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_trees_1846_);
return v___x_1872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1878_);
lean_dec(v___y_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* v_x_1881_, lean_object* v_mkInfoTree_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_infoState_1893_; uint8_t v_enabled_1894_; 
v___x_1892_ = lean_st_ref_get(v___y_1890_);
v_infoState_1893_ = lean_ctor_get(v___x_1892_, 7);
lean_inc_ref(v_infoState_1893_);
lean_dec(v___x_1892_);
v_enabled_1894_ = lean_ctor_get_uint8(v_infoState_1893_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1893_);
if (v_enabled_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_mkInfoTree_1882_);
lean_inc(v___y_1890_);
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
v___x_1895_ = lean_apply_9(v_x_1881_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, lean_box(0));
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v_a_1897_; lean_object* v_r_1898_; 
v___x_1896_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1890_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
lean_inc(v___y_1890_);
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
v_r_1898_ = lean_apply_9(v_x_1881_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, lean_box(0));
if (lean_obj_tag(v_r_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1923_; 
v_a_1899_ = lean_ctor_get(v_r_1898_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_r_1898_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1901_ = v_r_1898_;
v_isShared_1902_ = v_isSharedCheck_1923_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v_r_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1923_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
lean_inc(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 1);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1890_, v_mkInfoTree_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v_a_1897_, v___x_1904_);
lean_dec_ref(v___x_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1913_);
v___x_1907_ = v___x_1905_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1905_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_a_1899_);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1899_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1899_);
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1905_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1905_);
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
else
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v_r_1898_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v_r_1898_, 1);
v___x_1925_ = lean_box(0);
v___x_1926_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1890_, v_mkInfoTree_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v_a_1897_, v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v___x_1926_, 0);
lean_dec(v_unused_1934_);
v___x_1928_ = v___x_1926_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_dec(v___x_1926_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 1);
lean_ctor_set(v___x_1928_, 0, v_a_1924_);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1924_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1924_);
v_a_1935_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1926_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1926_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_1943_, lean_object* v_mkInfoTree_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_1943_, v_mkInfoTree_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_1964_, uint8_t v___x_1965_, lean_object* v___x_1966_, lean_object* v_x_1967_, uint8_t v___x_1968_, lean_object* v___x_1969_, lean_object* v___x_1970_, lean_object* v___f_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_fileName_1981_; lean_object* v_fileMap_1982_; lean_object* v_options_1983_; lean_object* v_currRecDepth_1984_; lean_object* v_maxRecDepth_1985_; lean_object* v_ref_1986_; lean_object* v_currNamespace_1987_; lean_object* v_openDecls_1988_; lean_object* v_initHeartbeats_1989_; lean_object* v_maxHeartbeats_1990_; lean_object* v_quotContext_1991_; lean_object* v_currMacroScope_1992_; uint8_t v_diag_1993_; lean_object* v_cancelTk_x3f_1994_; uint8_t v_suppressElabErrors_1995_; lean_object* v_inheritedTraceOptions_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2014_; 
v_fileName_1981_ = lean_ctor_get(v___y_1978_, 0);
v_fileMap_1982_ = lean_ctor_get(v___y_1978_, 1);
v_options_1983_ = lean_ctor_get(v___y_1978_, 2);
v_currRecDepth_1984_ = lean_ctor_get(v___y_1978_, 3);
v_maxRecDepth_1985_ = lean_ctor_get(v___y_1978_, 4);
v_ref_1986_ = lean_ctor_get(v___y_1978_, 5);
v_currNamespace_1987_ = lean_ctor_get(v___y_1978_, 6);
v_openDecls_1988_ = lean_ctor_get(v___y_1978_, 7);
v_initHeartbeats_1989_ = lean_ctor_get(v___y_1978_, 8);
v_maxHeartbeats_1990_ = lean_ctor_get(v___y_1978_, 9);
v_quotContext_1991_ = lean_ctor_get(v___y_1978_, 10);
v_currMacroScope_1992_ = lean_ctor_get(v___y_1978_, 11);
v_diag_1993_ = lean_ctor_get_uint8(v___y_1978_, sizeof(void*)*14);
v_cancelTk_x3f_1994_ = lean_ctor_get(v___y_1978_, 12);
v_suppressElabErrors_1995_ = lean_ctor_get_uint8(v___y_1978_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1996_ = lean_ctor_get(v___y_1978_, 13);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___y_1978_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1998_ = v___y_1978_;
v_isShared_1999_ = v_isSharedCheck_2014_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_inheritedTraceOptions_1996_);
lean_inc(v_cancelTk_x3f_1994_);
lean_inc(v_currMacroScope_1992_);
lean_inc(v_quotContext_1991_);
lean_inc(v_maxHeartbeats_1990_);
lean_inc(v_initHeartbeats_1989_);
lean_inc(v_openDecls_1988_);
lean_inc(v_currNamespace_1987_);
lean_inc(v_ref_1986_);
lean_inc(v_maxRecDepth_1985_);
lean_inc(v_currRecDepth_1984_);
lean_inc(v_options_1983_);
lean_inc(v_fileMap_1982_);
lean_inc(v_fileName_1981_);
lean_dec(v___y_1978_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2014_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_ref_2000_; lean_object* v___x_2002_; 
v_ref_2000_ = l_Lean_replaceRef(v___x_1964_, v_ref_1986_);
lean_dec(v_ref_1986_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 5, v_ref_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_fileName_1981_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_fileMap_1982_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_options_1983_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_currRecDepth_1984_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_maxRecDepth_1985_);
lean_ctor_set(v_reuseFailAlloc_2013_, 5, v_ref_2000_);
lean_ctor_set(v_reuseFailAlloc_2013_, 6, v_currNamespace_1987_);
lean_ctor_set(v_reuseFailAlloc_2013_, 7, v_openDecls_1988_);
lean_ctor_set(v_reuseFailAlloc_2013_, 8, v_initHeartbeats_1989_);
lean_ctor_set(v_reuseFailAlloc_2013_, 9, v_maxHeartbeats_1990_);
lean_ctor_set(v_reuseFailAlloc_2013_, 10, v_quotContext_1991_);
lean_ctor_set(v_reuseFailAlloc_2013_, 11, v_currMacroScope_1992_);
lean_ctor_set(v_reuseFailAlloc_2013_, 12, v_cancelTk_x3f_1994_);
lean_ctor_set(v_reuseFailAlloc_2013_, 13, v_inheritedTraceOptions_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*14, v_diag_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*14 + 1, v_suppressElabErrors_1995_);
v___x_2002_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
if (v___x_1965_ == 0)
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_1966_);
v___x_2004_ = l_Lean_Syntax_isOfKind(v___x_1966_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v___f_1971_);
v___x_2005_ = lean_box(v___x_1968_);
v___x_2006_ = lean_apply_11(v_x_1967_, v___x_2005_, v___x_1966_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___x_2002_, v___y_1979_, lean_box(0));
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = l_Lean_Syntax_getArg(v___x_1966_, v___x_1969_);
lean_inc(v___x_2007_);
v___x_2008_ = l_Lean_Syntax_isOfKind(v___x_2007_, v___x_1970_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v___x_2007_);
lean_dec_ref(v___f_1971_);
v___x_2009_ = lean_box(v___x_1968_);
v___x_2010_ = lean_apply_11(v_x_1967_, v___x_2009_, v___x_1966_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___x_2002_, v___y_1979_, lean_box(0));
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; 
lean_dec_ref(v_x_1967_);
lean_dec(v___x_1966_);
v___x_2011_ = lean_apply_10(v___f_1971_, v___x_2007_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___x_2002_, v___y_1979_, lean_box(0));
return v___x_2011_;
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec_ref(v_x_1967_);
v___x_2012_ = lean_apply_10(v___f_1971_, v___x_1966_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___x_2002_, v___y_1979_, lean_box(0));
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2015_ = _args[0];
lean_object* v___x_2016_ = _args[1];
lean_object* v___x_2017_ = _args[2];
lean_object* v_x_2018_ = _args[3];
lean_object* v___x_2019_ = _args[4];
lean_object* v___x_2020_ = _args[5];
lean_object* v___x_2021_ = _args[6];
lean_object* v___f_2022_ = _args[7];
lean_object* v___y_2023_ = _args[8];
lean_object* v___y_2024_ = _args[9];
lean_object* v___y_2025_ = _args[10];
lean_object* v___y_2026_ = _args[11];
lean_object* v___y_2027_ = _args[12];
lean_object* v___y_2028_ = _args[13];
lean_object* v___y_2029_ = _args[14];
lean_object* v___y_2030_ = _args[15];
lean_object* v___y_2031_ = _args[16];
_start:
{
uint8_t v___x_16641__boxed_2032_; uint8_t v___x_16643__boxed_2033_; lean_object* v_res_2034_; 
v___x_16641__boxed_2032_ = lean_unbox(v___x_2016_);
v___x_16643__boxed_2033_ = lean_unbox(v___x_2019_);
v_res_2034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_2015_, v___x_16641__boxed_2032_, v___x_2017_, v_x_2018_, v___x_16643__boxed_2033_, v___x_2020_, v___x_2021_, v___f_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
lean_dec(v___x_2015_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_2035_, lean_object* v_trees_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v___x_2046_ = lean_apply_9(v_a_2035_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2055_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2047_);
lean_ctor_set(v___x_2051_, 1, v_trees_2036_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2051_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_trees_2036_);
v_a_2056_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2046_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2046_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_2064_, lean_object* v_trees_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_2064_, v_trees_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2076_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2097_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
return v___x_2100_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_2104_, uint8_t v___x_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_id_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___f_2118_; lean_object* v___x_2119_; 
lean_inc(v_id_2108_);
v___f_2118_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2118_, 0, v_id_2108_);
v___x_2119_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2118_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
if (lean_obj_tag(v_a_2120_) == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2110_, v___y_2112_, v___y_2114_, v___y_2116_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
lean_inc(v_id_2108_);
v___x_2123_ = l_Lean_realizeGlobalConstNoOverload(v_id_2108_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
lean_dec(v_a_2122_);
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_n(v_a_2124_, 2);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2124_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (lean_obj_tag(v_a_2126_) == 1)
{
lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v___x_2107_);
v_val_2127_ = lean_ctor_get(v_a_2126_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2129_ = v_a_2126_;
v_isShared_2130_ = v_isSharedCheck_2171_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_dec(v_a_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2171_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
uint8_t v___x_2131_; lean_object* v___y_2133_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2131_ = 0;
v___x_2160_ = lean_array_get_size(v_val_2127_);
v___x_2161_ = lean_nat_dec_eq(v___x_2160_, v___x_2106_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_2163_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2124_);
v___x_2164_ = l_Lean_Name_str___override(v_a_2124_, v___x_2163_);
v___x_2165_ = l_Lean_MessageData_ofName(v___x_2164_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2162_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_MessageData_hint_x27(v___x_2168_);
v___y_2133_ = v___x_2169_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2133_ = v___x_2170_;
goto v___jp_2132_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; 
lean_inc(v_a_2124_);
v___x_2134_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2124_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_lctx_2136_; lean_object* v___x_2138_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_lctx_2136_ = lean_ctor_get(v___y_2113_, 2);
lean_inc_ref(v_lctx_2136_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v_lctx_2136_);
v___x_2138_ = v___x_2129_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_lctx_2136_);
v___x_2138_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(0);
lean_inc(v_id_2108_);
v___x_2140_ = l_Lean_Elab_Term_addTermInfo(v_id_2108_, v_a_2135_, v_a_2120_, v___x_2138_, v___x_2139_, v___x_2131_, v___x_2131_, v___x_2131_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec_ref_known(v___x_2140_, 1);
v___x_2141_ = lean_array_to_list(v_val_2127_);
v___x_2142_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_2104_, v___x_2105_, v_id_2108_, v_a_2124_, v___y_2133_, v___x_2141_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v_id_2108_);
return v___x_2142_;
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v___y_2133_);
lean_dec(v_val_2127_);
lean_dec(v_a_2124_);
lean_dec(v_id_2108_);
lean_dec_ref(v_x_2104_);
v_a_2143_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2140_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2140_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v___y_2133_);
lean_del_object(v___x_2129_);
lean_dec(v_val_2127_);
lean_dec(v_a_2124_);
lean_dec(v_id_2108_);
lean_dec_ref(v_x_2104_);
v_a_2152_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2134_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2134_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v_a_2126_);
lean_dec(v_a_2124_);
lean_dec(v_id_2108_);
v___x_2172_ = lean_box(v___x_2105_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
v___x_2173_ = lean_apply_11(v_x_2104_, v___x_2172_, v___x_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, lean_box(0));
return v___x_2173_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2124_);
lean_dec(v_id_2108_);
lean_dec(v___x_2107_);
lean_dec_ref(v_x_2104_);
v_a_2174_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2125_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2125_);
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
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_id_2108_);
v_a_2182_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2184_ = v___x_2123_;
v_isShared_2185_ = v_isSharedCheck_2196_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2123_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2196_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
uint8_t v___y_2187_; uint8_t v___x_2194_; 
v___x_2194_ = l_Lean_Exception_isInterrupt(v_a_2182_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
lean_inc(v_a_2182_);
v___x_2195_ = l_Lean_Exception_isRuntime(v_a_2182_);
v___y_2187_ = v___x_2195_;
goto v___jp_2186_;
}
else
{
v___y_2187_ = v___x_2194_;
goto v___jp_2186_;
}
v___jp_2186_:
{
if (v___y_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_del_object(v___x_2184_);
lean_dec(v_a_2182_);
v___x_2188_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2122_, v___y_2187_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref_known(v___x_2188_, 1);
v___x_2189_ = lean_box(v___x_2105_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
v___x_2190_ = lean_apply_11(v_x_2104_, v___x_2189_, v___x_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, lean_box(0));
return v___x_2190_;
}
else
{
lean_dec(v___x_2107_);
lean_dec_ref(v_x_2104_);
return v___x_2188_;
}
}
else
{
lean_object* v___x_2192_; 
lean_dec(v_a_2122_);
lean_dec(v___x_2107_);
lean_dec_ref(v_x_2104_);
if (v_isShared_2185_ == 0)
{
v___x_2192_ = v___x_2184_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2182_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_id_2108_);
lean_dec(v___x_2107_);
lean_dec_ref(v_x_2104_);
v_a_2197_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2121_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2121_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref_known(v_a_2120_, 1);
lean_dec(v_id_2108_);
v___x_2205_ = lean_box(v___x_2105_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
v___x_2206_ = lean_apply_11(v_x_2104_, v___x_2205_, v___x_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, lean_box(0));
return v___x_2206_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_id_2108_);
lean_dec(v___x_2107_);
lean_dec_ref(v_x_2104_);
v_a_2207_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2119_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2119_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v_id_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
uint8_t v___x_16841__boxed_2229_; lean_object* v_res_2230_; 
v___x_16841__boxed_2229_ = lean_unbox(v___x_2216_);
v_res_2230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_2215_, v___x_16841__boxed_2229_, v___x_2217_, v___x_2218_, v_id_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___x_2217_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2237_, lean_object* v_rules_2238_, lean_object* v_x_2239_, lean_object* v_a_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_lt(v_a_2240_, v_upperBound_2237_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_dec(v_a_2240_);
lean_dec_ref(v_x_2239_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_b_2241_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2253_ = lean_unsigned_to_nat(2u);
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_nat_mul(v_a_2240_, v___x_2253_);
v___x_2259_ = lean_array_get_borrowed(v___x_2254_, v_rules_2238_, v___x_2258_);
v___x_2293_ = lean_nat_add(v___x_2258_, v___x_2256_);
lean_dec(v___x_2258_);
v___x_2294_ = lean_array_get_size(v_rules_2238_);
v___x_2295_ = lean_nat_dec_lt(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_dec(v___x_2293_);
v___y_2261_ = v___x_2254_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_array_fget_borrowed(v_rules_2238_, v___x_2293_);
lean_dec(v___x_2293_);
lean_inc(v___x_2296_);
v___y_2261_ = v___x_2296_;
goto v___jp_2260_;
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2262_ = lean_mk_empty_array_with_capacity(v___x_2253_);
lean_inc(v___x_2259_);
v___x_2263_ = lean_array_push(v___x_2262_, v___x_2259_);
v___x_2264_ = lean_array_push(v___x_2263_, v___y_2261_);
v___x_2265_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
v___x_2266_ = lean_box(2);
v___x_2267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2265_);
lean_ctor_set(v___x_2267_, 2, v___x_2264_);
v___x_2268_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2267_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___f_2270_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2270_, 0, v_a_2269_);
v___x_2271_ = l_Lean_Syntax_getArg(v___x_2259_, v___x_2255_);
v___x_2272_ = l_Lean_Syntax_isNone(v___x_2271_);
lean_dec(v___x_2271_);
v___x_2273_ = lean_bool_not(v___x_2272_);
v___x_2274_ = l_Lean_Syntax_getArg(v___x_2259_, v___x_2256_);
v___x_2275_ = lean_box(v___x_2273_);
lean_inc_n(v___x_2274_, 2);
lean_inc_ref_n(v_x_2239_, 2);
v___f_2276_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2276_, 0, v_x_2239_);
lean_closure_set(v___f_2276_, 1, v___x_2275_);
lean_closure_set(v___f_2276_, 2, v___x_2256_);
lean_closure_set(v___f_2276_, 3, v___x_2274_);
v___x_2277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2278_ = l_Lean_Syntax_isOfKind(v___x_2274_, v___x_2277_);
v___x_2279_ = lean_box(v___x_2278_);
v___x_2280_ = lean_box(v___x_2273_);
lean_inc(v___x_2259_);
v___f_2281_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed), 17, 8);
lean_closure_set(v___f_2281_, 0, v___x_2259_);
lean_closure_set(v___f_2281_, 1, v___x_2279_);
lean_closure_set(v___f_2281_, 2, v___x_2274_);
lean_closure_set(v___f_2281_, 3, v_x_2239_);
lean_closure_set(v___f_2281_, 4, v___x_2280_);
lean_closure_set(v___f_2281_, 5, v___x_2256_);
lean_closure_set(v___f_2281_, 6, v___x_2277_);
lean_closure_set(v___f_2281_, 7, v___f_2276_);
v___x_2282_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2281_, v___f_2270_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v___x_2283_; 
lean_dec_ref_known(v___x_2282_, 1);
v___x_2283_ = lean_nat_add(v_a_2240_, v___x_2256_);
lean_dec(v_a_2240_);
v_a_2240_ = v___x_2283_;
v_b_2241_ = v___x_2257_;
goto _start;
}
else
{
lean_dec(v_a_2240_);
lean_dec_ref(v_x_2239_);
return v___x_2282_;
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_2240_);
lean_dec_ref(v_x_2239_);
v_a_2285_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2268_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2268_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2297_, lean_object* v_rules_2298_, lean_object* v_x_2299_, lean_object* v_a_2300_, lean_object* v_b_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2297_, v_rules_2298_, v_x_2299_, v_a_2300_, v_b_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec_ref(v_rules_2298_);
lean_dec(v_upperBound_2297_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2314_, lean_object* v_rwRulesSeqStx_2315_, lean_object* v_x_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v_lbrak_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v_lbrak_2327_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2315_, v___x_2326_);
v___x_2328_ = lean_unsigned_to_nat(2u);
v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2328_);
v___x_2330_ = lean_array_push(v___x_2329_, v_token_2314_);
v___x_2331_ = lean_array_push(v___x_2330_, v_lbrak_2327_);
v___x_2332_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
v___x_2333_ = lean_box(2);
v___x_2334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___x_2332_);
lean_ctor_set(v___x_2334_, 2, v___x_2331_);
v___x_2335_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2334_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2337_, 0, v_a_2336_);
v___x_2338_ = lean_box(0);
v___f_2339_ = ((lean_object*)(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0));
v___x_2340_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2339_, v___f_2337_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_rules_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref_known(v___x_2340_, 1);
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2315_, v___x_2341_);
v_rules_2343_ = l_Lean_Syntax_getArgs(v___x_2342_);
lean_dec(v___x_2342_);
v___x_2344_ = lean_array_get_size(v_rules_2343_);
v___x_2345_ = lean_nat_add(v___x_2344_, v___x_2341_);
v___x_2346_ = lean_nat_shiftr(v___x_2345_, v___x_2341_);
lean_dec(v___x_2345_);
v___x_2347_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_2346_, v_rules_2343_, v_x_2316_, v___x_2326_, v___x_2338_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec_ref(v_rules_2343_);
lean_dec(v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v___x_2347_, 0);
lean_dec(v_unused_2355_);
v___x_2349_ = v___x_2347_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v___x_2347_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2338_);
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2338_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
return v___x_2347_;
}
}
else
{
lean_dec_ref(v_x_2316_);
return v___x_2340_;
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_x_2316_);
v_a_2356_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2335_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2335_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2364_, lean_object* v_rwRulesSeqStx_2365_, lean_object* v_x_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2364_, v_rwRulesSeqStx_2365_, v_x_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_rwRulesSeqStx_2365_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* v_00_u03b1_2397_, lean_object* v_x_2398_, lean_object* v_mkInfoTree_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_2398_, v_mkInfoTree_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2410_, lean_object* v_x_2411_, lean_object* v_mkInfoTree_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(v_00_u03b1_2410_, v_x_2411_, v_mkInfoTree_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object* v_upperBound_2423_, lean_object* v_rules_2424_, lean_object* v_x_2425_, lean_object* v_inst_2426_, lean_object* v_R_2427_, lean_object* v_a_2428_, lean_object* v_b_2429_, lean_object* v_c_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2423_, v_rules_2424_, v_x_2425_, v_a_2428_, v_b_2429_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2441_ = _args[0];
lean_object* v_rules_2442_ = _args[1];
lean_object* v_x_2443_ = _args[2];
lean_object* v_inst_2444_ = _args[3];
lean_object* v_R_2445_ = _args[4];
lean_object* v_a_2446_ = _args[5];
lean_object* v_b_2447_ = _args[6];
lean_object* v_c_2448_ = _args[7];
lean_object* v___y_2449_ = _args[8];
lean_object* v___y_2450_ = _args[9];
lean_object* v___y_2451_ = _args[10];
lean_object* v___y_2452_ = _args[11];
lean_object* v___y_2453_ = _args[12];
lean_object* v___y_2454_ = _args[13];
lean_object* v___y_2455_ = _args[14];
lean_object* v___y_2456_ = _args[15];
lean_object* v___y_2457_ = _args[16];
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(v_upperBound_2441_, v_rules_2442_, v_x_2443_, v_inst_2444_, v_R_2445_, v_a_2446_, v_b_2447_, v_c_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_rules_2442_);
lean_dec(v_upperBound_2441_);
return v_res_2458_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = lean_box(0);
v___x_2460_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_ref_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_ref_2487_ = lean_ctor_get(v___y_2484_, 5);
v___x_2488_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
lean_inc(v_ref_2487_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_ref_2487_);
lean_ctor_set(v___x_2493_, 1, v_a_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 1);
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v_ctor_2509_, lean_object* v_args_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2578_ = lean_string_dec_eq(v_ctor_2509_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_array_get_size(v_args_2510_);
v___x_2581_ = lean_unsigned_to_nat(4u);
v___x_2582_ = lean_nat_dec_eq(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2584_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2583_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
goto v___jp_2516_;
}
}
v___jp_2516_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = l_Lean_instInhabitedExpr;
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_array_get_borrowed(v___x_2517_, v_args_2510_, v___x_2518_);
lean_inc(v___x_2519_);
v___x_2520_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2519_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = lean_array_get_borrowed(v___x_2517_, v_args_2510_, v___x_2522_);
lean_inc(v___x_2523_);
v___x_2524_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2523_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = lean_unsigned_to_nat(2u);
v___x_2527_ = lean_array_get_borrowed(v___x_2517_, v_args_2510_, v___x_2526_);
lean_inc(v___x_2527_);
v___x_2528_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2527_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_unsigned_to_nat(3u);
v___x_2531_ = lean_array_get_borrowed(v___x_2517_, v_args_2510_, v___x_2530_);
lean_inc(v___x_2531_);
v___x_2532_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2531_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2544_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2544_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2544_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; uint8_t v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2542_; 
v___x_2537_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2537_, 0, v_a_2529_);
v___x_2538_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1, v___x_2538_);
v___x_2539_ = lean_unbox(v_a_2525_);
lean_dec(v_a_2525_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1 + 1, v___x_2539_);
v___x_2540_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1 + 2, v___x_2540_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2537_);
v___x_2542_ = v___x_2535_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2529_);
lean_dec(v_a_2525_);
lean_dec(v_a_2521_);
v_a_2545_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2532_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2532_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_a_2525_);
lean_dec(v_a_2521_);
v_a_2553_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2528_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2528_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2521_);
v_a_2561_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2524_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2524_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2520_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2520_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_2593_, lean_object* v_args_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v_ctor_2593_, v_args_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_args_2594_);
lean_dec_ref(v_ctor_2593_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___f_2616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0));
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2618_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2617_, v___f_2616_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2626_, lean_object* v_msg_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2634_, lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2634_, v_msg_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_box(0);
v___x_2644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2645_ = l_Lean_Expr_const___override(v___x_2644_, v___x_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___x_2648_);
return v___x_2650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2651_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_box(1);
v___x_2653_ = l_Lean_MessageData_ofFormat(v___x_2652_);
return v___x_2653_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2658_ = l_Lean_MessageData_ofFormat(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 0)
{
return v_x_2659_;
}
else
{
lean_object* v_head_2661_; lean_object* v_tail_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2684_; 
v_head_2661_ = lean_ctor_get(v_x_2660_, 0);
v_tail_2662_ = lean_ctor_get(v_x_2660_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_x_2660_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2664_ = v_x_2660_;
v_isShared_2665_ = v_isSharedCheck_2684_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_tail_2662_);
lean_inc(v_head_2661_);
lean_dec(v_x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2684_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_before_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2682_; 
v_before_2666_ = lean_ctor_get(v_head_2661_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_head_2661_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v_head_2661_, 1);
lean_dec(v_unused_2683_);
v___x_2668_ = v_head_2661_;
v_isShared_2669_ = v_isSharedCheck_2682_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_before_2666_);
lean_dec(v_head_2661_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2682_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 7);
lean_ctor_set(v___x_2668_, 1, v___x_2670_);
lean_ctor_set(v___x_2668_, 0, v_x_2659_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_x_2659_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 7);
lean_ctor_set(v___x_2664_, 1, v___x_2673_);
lean_ctor_set(v___x_2664_, 0, v___x_2672_);
v___x_2675_ = v___x_2664_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = l_Lean_MessageData_ofSyntax(v_before_2666_);
v___x_2677_ = l_Lean_indentD(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2675_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v_x_2659_ = v___x_2678_;
v_x_2660_ = v_tail_2662_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2685_, lean_object* v_opt_2686_){
_start:
{
lean_object* v_name_2687_; lean_object* v_defValue_2688_; lean_object* v_map_2689_; lean_object* v___x_2690_; 
v_name_2687_ = lean_ctor_get(v_opt_2686_, 0);
v_defValue_2688_ = lean_ctor_get(v_opt_2686_, 1);
v_map_2689_ = lean_ctor_get(v_opts_2685_, 0);
v___x_2690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2689_, v_name_2687_);
if (lean_obj_tag(v___x_2690_) == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_unbox(v_defValue_2688_);
return v___x_2691_;
}
else
{
lean_object* v_val_2692_; 
v_val_2692_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_val_2692_);
lean_dec_ref_known(v___x_2690_, 1);
if (lean_obj_tag(v_val_2692_) == 1)
{
uint8_t v_v_2693_; 
v_v_2693_ = lean_ctor_get_uint8(v_val_2692_, 0);
lean_dec_ref_known(v_val_2692_, 0);
return v_v_2693_;
}
else
{
uint8_t v___x_2694_; 
lean_dec(v_val_2692_);
v___x_2694_ = lean_unbox(v_defValue_2688_);
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2695_, lean_object* v_opt_2696_){
_start:
{
uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_res_2697_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2695_, v_opt_2696_);
lean_dec_ref(v_opt_2696_);
lean_dec_ref(v_opts_2695_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2703_ = l_Lean_MessageData_ofFormat(v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2704_, lean_object* v_macroStack_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_options_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; uint8_t v___x_2711_; 
v_options_2708_ = lean_ctor_get(v___y_2706_, 2);
v___x_2709_ = l_Lean_Elab_pp_macroStack;
v___x_2710_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_2708_, v___x_2709_);
v___x_2711_ = lean_bool_not(v___x_2710_);
if (v___x_2711_ == 0)
{
if (lean_obj_tag(v_macroStack_2705_) == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v_msgData_2704_);
return v___x_2712_;
}
else
{
lean_object* v_head_2713_; lean_object* v_after_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2729_; 
v_head_2713_ = lean_ctor_get(v_macroStack_2705_, 0);
lean_inc(v_head_2713_);
v_after_2714_ = lean_ctor_get(v_head_2713_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_head_2713_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v_head_2713_, 0);
lean_dec(v_unused_2730_);
v___x_2716_ = v_head_2713_;
v_isShared_2717_ = v_isSharedCheck_2729_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_after_2714_);
lean_dec(v_head_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2729_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 7);
lean_ctor_set(v___x_2716_, 1, v___x_2718_);
lean_ctor_set(v___x_2716_, 0, v_msgData_2704_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_msgData_2704_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v_msgData_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2721_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = l_Lean_MessageData_ofSyntax(v_after_2714_);
v___x_2724_ = l_Lean_indentD(v___x_2723_);
v_msgData_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2725_, 0, v___x_2722_);
lean_ctor_set(v_msgData_2725_, 1, v___x_2724_);
v___x_2726_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_2725_, v_macroStack_2705_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
}
}
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_macroStack_2705_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_msgData_2704_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_2732_, lean_object* v_macroStack_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2732_, v_macroStack_2733_, v___y_2734_);
lean_dec_ref(v___y_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_ref_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v_macroStack_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2759_; 
v_ref_2745_ = lean_ctor_get(v___y_2742_, 5);
v___x_2746_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2737_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v_macroStack_2748_ = lean_ctor_get(v___y_2738_, 1);
v___x_2749_ = l_Lean_Elab_getBetterRef(v_ref_2745_, v_macroStack_2748_);
lean_inc(v_macroStack_2748_);
v___x_2750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_2747_, v_macroStack_2748_, v___y_2742_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2749_);
lean_ctor_set(v___x_2755_, 1, v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 1);
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = l_Lean_Expr_hasMVar(v_e_2769_);
v___x_2773_ = lean_bool_not(v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v_mctx_2775_; lean_object* v___x_2776_; lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v___x_2779_; lean_object* v_cache_2780_; lean_object* v_zetaDeltaFVarIds_2781_; lean_object* v_postponed_2782_; lean_object* v_diag_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2792_; 
v___x_2774_ = lean_st_ref_get(v___y_2770_);
v_mctx_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_ref(v_mctx_2775_);
lean_dec(v___x_2774_);
v___x_2776_ = l_Lean_instantiateMVarsCore(v_mctx_2775_, v_e_2769_);
v_fst_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_fst_2777_);
v_snd_2778_ = lean_ctor_get(v___x_2776_, 1);
lean_inc(v_snd_2778_);
lean_dec_ref(v___x_2776_);
v___x_2779_ = lean_st_ref_take(v___y_2770_);
v_cache_2780_ = lean_ctor_get(v___x_2779_, 1);
v_zetaDeltaFVarIds_2781_ = lean_ctor_get(v___x_2779_, 2);
v_postponed_2782_ = lean_ctor_get(v___x_2779_, 3);
v_diag_2783_ = lean_ctor_get(v___x_2779_, 4);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v___x_2779_, 0);
lean_dec(v_unused_2793_);
v___x_2785_ = v___x_2779_;
v_isShared_2786_ = v_isSharedCheck_2792_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_diag_2783_);
lean_inc(v_postponed_2782_);
lean_inc(v_zetaDeltaFVarIds_2781_);
lean_inc(v_cache_2780_);
lean_dec(v___x_2779_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2792_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_snd_2778_);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_snd_2778_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_cache_2780_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_zetaDeltaFVarIds_2781_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_postponed_2782_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_diag_2783_);
v___x_2788_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_st_ref_set(v___y_2770_, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_fst_2777_);
return v___x_2790_;
}
}
}
else
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_e_2769_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_2795_, v___y_2796_);
lean_dec(v___y_2796_);
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lean_Elab_abortTermExceptionId;
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_2806_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_2814_ = l_Lean_Expr_const___override(v___x_2813_, v___x_2812_);
return v___x_2814_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2815_; lean_object* v_ty_x3f_2816_; 
v___x_2815_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_2816_, 0, v___x_2815_);
return v_ty_x3f_2816_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_2821_ = l_Lean_MessageData_ofExpr(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_2823_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
lean_ctor_set(v___x_2824_, 1, v___x_2822_);
return v___x_2824_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2826_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
lean_ctor_set(v___x_2827_, 1, v___x_2825_);
return v___x_2827_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_ty_x3f_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_fileName_2848_; lean_object* v_fileMap_2849_; lean_object* v_options_2850_; lean_object* v_currRecDepth_2851_; lean_object* v_maxRecDepth_2852_; lean_object* v_ref_2853_; lean_object* v_currNamespace_2854_; lean_object* v_openDecls_2855_; lean_object* v_initHeartbeats_2856_; lean_object* v_maxHeartbeats_2857_; lean_object* v_quotContext_2858_; lean_object* v_currMacroScope_2859_; uint8_t v_diag_2860_; lean_object* v_cancelTk_x3f_2861_; uint8_t v_suppressElabErrors_2862_; lean_object* v_inheritedTraceOptions_2863_; uint8_t v___x_2864_; lean_object* v_ref_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_ty_x3f_2842_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_2843_ = 1;
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_box(v___x_2843_);
v___x_2846_ = lean_box(v___x_2843_);
lean_inc(v_stx_2834_);
v___x_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2847_, 0, v_stx_2834_);
lean_closure_set(v___x_2847_, 1, v_ty_x3f_2842_);
lean_closure_set(v___x_2847_, 2, v___x_2845_);
lean_closure_set(v___x_2847_, 3, v___x_2846_);
lean_closure_set(v___x_2847_, 4, v___x_2844_);
v_fileName_2848_ = lean_ctor_get(v_a_2839_, 0);
v_fileMap_2849_ = lean_ctor_get(v_a_2839_, 1);
v_options_2850_ = lean_ctor_get(v_a_2839_, 2);
v_currRecDepth_2851_ = lean_ctor_get(v_a_2839_, 3);
v_maxRecDepth_2852_ = lean_ctor_get(v_a_2839_, 4);
v_ref_2853_ = lean_ctor_get(v_a_2839_, 5);
v_currNamespace_2854_ = lean_ctor_get(v_a_2839_, 6);
v_openDecls_2855_ = lean_ctor_get(v_a_2839_, 7);
v_initHeartbeats_2856_ = lean_ctor_get(v_a_2839_, 8);
v_maxHeartbeats_2857_ = lean_ctor_get(v_a_2839_, 9);
v_quotContext_2858_ = lean_ctor_get(v_a_2839_, 10);
v_currMacroScope_2859_ = lean_ctor_get(v_a_2839_, 11);
v_diag_2860_ = lean_ctor_get_uint8(v_a_2839_, sizeof(void*)*14);
v_cancelTk_x3f_2861_ = lean_ctor_get(v_a_2839_, 12);
v_suppressElabErrors_2862_ = lean_ctor_get_uint8(v_a_2839_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2863_ = lean_ctor_get(v_a_2839_, 13);
v___x_2864_ = 1;
v_ref_2865_ = l_Lean_replaceRef(v_stx_2834_, v_ref_2853_);
lean_dec(v_stx_2834_);
lean_inc_ref(v_inheritedTraceOptions_2863_);
lean_inc(v_cancelTk_x3f_2861_);
lean_inc(v_currMacroScope_2859_);
lean_inc(v_quotContext_2858_);
lean_inc(v_maxHeartbeats_2857_);
lean_inc(v_initHeartbeats_2856_);
lean_inc(v_openDecls_2855_);
lean_inc(v_currNamespace_2854_);
lean_inc(v_maxRecDepth_2852_);
lean_inc(v_currRecDepth_2851_);
lean_inc_ref(v_options_2850_);
lean_inc_ref(v_fileMap_2849_);
lean_inc_ref(v_fileName_2848_);
v___x_2866_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2866_, 0, v_fileName_2848_);
lean_ctor_set(v___x_2866_, 1, v_fileMap_2849_);
lean_ctor_set(v___x_2866_, 2, v_options_2850_);
lean_ctor_set(v___x_2866_, 3, v_currRecDepth_2851_);
lean_ctor_set(v___x_2866_, 4, v_maxRecDepth_2852_);
lean_ctor_set(v___x_2866_, 5, v_ref_2865_);
lean_ctor_set(v___x_2866_, 6, v_currNamespace_2854_);
lean_ctor_set(v___x_2866_, 7, v_openDecls_2855_);
lean_ctor_set(v___x_2866_, 8, v_initHeartbeats_2856_);
lean_ctor_set(v___x_2866_, 9, v_maxHeartbeats_2857_);
lean_ctor_set(v___x_2866_, 10, v_quotContext_2858_);
lean_ctor_set(v___x_2866_, 11, v_currMacroScope_2859_);
lean_ctor_set(v___x_2866_, 12, v_cancelTk_x3f_2861_);
lean_ctor_set(v___x_2866_, 13, v_inheritedTraceOptions_2863_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*14, v_diag_2860_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*14 + 1, v_suppressElabErrors_2862_);
v___x_2867_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2847_, v___x_2864_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v___x_2866_, v_a_2840_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v_a_2870_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; uint8_t v___x_2965_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_2868_, v_a_2838_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2965_ = l_Lean_Expr_hasSorry(v_a_2870_);
if (v___x_2965_ == 0)
{
v___y_2910_ = v_a_2835_;
v___y_2911_ = v_a_2836_;
v___y_2912_ = v_a_2837_;
v___y_2913_ = v_a_2838_;
v___y_2914_ = v___x_2866_;
v___y_2915_ = v_a_2840_;
goto v___jp_2909_;
}
else
{
uint8_t v___x_2966_; 
v___x_2966_ = l_Lean_Expr_hasSyntheticSorry(v_a_2870_);
if (v___x_2966_ == 0)
{
v___y_2947_ = v_a_2835_;
v___y_2948_ = v_a_2836_;
v___y_2949_ = v_a_2837_;
v___y_2950_ = v_a_2838_;
v___y_2951_ = v___x_2866_;
v___y_2952_ = v_a_2840_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2967_; lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_a_2870_);
lean_dec_ref_known(v___x_2866_, 14);
v___x_2967_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
v___jp_2871_:
{
if (v___y_2881_ == 0)
{
if (lean_obj_tag(v___y_2878_) == 0)
{
lean_dec_ref_known(v___y_2878_, 2);
lean_dec_ref(v___y_2877_);
lean_dec(v_a_2870_);
return v___y_2880_;
}
else
{
lean_object* v_id_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2895_; 
v_id_2882_ = lean_ctor_get(v___y_2878_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___y_2878_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; 
v_unused_2896_ = lean_ctor_get(v___y_2878_, 1);
lean_dec(v_unused_2896_);
v___x_2884_ = v___y_2878_;
v_isShared_2885_ = v_isSharedCheck_2895_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_id_2882_);
lean_dec(v___y_2878_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2895_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
uint8_t v___x_2886_; 
v___x_2886_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2872_, v_id_2882_);
lean_dec(v_id_2882_);
if (v___x_2886_ == 0)
{
lean_del_object(v___x_2884_);
lean_dec_ref(v___y_2877_);
lean_dec(v_a_2870_);
return v___y_2880_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec_ref(v___y_2880_);
v___x_2887_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_2888_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_2889_ = l_Lean_indentExpr(v_a_2870_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set_tag(v___x_2884_, 7);
lean_ctor_set(v___x_2884_, 1, v___x_2889_);
lean_ctor_set(v___x_2884_, 0, v___x_2888_);
v___x_2891_ = v___x_2884_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2887_);
v___x_2893_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2892_, v___y_2879_, v___y_2875_, v___y_2874_, v___y_2876_, v___y_2877_, v___y_2873_);
lean_dec_ref(v___y_2877_);
return v___x_2893_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_a_2870_);
return v___y_2880_;
}
}
v___jp_2897_:
{
lean_object* v___x_2904_; 
lean_inc(v_a_2870_);
v___x_2904_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_2870_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_dec_ref(v___y_2902_);
lean_dec(v_a_2870_);
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
v___x_2906_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2907_ = l_Lean_Exception_isInterrupt(v_a_2905_);
if (v___x_2907_ == 0)
{
uint8_t v___x_2908_; 
lean_inc(v_a_2905_);
v___x_2908_ = l_Lean_Exception_isRuntime(v_a_2905_);
v___y_2872_ = v___x_2906_;
v___y_2873_ = v___y_2903_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v_a_2905_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___x_2904_;
v___y_2881_ = v___x_2908_;
goto v___jp_2871_;
}
else
{
v___y_2872_ = v___x_2906_;
v___y_2873_ = v___y_2903_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2901_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v_a_2905_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___x_2904_;
v___y_2881_ = v___x_2907_;
goto v___jp_2871_;
}
}
}
v___jp_2909_:
{
lean_object* v___x_2916_; 
lean_inc(v_a_2870_);
v___x_2916_ = l_Lean_Meta_getMVars(v_a_2870_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2918_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2917_, v___x_2844_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v_a_2917_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; uint8_t v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = lean_unbox(v_a_2919_);
lean_dec(v_a_2919_);
if (v___x_2920_ == 0)
{
v___y_2898_ = v___y_2910_;
v___y_2899_ = v___y_2911_;
v___y_2900_ = v___y_2912_;
v___y_2901_ = v___y_2913_;
v___y_2902_ = v___y_2914_;
v___y_2903_ = v___y_2915_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v___y_2914_);
lean_dec(v_a_2870_);
v___x_2921_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___y_2914_);
lean_dec(v_a_2870_);
v_a_2930_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2918_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2918_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v___y_2914_);
lean_dec(v_a_2870_);
v_a_2938_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2916_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2916_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
v___jp_2946_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
v___x_2953_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_2954_ = l_Lean_indentExpr(v_a_2870_);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2955_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec_ref(v___y_2951_);
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref_known(v___x_2866_, 14);
v_a_2976_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2867_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2867_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_fileName_3001_; lean_object* v_fileMap_3002_; lean_object* v_options_3003_; lean_object* v_currRecDepth_3004_; lean_object* v_maxRecDepth_3005_; lean_object* v_ref_3006_; lean_object* v_currNamespace_3007_; lean_object* v_openDecls_3008_; lean_object* v_initHeartbeats_3009_; lean_object* v_maxHeartbeats_3010_; lean_object* v_quotContext_3011_; lean_object* v_currMacroScope_3012_; uint8_t v_diag_3013_; lean_object* v_cancelTk_x3f_3014_; uint8_t v_suppressElabErrors_3015_; lean_object* v_inheritedTraceOptions_3016_; lean_object* v_ref_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_fileName_3001_ = lean_ctor_get(v_a_2998_, 0);
v_fileMap_3002_ = lean_ctor_get(v_a_2998_, 1);
v_options_3003_ = lean_ctor_get(v_a_2998_, 2);
v_currRecDepth_3004_ = lean_ctor_get(v_a_2998_, 3);
v_maxRecDepth_3005_ = lean_ctor_get(v_a_2998_, 4);
v_ref_3006_ = lean_ctor_get(v_a_2998_, 5);
v_currNamespace_3007_ = lean_ctor_get(v_a_2998_, 6);
v_openDecls_3008_ = lean_ctor_get(v_a_2998_, 7);
v_initHeartbeats_3009_ = lean_ctor_get(v_a_2998_, 8);
v_maxHeartbeats_3010_ = lean_ctor_get(v_a_2998_, 9);
v_quotContext_3011_ = lean_ctor_get(v_a_2998_, 10);
v_currMacroScope_3012_ = lean_ctor_get(v_a_2998_, 11);
v_diag_3013_ = lean_ctor_get_uint8(v_a_2998_, sizeof(void*)*14);
v_cancelTk_x3f_3014_ = lean_ctor_get(v_a_2998_, 12);
v_suppressElabErrors_3015_ = lean_ctor_get_uint8(v_a_2998_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3016_ = lean_ctor_get(v_a_2998_, 13);
v_ref_3017_ = l_Lean_replaceRef(v_stx_2993_, v_ref_3006_);
lean_inc_ref(v_inheritedTraceOptions_3016_);
lean_inc(v_cancelTk_x3f_3014_);
lean_inc(v_currMacroScope_3012_);
lean_inc(v_quotContext_3011_);
lean_inc(v_maxHeartbeats_3010_);
lean_inc(v_initHeartbeats_3009_);
lean_inc(v_openDecls_3008_);
lean_inc(v_currNamespace_3007_);
lean_inc(v_maxRecDepth_3005_);
lean_inc(v_currRecDepth_3004_);
lean_inc_ref(v_options_3003_);
lean_inc_ref(v_fileMap_3002_);
lean_inc_ref(v_fileName_3001_);
v___x_3018_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3018_, 0, v_fileName_3001_);
lean_ctor_set(v___x_3018_, 1, v_fileMap_3002_);
lean_ctor_set(v___x_3018_, 2, v_options_3003_);
lean_ctor_set(v___x_3018_, 3, v_currRecDepth_3004_);
lean_ctor_set(v___x_3018_, 4, v_maxRecDepth_3005_);
lean_ctor_set(v___x_3018_, 5, v_ref_3017_);
lean_ctor_set(v___x_3018_, 6, v_currNamespace_3007_);
lean_ctor_set(v___x_3018_, 7, v_openDecls_3008_);
lean_ctor_set(v___x_3018_, 8, v_initHeartbeats_3009_);
lean_ctor_set(v___x_3018_, 9, v_maxHeartbeats_3010_);
lean_ctor_set(v___x_3018_, 10, v_quotContext_3011_);
lean_ctor_set(v___x_3018_, 11, v_currMacroScope_3012_);
lean_ctor_set(v___x_3018_, 12, v_cancelTk_x3f_3014_);
lean_ctor_set(v___x_3018_, 13, v_inheritedTraceOptions_3016_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*14, v_diag_3013_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*14 + 1, v_suppressElabErrors_3015_);
lean_inc(v_stx_2993_);
v___x_3019_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v___x_3018_, v_a_2999_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref_known(v___x_3018_, 14);
lean_dec(v_stx_2993_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_fst_3024_; lean_object* v___x_3026_; 
v_fst_3024_ = lean_ctor_get(v_a_3020_, 0);
lean_inc(v_fst_3024_);
lean_dec(v_a_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v_fst_3024_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_fst_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3044_; 
v_a_3029_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3031_ = v___x_3019_;
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3019_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3033_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3029_);
if (v_isShared_3032_ == 0)
{
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3029_);
v___x_3035_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
uint8_t v___y_3037_; uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Exception_isInterrupt(v_a_3029_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
lean_inc(v_a_3029_);
v___x_3042_ = l_Lean_Exception_isRuntime(v_a_3029_);
v___y_3037_ = v___x_3042_;
goto v___jp_3036_;
}
else
{
v___y_3037_ = v___x_3041_;
goto v___jp_3036_;
}
v___jp_3036_:
{
if (v___y_3037_ == 0)
{
if (lean_obj_tag(v_a_3029_) == 0)
{
lean_dec_ref_known(v_a_3029_, 2);
lean_dec_ref_known(v___x_3018_, 14);
lean_dec(v_stx_2993_);
return v___x_3035_;
}
else
{
lean_object* v_id_3038_; uint8_t v___x_3039_; 
v_id_3038_ = lean_ctor_get(v_a_3029_, 0);
lean_inc(v_id_3038_);
lean_dec_ref_known(v_a_3029_, 2);
v___x_3039_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3033_, v_id_3038_);
lean_dec(v_id_3038_);
if (v___x_3039_ == 0)
{
lean_dec_ref_known(v___x_3018_, 14);
lean_dec(v_stx_2993_);
return v___x_3035_;
}
else
{
lean_object* v___x_3040_; 
lean_dec_ref(v___x_3035_);
v___x_3040_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v___x_3018_, v_a_2999_);
lean_dec_ref_known(v___x_3018_, 14);
return v___x_3040_;
}
}
}
else
{
lean_dec(v_a_3029_);
lean_dec_ref_known(v___x_3018_, 14);
lean_dec(v_stx_2993_);
return v___x_3035_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
return v_res_3053_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_box(0);
v___x_3060_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3061_ = l_Lean_Expr_const___override(v___x_3060_, v___x_3059_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3062_; lean_object* v_ty_x3f_3063_; 
v___x_3062_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3063_, 0, v___x_3062_);
return v_ty_x3f_3063_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3065_ = l_Lean_MessageData_ofExpr(v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3067_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3070_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_ty_x3f_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_fileName_3086_; lean_object* v_fileMap_3087_; lean_object* v_options_3088_; lean_object* v_currRecDepth_3089_; lean_object* v_maxRecDepth_3090_; lean_object* v_ref_3091_; lean_object* v_currNamespace_3092_; lean_object* v_openDecls_3093_; lean_object* v_initHeartbeats_3094_; lean_object* v_maxHeartbeats_3095_; lean_object* v_quotContext_3096_; lean_object* v_currMacroScope_3097_; uint8_t v_diag_3098_; lean_object* v_cancelTk_x3f_3099_; uint8_t v_suppressElabErrors_3100_; lean_object* v_inheritedTraceOptions_3101_; uint8_t v___x_3102_; lean_object* v_ref_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_ty_x3f_3080_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3081_ = 1;
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_box(v___x_3081_);
v___x_3084_ = lean_box(v___x_3081_);
lean_inc(v_stx_3072_);
v___x_3085_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3085_, 0, v_stx_3072_);
lean_closure_set(v___x_3085_, 1, v_ty_x3f_3080_);
lean_closure_set(v___x_3085_, 2, v___x_3083_);
lean_closure_set(v___x_3085_, 3, v___x_3084_);
lean_closure_set(v___x_3085_, 4, v___x_3082_);
v_fileName_3086_ = lean_ctor_get(v_a_3077_, 0);
v_fileMap_3087_ = lean_ctor_get(v_a_3077_, 1);
v_options_3088_ = lean_ctor_get(v_a_3077_, 2);
v_currRecDepth_3089_ = lean_ctor_get(v_a_3077_, 3);
v_maxRecDepth_3090_ = lean_ctor_get(v_a_3077_, 4);
v_ref_3091_ = lean_ctor_get(v_a_3077_, 5);
v_currNamespace_3092_ = lean_ctor_get(v_a_3077_, 6);
v_openDecls_3093_ = lean_ctor_get(v_a_3077_, 7);
v_initHeartbeats_3094_ = lean_ctor_get(v_a_3077_, 8);
v_maxHeartbeats_3095_ = lean_ctor_get(v_a_3077_, 9);
v_quotContext_3096_ = lean_ctor_get(v_a_3077_, 10);
v_currMacroScope_3097_ = lean_ctor_get(v_a_3077_, 11);
v_diag_3098_ = lean_ctor_get_uint8(v_a_3077_, sizeof(void*)*14);
v_cancelTk_x3f_3099_ = lean_ctor_get(v_a_3077_, 12);
v_suppressElabErrors_3100_ = lean_ctor_get_uint8(v_a_3077_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3101_ = lean_ctor_get(v_a_3077_, 13);
v___x_3102_ = 1;
v_ref_3103_ = l_Lean_replaceRef(v_stx_3072_, v_ref_3091_);
lean_dec(v_stx_3072_);
lean_inc_ref(v_inheritedTraceOptions_3101_);
lean_inc(v_cancelTk_x3f_3099_);
lean_inc(v_currMacroScope_3097_);
lean_inc(v_quotContext_3096_);
lean_inc(v_maxHeartbeats_3095_);
lean_inc(v_initHeartbeats_3094_);
lean_inc(v_openDecls_3093_);
lean_inc(v_currNamespace_3092_);
lean_inc(v_maxRecDepth_3090_);
lean_inc(v_currRecDepth_3089_);
lean_inc_ref(v_options_3088_);
lean_inc_ref(v_fileMap_3087_);
lean_inc_ref(v_fileName_3086_);
v___x_3104_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3104_, 0, v_fileName_3086_);
lean_ctor_set(v___x_3104_, 1, v_fileMap_3087_);
lean_ctor_set(v___x_3104_, 2, v_options_3088_);
lean_ctor_set(v___x_3104_, 3, v_currRecDepth_3089_);
lean_ctor_set(v___x_3104_, 4, v_maxRecDepth_3090_);
lean_ctor_set(v___x_3104_, 5, v_ref_3103_);
lean_ctor_set(v___x_3104_, 6, v_currNamespace_3092_);
lean_ctor_set(v___x_3104_, 7, v_openDecls_3093_);
lean_ctor_set(v___x_3104_, 8, v_initHeartbeats_3094_);
lean_ctor_set(v___x_3104_, 9, v_maxHeartbeats_3095_);
lean_ctor_set(v___x_3104_, 10, v_quotContext_3096_);
lean_ctor_set(v___x_3104_, 11, v_currMacroScope_3097_);
lean_ctor_set(v___x_3104_, 12, v_cancelTk_x3f_3099_);
lean_ctor_set(v___x_3104_, 13, v_inheritedTraceOptions_3101_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*14, v_diag_3098_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*14 + 1, v_suppressElabErrors_3100_);
v___x_3105_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3085_, v___x_3102_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v___x_3104_, v_a_3078_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; lean_object* v_a_3108_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___x_3203_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3106_, v_a_3076_);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v___x_3107_);
v___x_3203_ = l_Lean_Expr_hasSorry(v_a_3108_);
if (v___x_3203_ == 0)
{
v___y_3148_ = v_a_3073_;
v___y_3149_ = v_a_3074_;
v___y_3150_ = v_a_3075_;
v___y_3151_ = v_a_3076_;
v___y_3152_ = v___x_3104_;
v___y_3153_ = v_a_3078_;
goto v___jp_3147_;
}
else
{
uint8_t v___x_3204_; 
v___x_3204_ = l_Lean_Expr_hasSyntheticSorry(v_a_3108_);
if (v___x_3204_ == 0)
{
v___y_3185_ = v_a_3073_;
v___y_3186_ = v_a_3074_;
v___y_3187_ = v_a_3075_;
v___y_3188_ = v_a_3076_;
v___y_3189_ = v___x_3104_;
v___y_3190_ = v_a_3078_;
goto v___jp_3184_;
}
else
{
lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_3108_);
lean_dec_ref_known(v___x_3104_, 14);
v___x_3205_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3109_:
{
if (v___y_3119_ == 0)
{
if (lean_obj_tag(v___y_3115_) == 0)
{
lean_dec_ref_known(v___y_3115_, 2);
lean_dec_ref(v___y_3114_);
lean_dec(v_a_3108_);
return v___y_3112_;
}
else
{
lean_object* v_id_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3133_; 
v_id_3120_ = lean_ctor_get(v___y_3115_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___y_3115_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___y_3115_, 1);
lean_dec(v_unused_3134_);
v___x_3122_ = v___y_3115_;
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_id_3120_);
lean_dec(v___y_3115_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
uint8_t v___x_3124_; 
v___x_3124_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3116_, v_id_3120_);
lean_dec(v_id_3120_);
if (v___x_3124_ == 0)
{
lean_del_object(v___x_3122_);
lean_dec_ref(v___y_3114_);
lean_dec(v_a_3108_);
return v___y_3112_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec_ref(v___y_3112_);
v___x_3125_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3126_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3127_ = l_Lean_indentExpr(v_a_3108_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 7);
lean_ctor_set(v___x_3122_, 1, v___x_3127_);
lean_ctor_set(v___x_3122_, 0, v___x_3126_);
v___x_3129_ = v___x_3122_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___x_3125_);
v___x_3131_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3130_, v___y_3118_, v___y_3113_, v___y_3111_, v___y_3110_, v___y_3114_, v___y_3117_);
lean_dec_ref(v___y_3114_);
return v___x_3131_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v_a_3108_);
return v___y_3112_;
}
}
v___jp_3135_:
{
lean_object* v___x_3142_; 
lean_inc(v_a_3108_);
v___x_3142_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3108_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_dec_ref(v___y_3140_);
lean_dec(v_a_3108_);
return v___x_3142_;
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
v___x_3144_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3145_ = l_Lean_Exception_isInterrupt(v_a_3143_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
lean_inc(v_a_3143_);
v___x_3146_ = l_Lean_Exception_isRuntime(v_a_3143_);
v___y_3110_ = v___y_3139_;
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3142_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v_a_3143_;
v___y_3116_ = v___x_3144_;
v___y_3117_ = v___y_3141_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___x_3146_;
goto v___jp_3109_;
}
else
{
v___y_3110_ = v___y_3139_;
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3142_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3140_;
v___y_3115_ = v_a_3143_;
v___y_3116_ = v___x_3144_;
v___y_3117_ = v___y_3141_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___x_3145_;
goto v___jp_3109_;
}
}
}
v___jp_3147_:
{
lean_object* v___x_3154_; 
lean_inc(v_a_3108_);
v___x_3154_ = l_Lean_Meta_getMVars(v_a_3108_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3155_, v___x_3082_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v_a_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; uint8_t v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = lean_unbox(v_a_3157_);
lean_dec(v_a_3157_);
if (v___x_3158_ == 0)
{
v___y_3136_ = v___y_3148_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v___y_3150_;
v___y_3139_ = v___y_3151_;
v___y_3140_ = v___y_3152_;
v___y_3141_ = v___y_3153_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v___y_3152_);
lean_dec(v_a_3108_);
v___x_3159_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___y_3152_);
lean_dec(v_a_3108_);
v_a_3168_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3156_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3156_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v___y_3152_);
lean_dec(v_a_3108_);
v_a_3176_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3154_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3154_);
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
v___jp_3184_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v___x_3191_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3192_ = l_Lean_indentExpr(v_a_3108_);
v___x_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3193_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec_ref(v___y_3189_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref_known(v___x_3104_, 14);
v_a_3214_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3105_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3105_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_fileName_3239_; lean_object* v_fileMap_3240_; lean_object* v_options_3241_; lean_object* v_currRecDepth_3242_; lean_object* v_maxRecDepth_3243_; lean_object* v_ref_3244_; lean_object* v_currNamespace_3245_; lean_object* v_openDecls_3246_; lean_object* v_initHeartbeats_3247_; lean_object* v_maxHeartbeats_3248_; lean_object* v_quotContext_3249_; lean_object* v_currMacroScope_3250_; uint8_t v_diag_3251_; lean_object* v_cancelTk_x3f_3252_; uint8_t v_suppressElabErrors_3253_; lean_object* v_inheritedTraceOptions_3254_; lean_object* v_ref_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_fileName_3239_ = lean_ctor_get(v_a_3236_, 0);
v_fileMap_3240_ = lean_ctor_get(v_a_3236_, 1);
v_options_3241_ = lean_ctor_get(v_a_3236_, 2);
v_currRecDepth_3242_ = lean_ctor_get(v_a_3236_, 3);
v_maxRecDepth_3243_ = lean_ctor_get(v_a_3236_, 4);
v_ref_3244_ = lean_ctor_get(v_a_3236_, 5);
v_currNamespace_3245_ = lean_ctor_get(v_a_3236_, 6);
v_openDecls_3246_ = lean_ctor_get(v_a_3236_, 7);
v_initHeartbeats_3247_ = lean_ctor_get(v_a_3236_, 8);
v_maxHeartbeats_3248_ = lean_ctor_get(v_a_3236_, 9);
v_quotContext_3249_ = lean_ctor_get(v_a_3236_, 10);
v_currMacroScope_3250_ = lean_ctor_get(v_a_3236_, 11);
v_diag_3251_ = lean_ctor_get_uint8(v_a_3236_, sizeof(void*)*14);
v_cancelTk_x3f_3252_ = lean_ctor_get(v_a_3236_, 12);
v_suppressElabErrors_3253_ = lean_ctor_get_uint8(v_a_3236_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3254_ = lean_ctor_get(v_a_3236_, 13);
v_ref_3255_ = l_Lean_replaceRef(v_stx_3231_, v_ref_3244_);
lean_inc_ref(v_inheritedTraceOptions_3254_);
lean_inc(v_cancelTk_x3f_3252_);
lean_inc(v_currMacroScope_3250_);
lean_inc(v_quotContext_3249_);
lean_inc(v_maxHeartbeats_3248_);
lean_inc(v_initHeartbeats_3247_);
lean_inc(v_openDecls_3246_);
lean_inc(v_currNamespace_3245_);
lean_inc(v_maxRecDepth_3243_);
lean_inc(v_currRecDepth_3242_);
lean_inc_ref(v_options_3241_);
lean_inc_ref(v_fileMap_3240_);
lean_inc_ref(v_fileName_3239_);
v___x_3256_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3256_, 0, v_fileName_3239_);
lean_ctor_set(v___x_3256_, 1, v_fileMap_3240_);
lean_ctor_set(v___x_3256_, 2, v_options_3241_);
lean_ctor_set(v___x_3256_, 3, v_currRecDepth_3242_);
lean_ctor_set(v___x_3256_, 4, v_maxRecDepth_3243_);
lean_ctor_set(v___x_3256_, 5, v_ref_3255_);
lean_ctor_set(v___x_3256_, 6, v_currNamespace_3245_);
lean_ctor_set(v___x_3256_, 7, v_openDecls_3246_);
lean_ctor_set(v___x_3256_, 8, v_initHeartbeats_3247_);
lean_ctor_set(v___x_3256_, 9, v_maxHeartbeats_3248_);
lean_ctor_set(v___x_3256_, 10, v_quotContext_3249_);
lean_ctor_set(v___x_3256_, 11, v_currMacroScope_3250_);
lean_ctor_set(v___x_3256_, 12, v_cancelTk_x3f_3252_);
lean_ctor_set(v___x_3256_, 13, v_inheritedTraceOptions_3254_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*14, v_diag_3251_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*14 + 1, v_suppressElabErrors_3253_);
lean_inc(v_stx_3231_);
v___x_3257_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v___x_3256_, v_a_3237_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3266_; 
lean_dec_ref_known(v___x_3256_, 14);
lean_dec(v_stx_3231_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_fst_3262_; lean_object* v___x_3264_; 
v_fst_3262_ = lean_ctor_get(v_a_3258_, 0);
lean_inc(v_fst_3262_);
lean_dec(v_a_3258_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v_fst_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_fst_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3282_; 
v_a_3267_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3269_ = v___x_3257_;
v_isShared_3270_ = v_isSharedCheck_3282_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3257_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3282_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3267_);
if (v_isShared_3270_ == 0)
{
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3267_);
v___x_3273_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
uint8_t v___y_3275_; uint8_t v___x_3279_; 
v___x_3279_ = l_Lean_Exception_isInterrupt(v_a_3267_);
if (v___x_3279_ == 0)
{
uint8_t v___x_3280_; 
lean_inc(v_a_3267_);
v___x_3280_ = l_Lean_Exception_isRuntime(v_a_3267_);
v___y_3275_ = v___x_3280_;
goto v___jp_3274_;
}
else
{
v___y_3275_ = v___x_3279_;
goto v___jp_3274_;
}
v___jp_3274_:
{
if (v___y_3275_ == 0)
{
if (lean_obj_tag(v_a_3267_) == 0)
{
lean_dec_ref_known(v_a_3267_, 2);
lean_dec_ref_known(v___x_3256_, 14);
lean_dec(v_stx_3231_);
return v___x_3273_;
}
else
{
lean_object* v_id_3276_; uint8_t v___x_3277_; 
v_id_3276_ = lean_ctor_get(v_a_3267_, 0);
lean_inc(v_id_3276_);
lean_dec_ref_known(v_a_3267_, 2);
v___x_3277_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3271_, v_id_3276_);
lean_dec(v_id_3276_);
if (v___x_3277_ == 0)
{
lean_dec_ref_known(v___x_3256_, 14);
lean_dec(v_stx_3231_);
return v___x_3273_;
}
else
{
lean_object* v___x_3278_; 
lean_dec_ref(v___x_3273_);
v___x_3278_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v___x_3256_, v_a_3237_);
lean_dec_ref_known(v___x_3256_, 14);
return v___x_3278_;
}
}
}
else
{
lean_dec(v_a_3267_);
lean_dec_ref_known(v___x_3256_, 14);
lean_dec(v_stx_3231_);
return v___x_3273_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3293_ = l_Lean_MessageData_ofExpr(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3295_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___x_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3298_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v___x_3297_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_ty_x3f_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_fileName_3314_; lean_object* v_fileMap_3315_; lean_object* v_options_3316_; lean_object* v_currRecDepth_3317_; lean_object* v_maxRecDepth_3318_; lean_object* v_ref_3319_; lean_object* v_currNamespace_3320_; lean_object* v_openDecls_3321_; lean_object* v_initHeartbeats_3322_; lean_object* v_maxHeartbeats_3323_; lean_object* v_quotContext_3324_; lean_object* v_currMacroScope_3325_; uint8_t v_diag_3326_; lean_object* v_cancelTk_x3f_3327_; uint8_t v_suppressElabErrors_3328_; lean_object* v_inheritedTraceOptions_3329_; uint8_t v___x_3330_; lean_object* v_ref_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_ty_x3f_3308_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3309_ = 1;
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_box(v___x_3309_);
v___x_3312_ = lean_box(v___x_3309_);
lean_inc(v_stx_3300_);
v___x_3313_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3313_, 0, v_stx_3300_);
lean_closure_set(v___x_3313_, 1, v_ty_x3f_3308_);
lean_closure_set(v___x_3313_, 2, v___x_3311_);
lean_closure_set(v___x_3313_, 3, v___x_3312_);
lean_closure_set(v___x_3313_, 4, v___x_3310_);
v_fileName_3314_ = lean_ctor_get(v_a_3305_, 0);
v_fileMap_3315_ = lean_ctor_get(v_a_3305_, 1);
v_options_3316_ = lean_ctor_get(v_a_3305_, 2);
v_currRecDepth_3317_ = lean_ctor_get(v_a_3305_, 3);
v_maxRecDepth_3318_ = lean_ctor_get(v_a_3305_, 4);
v_ref_3319_ = lean_ctor_get(v_a_3305_, 5);
v_currNamespace_3320_ = lean_ctor_get(v_a_3305_, 6);
v_openDecls_3321_ = lean_ctor_get(v_a_3305_, 7);
v_initHeartbeats_3322_ = lean_ctor_get(v_a_3305_, 8);
v_maxHeartbeats_3323_ = lean_ctor_get(v_a_3305_, 9);
v_quotContext_3324_ = lean_ctor_get(v_a_3305_, 10);
v_currMacroScope_3325_ = lean_ctor_get(v_a_3305_, 11);
v_diag_3326_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*14);
v_cancelTk_x3f_3327_ = lean_ctor_get(v_a_3305_, 12);
v_suppressElabErrors_3328_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3329_ = lean_ctor_get(v_a_3305_, 13);
v___x_3330_ = 1;
v_ref_3331_ = l_Lean_replaceRef(v_stx_3300_, v_ref_3319_);
lean_dec(v_stx_3300_);
lean_inc_ref(v_inheritedTraceOptions_3329_);
lean_inc(v_cancelTk_x3f_3327_);
lean_inc(v_currMacroScope_3325_);
lean_inc(v_quotContext_3324_);
lean_inc(v_maxHeartbeats_3323_);
lean_inc(v_initHeartbeats_3322_);
lean_inc(v_openDecls_3321_);
lean_inc(v_currNamespace_3320_);
lean_inc(v_maxRecDepth_3318_);
lean_inc(v_currRecDepth_3317_);
lean_inc_ref(v_options_3316_);
lean_inc_ref(v_fileMap_3315_);
lean_inc_ref(v_fileName_3314_);
v___x_3332_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3332_, 0, v_fileName_3314_);
lean_ctor_set(v___x_3332_, 1, v_fileMap_3315_);
lean_ctor_set(v___x_3332_, 2, v_options_3316_);
lean_ctor_set(v___x_3332_, 3, v_currRecDepth_3317_);
lean_ctor_set(v___x_3332_, 4, v_maxRecDepth_3318_);
lean_ctor_set(v___x_3332_, 5, v_ref_3331_);
lean_ctor_set(v___x_3332_, 6, v_currNamespace_3320_);
lean_ctor_set(v___x_3332_, 7, v_openDecls_3321_);
lean_ctor_set(v___x_3332_, 8, v_initHeartbeats_3322_);
lean_ctor_set(v___x_3332_, 9, v_maxHeartbeats_3323_);
lean_ctor_set(v___x_3332_, 10, v_quotContext_3324_);
lean_ctor_set(v___x_3332_, 11, v_currMacroScope_3325_);
lean_ctor_set(v___x_3332_, 12, v_cancelTk_x3f_3327_);
lean_ctor_set(v___x_3332_, 13, v_inheritedTraceOptions_3329_);
lean_ctor_set_uint8(v___x_3332_, sizeof(void*)*14, v_diag_3326_);
lean_ctor_set_uint8(v___x_3332_, sizeof(void*)*14 + 1, v_suppressElabErrors_3328_);
v___x_3333_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3313_, v___x_3330_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v___x_3332_, v_a_3306_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; lean_object* v_a_3336_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___x_3431_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3334_, v_a_3304_);
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v___x_3431_ = l_Lean_Expr_hasSorry(v_a_3336_);
if (v___x_3431_ == 0)
{
v___y_3376_ = v_a_3301_;
v___y_3377_ = v_a_3302_;
v___y_3378_ = v_a_3303_;
v___y_3379_ = v_a_3304_;
v___y_3380_ = v___x_3332_;
v___y_3381_ = v_a_3306_;
goto v___jp_3375_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = l_Lean_Expr_hasSyntheticSorry(v_a_3336_);
if (v___x_3432_ == 0)
{
v___y_3413_ = v_a_3301_;
v___y_3414_ = v_a_3302_;
v___y_3415_ = v_a_3303_;
v___y_3416_ = v_a_3304_;
v___y_3417_ = v___x_3332_;
v___y_3418_ = v_a_3306_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3433_; lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v_a_3336_);
lean_dec_ref_known(v___x_3332_, 14);
v___x_3433_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
v___jp_3337_:
{
if (v___y_3347_ == 0)
{
if (lean_obj_tag(v___y_3346_) == 0)
{
lean_dec_ref_known(v___y_3346_, 2);
lean_dec_ref(v___y_3338_);
lean_dec(v_a_3336_);
return v___y_3341_;
}
else
{
lean_object* v_id_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3361_; 
v_id_3348_ = lean_ctor_get(v___y_3346_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___y_3346_);
if (v_isSharedCheck_3361_ == 0)
{
lean_object* v_unused_3362_; 
v_unused_3362_ = lean_ctor_get(v___y_3346_, 1);
lean_dec(v_unused_3362_);
v___x_3350_ = v___y_3346_;
v_isShared_3351_ = v_isSharedCheck_3361_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_id_3348_);
lean_dec(v___y_3346_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3361_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
uint8_t v___x_3352_; 
v___x_3352_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3345_, v_id_3348_);
lean_dec(v_id_3348_);
if (v___x_3352_ == 0)
{
lean_del_object(v___x_3350_);
lean_dec_ref(v___y_3338_);
lean_dec(v_a_3336_);
return v___y_3341_;
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
lean_dec_ref(v___y_3341_);
v___x_3353_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3354_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3355_ = l_Lean_indentExpr(v_a_3336_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 7);
lean_ctor_set(v___x_3350_, 1, v___x_3355_);
lean_ctor_set(v___x_3350_, 0, v___x_3354_);
v___x_3357_ = v___x_3350_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___x_3353_);
v___x_3359_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3358_, v___y_3344_, v___y_3343_, v___y_3339_, v___y_3340_, v___y_3338_, v___y_3342_);
lean_dec_ref(v___y_3338_);
return v___x_3359_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3346_);
lean_dec_ref(v___y_3338_);
lean_dec(v_a_3336_);
return v___y_3341_;
}
}
v___jp_3363_:
{
lean_object* v___x_3370_; 
lean_inc(v_a_3336_);
v___x_3370_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3336_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_dec_ref(v___y_3368_);
lean_dec(v_a_3336_);
return v___x_3370_;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
v___x_3372_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3373_ = l_Lean_Exception_isInterrupt(v_a_3371_);
if (v___x_3373_ == 0)
{
uint8_t v___x_3374_; 
lean_inc(v_a_3371_);
v___x_3374_ = l_Lean_Exception_isRuntime(v_a_3371_);
v___y_3338_ = v___y_3368_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___y_3367_;
v___y_3341_ = v___x_3370_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v___y_3364_;
v___y_3345_ = v___x_3372_;
v___y_3346_ = v_a_3371_;
v___y_3347_ = v___x_3374_;
goto v___jp_3337_;
}
else
{
v___y_3338_ = v___y_3368_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___y_3367_;
v___y_3341_ = v___x_3370_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v___y_3364_;
v___y_3345_ = v___x_3372_;
v___y_3346_ = v_a_3371_;
v___y_3347_ = v___x_3373_;
goto v___jp_3337_;
}
}
}
v___jp_3375_:
{
lean_object* v___x_3382_; 
lean_inc(v_a_3336_);
v___x_3382_ = l_Lean_Meta_getMVars(v_a_3336_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3383_, v___x_3310_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v_a_3383_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; uint8_t v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = lean_unbox(v_a_3385_);
lean_dec(v_a_3385_);
if (v___x_3386_ == 0)
{
v___y_3364_ = v___y_3376_;
v___y_3365_ = v___y_3377_;
v___y_3366_ = v___y_3378_;
v___y_3367_ = v___y_3379_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3381_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3387_; lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___y_3380_);
lean_dec(v_a_3336_);
v___x_3387_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
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
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v___y_3380_);
lean_dec(v_a_3336_);
v_a_3396_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3384_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3384_);
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
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v___y_3380_);
lean_dec(v_a_3336_);
v_a_3404_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3382_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3382_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
v___jp_3412_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
v___x_3419_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3420_ = l_Lean_indentExpr(v_a_3336_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3421_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec_ref(v___y_3417_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref_known(v___x_3332_, 14);
v_a_3442_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3333_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3333_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3458_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3466_ = l_Lean_Expr_const___override(v___x_3465_, v___x_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3467_; lean_object* v_ty_x3f_3468_; 
v___x_3467_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3468_, 0, v___x_3467_);
return v_ty_x3f_3468_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3470_ = l_Lean_MessageData_ofExpr(v___x_3469_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3472_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3475_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v___x_3474_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_ty_x3f_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v_fileName_3491_; lean_object* v_fileMap_3492_; lean_object* v_options_3493_; lean_object* v_currRecDepth_3494_; lean_object* v_maxRecDepth_3495_; lean_object* v_ref_3496_; lean_object* v_currNamespace_3497_; lean_object* v_openDecls_3498_; lean_object* v_initHeartbeats_3499_; lean_object* v_maxHeartbeats_3500_; lean_object* v_quotContext_3501_; lean_object* v_currMacroScope_3502_; uint8_t v_diag_3503_; lean_object* v_cancelTk_x3f_3504_; uint8_t v_suppressElabErrors_3505_; lean_object* v_inheritedTraceOptions_3506_; uint8_t v___x_3507_; lean_object* v_ref_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_ty_x3f_3485_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3486_ = 1;
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_box(v___x_3486_);
v___x_3489_ = lean_box(v___x_3486_);
lean_inc(v_stx_3477_);
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3490_, 0, v_stx_3477_);
lean_closure_set(v___x_3490_, 1, v_ty_x3f_3485_);
lean_closure_set(v___x_3490_, 2, v___x_3488_);
lean_closure_set(v___x_3490_, 3, v___x_3489_);
lean_closure_set(v___x_3490_, 4, v___x_3487_);
v_fileName_3491_ = lean_ctor_get(v_a_3482_, 0);
v_fileMap_3492_ = lean_ctor_get(v_a_3482_, 1);
v_options_3493_ = lean_ctor_get(v_a_3482_, 2);
v_currRecDepth_3494_ = lean_ctor_get(v_a_3482_, 3);
v_maxRecDepth_3495_ = lean_ctor_get(v_a_3482_, 4);
v_ref_3496_ = lean_ctor_get(v_a_3482_, 5);
v_currNamespace_3497_ = lean_ctor_get(v_a_3482_, 6);
v_openDecls_3498_ = lean_ctor_get(v_a_3482_, 7);
v_initHeartbeats_3499_ = lean_ctor_get(v_a_3482_, 8);
v_maxHeartbeats_3500_ = lean_ctor_get(v_a_3482_, 9);
v_quotContext_3501_ = lean_ctor_get(v_a_3482_, 10);
v_currMacroScope_3502_ = lean_ctor_get(v_a_3482_, 11);
v_diag_3503_ = lean_ctor_get_uint8(v_a_3482_, sizeof(void*)*14);
v_cancelTk_x3f_3504_ = lean_ctor_get(v_a_3482_, 12);
v_suppressElabErrors_3505_ = lean_ctor_get_uint8(v_a_3482_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3506_ = lean_ctor_get(v_a_3482_, 13);
v___x_3507_ = 1;
v_ref_3508_ = l_Lean_replaceRef(v_stx_3477_, v_ref_3496_);
lean_dec(v_stx_3477_);
lean_inc_ref(v_inheritedTraceOptions_3506_);
lean_inc(v_cancelTk_x3f_3504_);
lean_inc(v_currMacroScope_3502_);
lean_inc(v_quotContext_3501_);
lean_inc(v_maxHeartbeats_3500_);
lean_inc(v_initHeartbeats_3499_);
lean_inc(v_openDecls_3498_);
lean_inc(v_currNamespace_3497_);
lean_inc(v_maxRecDepth_3495_);
lean_inc(v_currRecDepth_3494_);
lean_inc_ref(v_options_3493_);
lean_inc_ref(v_fileMap_3492_);
lean_inc_ref(v_fileName_3491_);
v___x_3509_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3509_, 0, v_fileName_3491_);
lean_ctor_set(v___x_3509_, 1, v_fileMap_3492_);
lean_ctor_set(v___x_3509_, 2, v_options_3493_);
lean_ctor_set(v___x_3509_, 3, v_currRecDepth_3494_);
lean_ctor_set(v___x_3509_, 4, v_maxRecDepth_3495_);
lean_ctor_set(v___x_3509_, 5, v_ref_3508_);
lean_ctor_set(v___x_3509_, 6, v_currNamespace_3497_);
lean_ctor_set(v___x_3509_, 7, v_openDecls_3498_);
lean_ctor_set(v___x_3509_, 8, v_initHeartbeats_3499_);
lean_ctor_set(v___x_3509_, 9, v_maxHeartbeats_3500_);
lean_ctor_set(v___x_3509_, 10, v_quotContext_3501_);
lean_ctor_set(v___x_3509_, 11, v_currMacroScope_3502_);
lean_ctor_set(v___x_3509_, 12, v_cancelTk_x3f_3504_);
lean_ctor_set(v___x_3509_, 13, v_inheritedTraceOptions_3506_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14, v_diag_3503_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14 + 1, v_suppressElabErrors_3505_);
v___x_3510_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3490_, v___x_3507_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v___x_3509_, v_a_3483_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v_a_3513_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; uint8_t v___x_3608_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3511_, v_a_3481_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref(v___x_3512_);
v___x_3608_ = l_Lean_Expr_hasSorry(v_a_3513_);
if (v___x_3608_ == 0)
{
v___y_3553_ = v_a_3478_;
v___y_3554_ = v_a_3479_;
v___y_3555_ = v_a_3480_;
v___y_3556_ = v_a_3481_;
v___y_3557_ = v___x_3509_;
v___y_3558_ = v_a_3483_;
goto v___jp_3552_;
}
else
{
uint8_t v___x_3609_; 
v___x_3609_ = l_Lean_Expr_hasSyntheticSorry(v_a_3513_);
if (v___x_3609_ == 0)
{
v___y_3590_ = v_a_3478_;
v___y_3591_ = v_a_3479_;
v___y_3592_ = v_a_3480_;
v___y_3593_ = v_a_3481_;
v___y_3594_ = v___x_3509_;
v___y_3595_ = v_a_3483_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_a_3513_);
lean_dec_ref_known(v___x_3509_, 14);
v___x_3610_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
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
v___jp_3514_:
{
if (v___y_3524_ == 0)
{
if (lean_obj_tag(v___y_3523_) == 0)
{
lean_dec_ref_known(v___y_3523_, 2);
lean_dec_ref(v___y_3517_);
lean_dec(v_a_3513_);
return v___y_3520_;
}
else
{
lean_object* v_id_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3538_; 
v_id_3525_ = lean_ctor_get(v___y_3523_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___y_3523_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___y_3523_, 1);
lean_dec(v_unused_3539_);
v___x_3527_ = v___y_3523_;
v_isShared_3528_ = v_isSharedCheck_3538_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_id_3525_);
lean_dec(v___y_3523_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3538_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
uint8_t v___x_3529_; 
v___x_3529_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3522_, v_id_3525_);
lean_dec(v_id_3525_);
if (v___x_3529_ == 0)
{
lean_del_object(v___x_3527_);
lean_dec_ref(v___y_3517_);
lean_dec(v_a_3513_);
return v___y_3520_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
lean_dec_ref(v___y_3520_);
v___x_3530_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3531_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3532_ = l_Lean_indentExpr(v_a_3513_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set_tag(v___x_3527_, 7);
lean_ctor_set(v___x_3527_, 1, v___x_3532_);
lean_ctor_set(v___x_3527_, 0, v___x_3531_);
v___x_3534_ = v___x_3527_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v___x_3530_);
v___x_3536_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3535_, v___y_3519_, v___y_3521_, v___y_3518_, v___y_3516_, v___y_3517_, v___y_3515_);
lean_dec_ref(v___y_3517_);
return v___x_3536_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3517_);
lean_dec(v_a_3513_);
return v___y_3520_;
}
}
v___jp_3540_:
{
lean_object* v___x_3547_; 
lean_inc(v_a_3513_);
v___x_3547_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3513_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref(v___y_3545_);
lean_dec(v_a_3513_);
return v___x_3547_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
v___x_3549_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3550_ = l_Lean_Exception_isInterrupt(v_a_3548_);
if (v___x_3550_ == 0)
{
uint8_t v___x_3551_; 
lean_inc(v_a_3548_);
v___x_3551_ = l_Lean_Exception_isRuntime(v_a_3548_);
v___y_3515_ = v___y_3546_;
v___y_3516_ = v___y_3544_;
v___y_3517_ = v___y_3545_;
v___y_3518_ = v___y_3543_;
v___y_3519_ = v___y_3541_;
v___y_3520_ = v___x_3547_;
v___y_3521_ = v___y_3542_;
v___y_3522_ = v___x_3549_;
v___y_3523_ = v_a_3548_;
v___y_3524_ = v___x_3551_;
goto v___jp_3514_;
}
else
{
v___y_3515_ = v___y_3546_;
v___y_3516_ = v___y_3544_;
v___y_3517_ = v___y_3545_;
v___y_3518_ = v___y_3543_;
v___y_3519_ = v___y_3541_;
v___y_3520_ = v___x_3547_;
v___y_3521_ = v___y_3542_;
v___y_3522_ = v___x_3549_;
v___y_3523_ = v_a_3548_;
v___y_3524_ = v___x_3550_;
goto v___jp_3514_;
}
}
}
v___jp_3552_:
{
lean_object* v___x_3559_; 
lean_inc(v_a_3513_);
v___x_3559_ = l_Lean_Meta_getMVars(v_a_3513_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3560_, v___x_3487_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v_a_3560_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; uint8_t v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = lean_unbox(v_a_3562_);
lean_dec(v_a_3562_);
if (v___x_3563_ == 0)
{
v___y_3541_ = v___y_3553_;
v___y_3542_ = v___y_3554_;
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3557_;
v___y_3546_ = v___y_3558_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3564_; lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v___y_3557_);
lean_dec(v_a_3513_);
v___x_3564_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec_ref(v___y_3557_);
lean_dec(v_a_3513_);
v_a_3573_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3561_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3561_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v___y_3557_);
lean_dec(v_a_3513_);
v_a_3581_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3559_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3559_);
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
v___jp_3589_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
v___x_3596_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3597_ = l_Lean_indentExpr(v_a_3513_);
v___x_3598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3598_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec_ref(v___y_3594_);
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref_known(v___x_3509_, 14);
v_a_3619_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3510_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3510_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_fileName_3644_; lean_object* v_fileMap_3645_; lean_object* v_options_3646_; lean_object* v_currRecDepth_3647_; lean_object* v_maxRecDepth_3648_; lean_object* v_ref_3649_; lean_object* v_currNamespace_3650_; lean_object* v_openDecls_3651_; lean_object* v_initHeartbeats_3652_; lean_object* v_maxHeartbeats_3653_; lean_object* v_quotContext_3654_; lean_object* v_currMacroScope_3655_; uint8_t v_diag_3656_; lean_object* v_cancelTk_x3f_3657_; uint8_t v_suppressElabErrors_3658_; lean_object* v_inheritedTraceOptions_3659_; lean_object* v_ref_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v_fileName_3644_ = lean_ctor_get(v_a_3641_, 0);
v_fileMap_3645_ = lean_ctor_get(v_a_3641_, 1);
v_options_3646_ = lean_ctor_get(v_a_3641_, 2);
v_currRecDepth_3647_ = lean_ctor_get(v_a_3641_, 3);
v_maxRecDepth_3648_ = lean_ctor_get(v_a_3641_, 4);
v_ref_3649_ = lean_ctor_get(v_a_3641_, 5);
v_currNamespace_3650_ = lean_ctor_get(v_a_3641_, 6);
v_openDecls_3651_ = lean_ctor_get(v_a_3641_, 7);
v_initHeartbeats_3652_ = lean_ctor_get(v_a_3641_, 8);
v_maxHeartbeats_3653_ = lean_ctor_get(v_a_3641_, 9);
v_quotContext_3654_ = lean_ctor_get(v_a_3641_, 10);
v_currMacroScope_3655_ = lean_ctor_get(v_a_3641_, 11);
v_diag_3656_ = lean_ctor_get_uint8(v_a_3641_, sizeof(void*)*14);
v_cancelTk_x3f_3657_ = lean_ctor_get(v_a_3641_, 12);
v_suppressElabErrors_3658_ = lean_ctor_get_uint8(v_a_3641_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3659_ = lean_ctor_get(v_a_3641_, 13);
v_ref_3660_ = l_Lean_replaceRef(v_stx_3636_, v_ref_3649_);
lean_inc_ref(v_inheritedTraceOptions_3659_);
lean_inc(v_cancelTk_x3f_3657_);
lean_inc(v_currMacroScope_3655_);
lean_inc(v_quotContext_3654_);
lean_inc(v_maxHeartbeats_3653_);
lean_inc(v_initHeartbeats_3652_);
lean_inc(v_openDecls_3651_);
lean_inc(v_currNamespace_3650_);
lean_inc(v_maxRecDepth_3648_);
lean_inc(v_currRecDepth_3647_);
lean_inc_ref(v_options_3646_);
lean_inc_ref(v_fileMap_3645_);
lean_inc_ref(v_fileName_3644_);
v___x_3661_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3661_, 0, v_fileName_3644_);
lean_ctor_set(v___x_3661_, 1, v_fileMap_3645_);
lean_ctor_set(v___x_3661_, 2, v_options_3646_);
lean_ctor_set(v___x_3661_, 3, v_currRecDepth_3647_);
lean_ctor_set(v___x_3661_, 4, v_maxRecDepth_3648_);
lean_ctor_set(v___x_3661_, 5, v_ref_3660_);
lean_ctor_set(v___x_3661_, 6, v_currNamespace_3650_);
lean_ctor_set(v___x_3661_, 7, v_openDecls_3651_);
lean_ctor_set(v___x_3661_, 8, v_initHeartbeats_3652_);
lean_ctor_set(v___x_3661_, 9, v_maxHeartbeats_3653_);
lean_ctor_set(v___x_3661_, 10, v_quotContext_3654_);
lean_ctor_set(v___x_3661_, 11, v_currMacroScope_3655_);
lean_ctor_set(v___x_3661_, 12, v_cancelTk_x3f_3657_);
lean_ctor_set(v___x_3661_, 13, v_inheritedTraceOptions_3659_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*14, v_diag_3656_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*14 + 1, v_suppressElabErrors_3658_);
lean_inc(v_stx_3636_);
v___x_3662_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v___x_3661_, v_a_3642_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
lean_dec_ref_known(v___x_3661_, 14);
lean_dec(v_stx_3636_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v_fst_3667_; lean_object* v___x_3669_; 
v_fst_3667_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_fst_3667_);
lean_dec(v_a_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_fst_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_fst_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3687_; 
v_a_3672_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3674_ = v___x_3662_;
v_isShared_3675_ = v_isSharedCheck_3687_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3662_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3687_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3672_);
if (v_isShared_3675_ == 0)
{
v___x_3678_ = v___x_3674_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3672_);
v___x_3678_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
uint8_t v___y_3680_; uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_Exception_isInterrupt(v_a_3672_);
if (v___x_3684_ == 0)
{
uint8_t v___x_3685_; 
lean_inc(v_a_3672_);
v___x_3685_ = l_Lean_Exception_isRuntime(v_a_3672_);
v___y_3680_ = v___x_3685_;
goto v___jp_3679_;
}
else
{
v___y_3680_ = v___x_3684_;
goto v___jp_3679_;
}
v___jp_3679_:
{
if (v___y_3680_ == 0)
{
if (lean_obj_tag(v_a_3672_) == 0)
{
lean_dec_ref_known(v_a_3672_, 2);
lean_dec_ref_known(v___x_3661_, 14);
lean_dec(v_stx_3636_);
return v___x_3678_;
}
else
{
lean_object* v_id_3681_; uint8_t v___x_3682_; 
v_id_3681_ = lean_ctor_get(v_a_3672_, 0);
lean_inc(v_id_3681_);
lean_dec_ref_known(v_a_3672_, 2);
v___x_3682_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3676_, v_id_3681_);
lean_dec(v_id_3681_);
if (v___x_3682_ == 0)
{
lean_dec_ref_known(v___x_3661_, 14);
lean_dec(v_stx_3636_);
return v___x_3678_;
}
else
{
lean_object* v___x_3683_; 
lean_dec_ref(v___x_3678_);
v___x_3683_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v___x_3661_, v_a_3642_);
lean_dec_ref_known(v___x_3661_, 14);
return v___x_3683_;
}
}
}
else
{
lean_dec(v_a_3672_);
lean_dec_ref_known(v___x_3661_, 14);
lean_dec(v_stx_3636_);
return v___x_3678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3728_, lean_object* v_item_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_item_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3748_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3729_, v___x_3747_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3748_) == 0)
{
uint8_t v___x_3749_; 
lean_dec_ref_known(v___x_3748_, 1);
v___x_3749_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3729_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3750_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3729_);
lean_inc_ref(v_item_3729_);
v___x_3751_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3729_);
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3753_ = lean_string_dec_eq(v___x_3750_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3755_ = lean_string_dec_eq(v___x_3750_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3757_ = lean_string_dec_eq(v___x_3750_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3759_ = lean_string_dec_eq(v___x_3750_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3761_ = lean_string_dec_eq(v___x_3750_, v___x_3760_);
lean_dec_ref(v___x_3750_);
if (v___x_3761_ == 0)
{
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3763_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3729_, v___x_3762_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3763_) == 0)
{
uint8_t v___x_3764_; 
lean_dec_ref_known(v___x_3763_, 1);
v___x_3764_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3751_);
if (v___x_3764_ == 0)
{
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3765_; 
lean_dec_ref(v___x_3751_);
lean_inc_ref(v_item_3729_);
v___x_3765_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_value_3766_; lean_object* v___x_3767_; 
lean_dec_ref_known(v___x_3765_, 1);
v_value_3766_ = lean_ctor_get(v_item_3729_, 2);
lean_inc(v_value_3766_);
lean_dec_ref(v_item_3729_);
v___x_3767_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3766_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3786_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3786_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3786_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
uint8_t v_offsetCnstrs_3772_; lean_object* v_occs_3773_; uint8_t v_newGoals_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3785_; 
v_offsetCnstrs_3772_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 1);
v_occs_3773_ = lean_ctor_get(v_config_3728_, 0);
v_newGoals_3774_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 2);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_config_3728_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3776_ = v_config_3728_;
v_isShared_3777_ = v_isSharedCheck_3785_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_occs_3773_);
lean_dec(v_config_3728_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3785_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_occs_3773_);
v___x_3779_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
uint8_t v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_unbox(v_a_3768_);
lean_dec(v_a_3768_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*1, v___x_3780_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*1 + 1, v_offsetCnstrs_3772_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*1 + 2, v_newGoals_3774_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v___x_3779_);
v___x_3782_ = v___x_3770_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3779_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_config_3728_);
v_a_3787_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3767_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3767_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3795_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3765_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3765_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3803_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3763_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3763_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec_ref(v___x_3750_);
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_3812_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3729_, v___x_3811_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3812_) == 0)
{
uint8_t v___x_3813_; 
lean_dec_ref_known(v___x_3812_, 1);
v___x_3813_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3751_);
if (v___x_3813_ == 0)
{
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3814_; 
lean_dec_ref(v___x_3751_);
v___x_3814_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3833_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3833_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3833_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
uint8_t v_transparency_3819_; lean_object* v_occs_3820_; uint8_t v_newGoals_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3832_; 
v_transparency_3819_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1);
v_occs_3820_ = lean_ctor_get(v_config_3728_, 0);
v_newGoals_3821_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 2);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_config_3728_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3823_ = v_config_3728_;
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_occs_3820_);
lean_dec(v_config_3728_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_occs_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*1, v_transparency_3819_);
v___x_3826_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
uint8_t v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_unbox(v_a_3815_);
lean_dec(v_a_3815_);
lean_ctor_set_uint8(v___x_3826_, sizeof(void*)*1 + 1, v___x_3827_);
lean_ctor_set_uint8(v___x_3826_, sizeof(void*)*1 + 2, v_newGoals_3821_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3826_);
v___x_3829_ = v___x_3817_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3826_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_config_3728_);
v_a_3834_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3814_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3814_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3842_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3812_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3812_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v___x_3750_);
v___x_3850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_3851_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3729_, v___x_3850_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3851_) == 0)
{
uint8_t v___x_3852_; 
lean_dec_ref_known(v___x_3851_, 1);
v___x_3852_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3751_);
if (v___x_3852_ == 0)
{
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3853_; 
lean_dec_ref(v___x_3751_);
lean_inc_ref(v_item_3729_);
v___x_3853_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_value_3854_; lean_object* v___x_3855_; 
lean_dec_ref_known(v___x_3853_, 1);
v_value_3854_ = lean_ctor_get(v_item_3729_, 2);
lean_inc(v_value_3854_);
lean_dec_ref(v_item_3729_);
v___x_3855_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_3854_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3874_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3874_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3874_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
uint8_t v_transparency_3860_; uint8_t v_offsetCnstrs_3861_; uint8_t v_newGoals_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3872_; 
v_transparency_3860_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1);
v_offsetCnstrs_3861_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 1);
v_newGoals_3862_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 2);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_config_3728_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; 
v_unused_3873_ = lean_ctor_get(v_config_3728_, 0);
lean_dec(v_unused_3873_);
v___x_3864_ = v_config_3728_;
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
else
{
lean_dec(v_config_3728_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_a_3856_);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*1, v_transparency_3860_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*1 + 1, v_offsetCnstrs_3861_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*1 + 2, v_newGoals_3862_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3869_; 
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3867_);
v___x_3869_ = v___x_3858_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec_ref(v_config_3728_);
v_a_3875_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3855_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3855_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3883_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3853_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3853_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3891_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3851_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3851_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
else
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_dec_ref(v___x_3750_);
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_3900_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3729_, v___x_3899_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3900_) == 0)
{
uint8_t v___x_3901_; 
lean_dec_ref_known(v___x_3900_, 1);
v___x_3901_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3751_);
if (v___x_3901_ == 0)
{
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3902_; 
lean_dec_ref(v___x_3751_);
lean_inc_ref(v_item_3729_);
v___x_3902_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_value_3903_; lean_object* v___x_3904_; 
lean_dec_ref_known(v___x_3902_, 1);
v_value_3903_ = lean_ctor_get(v_item_3729_, 2);
lean_inc(v_value_3903_);
lean_dec_ref(v_item_3729_);
v___x_3904_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_3903_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3923_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3923_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3923_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
uint8_t v_transparency_3909_; uint8_t v_offsetCnstrs_3910_; lean_object* v_occs_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3922_; 
v_transparency_3909_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1);
v_offsetCnstrs_3910_ = lean_ctor_get_uint8(v_config_3728_, sizeof(void*)*1 + 1);
v_occs_3911_ = lean_ctor_get(v_config_3728_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_config_3728_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3913_ = v_config_3728_;
v_isShared_3914_ = v_isSharedCheck_3922_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_occs_3911_);
lean_dec(v_config_3728_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3922_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_occs_3911_);
lean_ctor_set_uint8(v_reuseFailAlloc_3921_, sizeof(void*)*1, v_transparency_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3921_, sizeof(void*)*1 + 1, v_offsetCnstrs_3910_);
v___x_3916_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
uint8_t v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_unbox(v_a_3905_);
lean_dec(v_a_3905_);
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*1 + 2, v___x_3917_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3916_);
v___x_3919_ = v___x_3907_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3916_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_config_3728_);
v_a_3924_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3904_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3904_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3932_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3902_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3902_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3940_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3900_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3900_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
else
{
uint8_t v___x_3948_; 
lean_dec_ref(v___x_3750_);
lean_dec_ref(v_config_3728_);
v___x_3948_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3751_);
if (v___x_3948_ == 0)
{
lean_dec_ref(v_item_3729_);
v_item_3738_ = v___x_3751_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
else
{
lean_object* v_value_3949_; lean_object* v___x_3950_; 
lean_dec_ref(v___x_3751_);
v_value_3949_ = lean_ctor_get(v_item_3729_, 2);
lean_inc(v_value_3949_);
lean_dec_ref(v_item_3729_);
v___x_3950_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_3949_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
return v___x_3950_;
}
}
}
else
{
lean_dec_ref(v_config_3728_);
v_item_3738_ = v_item_3729_;
v___y_3739_ = v___y_3730_;
v___y_3740_ = v___y_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
goto v___jp_3737_;
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref(v_item_3729_);
lean_dec_ref(v_config_3728_);
v_a_3951_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3748_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3748_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
v___jp_3737_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3746_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3738_, v___x_3745_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3959_, lean_object* v_item_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_3959_, v_item_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_3971_, v___y_3975_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4007_, lean_object* v_msg_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4017_, lean_object* v_msg_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4017_, v_msg_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4027_, lean_object* v_macroStack_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4027_, v_macroStack_4028_, v___y_4033_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4037_, lean_object* v_macroStack_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4037_, v_macroStack_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
return v_res_4046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = lean_box(0);
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4049_ = l_Lean_mkConst(v___x_4048_, v___x_4047_);
return v___x_4049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4052_, lean_object* v_cfgItem_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4062_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4052_, v_cfgItem_4053_, v___x_4061_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4063_, lean_object* v_cfgItem_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4063_, v_cfgItem_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v_cfgItem_4064_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4074_, lean_object* v_init_4075_, uint8_t v_logExceptions_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v_onErr_4081_; lean_object* v_eval_4082_; 
v_onErr_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4076_ == 0)
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4082_, v_init_4075_, v_cfg_4074_, v_onErr_4081_, v_logExceptions_4076_, v_a_4078_, v_a_4079_);
return v___x_4083_;
}
else
{
uint8_t v_recover_4084_; lean_object* v___x_4085_; 
v_recover_4084_ = lean_ctor_get_uint8(v_a_4077_, sizeof(void*)*1);
v___x_4085_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4082_, v_init_4075_, v_cfg_4074_, v_onErr_4081_, v_recover_4084_, v_a_4078_, v_a_4079_);
return v___x_4085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4086_, lean_object* v_init_4087_, lean_object* v_logExceptions_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
uint8_t v_logExceptions_boxed_4093_; lean_object* v_res_4094_; 
v_logExceptions_boxed_4093_ = lean_unbox(v_logExceptions_4088_);
v_res_4094_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4086_, v_init_4087_, v_logExceptions_boxed_4093_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec_ref(v_a_4089_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4095_, lean_object* v_init_4096_, uint8_t v_logExceptions_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4095_, v_init_4096_, v_logExceptions_4097_, v_a_4098_, v_a_4104_, v_a_4105_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4108_, lean_object* v_init_4109_, lean_object* v_logExceptions_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
uint8_t v_logExceptions_boxed_4120_; lean_object* v_res_4121_; 
v_logExceptions_boxed_4120_ = lean_unbox(v_logExceptions_4110_);
v_res_4121_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4108_, v_init_4109_, v_logExceptions_boxed_4120_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_a_4116_);
lean_dec_ref(v_a_4115_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
lean_dec_ref(v_a_4111_);
return v_res_4121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4129_ = l_Lean_MessageData_ofFormat(v___x_4128_);
return v___x_4129_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4143_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4144_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4142_, v_x_4132_, v___x_4143_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4156_, uint8_t v_symm_4157_, lean_object* v_a_4158_, lean_object* v_x_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4156_, v_symm_4157_, v_x_4159_, v_a_4158_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4170_, lean_object* v_symm_4171_, lean_object* v_a_4172_, lean_object* v_x_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
uint8_t v_symm_boxed_4183_; lean_object* v_res_4184_; 
v_symm_boxed_4183_ = lean_unbox(v_symm_4171_);
v_res_4184_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4170_, v_symm_boxed_4183_, v_a_4172_, v_x_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4185_, lean_object* v___x_4186_, lean_object* v___f_4187_, uint8_t v_symm_4188_, lean_object* v_term_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4199_ = lean_box(v_symm_4188_);
lean_inc_ref(v_a_4185_);
lean_inc(v_term_4189_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4200_, 0, v_term_4189_);
lean_closure_set(v___f_4200_, 1, v___x_4199_);
lean_closure_set(v___f_4200_, 2, v_a_4185_);
v___x_4201_ = lean_box(v_symm_4188_);
v___x_4202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4202_, 0, v_term_4189_);
lean_closure_set(v___x_4202_, 1, v___x_4201_);
lean_closure_set(v___x_4202_, 2, v_a_4185_);
v___x_4203_ = l_Lean_Elab_Tactic_withLocation(v___x_4186_, v___f_4200_, v___x_4202_, v___f_4187_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4204_, lean_object* v___x_4205_, lean_object* v___f_4206_, lean_object* v_symm_4207_, lean_object* v_term_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
uint8_t v_symm_boxed_4218_; lean_object* v_res_4219_; 
v_symm_boxed_4218_ = lean_unbox(v_symm_4207_);
v_res_4219_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4204_, v___x_4205_, v___f_4206_, v_symm_boxed_4218_, v_term_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___x_4205_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4236_ = lean_unsigned_to_nat(1u);
v___x_4237_ = l_Lean_Syntax_getArg(v_stx_4226_, v___x_4236_);
v___x_4238_ = 1;
v___x_4239_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4240_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4237_, v___x_4239_, v___x_4238_, v_a_4227_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___f_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___f_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___f_4242_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4243_ = lean_unsigned_to_nat(3u);
v___x_4244_ = l_Lean_Syntax_getArg(v_stx_4226_, v___x_4243_);
v___x_4245_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4244_);
lean_dec(v___x_4244_);
v___f_4246_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4246_, 0, v_a_4241_);
lean_closure_set(v___f_4246_, 1, v___x_4245_);
lean_closure_set(v___f_4246_, 2, v___f_4242_);
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = l_Lean_Syntax_getArg(v_stx_4226_, v___x_4247_);
v___x_4249_ = lean_unsigned_to_nat(2u);
v___x_4250_ = l_Lean_Syntax_getArg(v_stx_4226_, v___x_4249_);
v___x_4251_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4248_, v___x_4250_, v___f_4246_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
lean_dec(v___x_4250_);
return v___x_4251_;
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
v_a_4252_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4240_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4240_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_stx_4260_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4286_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4289_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4290_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4286_, v___x_4287_, v___x_4288_, v___x_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4321_ = l_Lean_addBuiltinDeclarationRanges(v___x_4319_, v___x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4323_;
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
