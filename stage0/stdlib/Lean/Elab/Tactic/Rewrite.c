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
uint8_t v___x_12329__boxed_70_; lean_object* v_res_71_; 
v___x_12329__boxed_70_ = lean_unbox(v___x_64_);
v_res_71_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_63_, v___x_12329__boxed_70_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
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
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v_toCold_650_; lean_object* v_mctx_651_; lean_object* v_lctx_652_; lean_object* v_options_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_647_ = lean_st_ref_get(v___y_645_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_643_);
v_toCold_650_ = lean_ctor_get(v___y_644_, 0);
v_mctx_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_mctx_651_);
lean_dec(v___x_649_);
v_lctx_652_ = lean_ctor_get(v___y_642_, 2);
v_options_653_ = lean_ctor_get(v_toCold_650_, 2);
lean_inc_ref(v_options_653_);
lean_inc_ref(v_lctx_652_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_648_);
lean_ctor_set(v___x_654_, 1, v_mctx_651_);
lean_ctor_set(v___x_654_, 2, v_lctx_652_);
lean_ctor_set(v___x_654_, 3, v_options_653_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_641_);
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
v_ref_670_ = lean_ctor_get(v___y_667_, 2);
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
lean_object* v_toCold_699_; lean_object* v_currRecDepth_700_; lean_object* v_ref_701_; uint8_t v_diag_702_; uint8_t v_suppressElabErrors_703_; lean_object* v_ref_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_toCold_699_ = lean_ctor_get(v___y_696_, 0);
v_currRecDepth_700_ = lean_ctor_get(v___y_696_, 1);
v_ref_701_ = lean_ctor_get(v___y_696_, 2);
v_diag_702_ = lean_ctor_get_uint8(v___y_696_, sizeof(void*)*3);
v_suppressElabErrors_703_ = lean_ctor_get_uint8(v___y_696_, sizeof(void*)*3 + 1);
v_ref_704_ = l_Lean_replaceRef(v_ref_688_, v_ref_701_);
lean_inc(v_currRecDepth_700_);
lean_inc_ref(v_toCold_699_);
v___x_705_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_705_, 0, v_toCold_699_);
lean_ctor_set(v___x_705_, 1, v_currRecDepth_700_);
lean_ctor_set(v___x_705_, 2, v_ref_704_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*3, v_diag_702_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*3 + 1, v_suppressElabErrors_703_);
v___x_706_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_689_, v___y_694_, v___y_695_, v___x_705_, v___y_697_);
lean_dec_ref_known(v___x_705_, 3);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_707_, v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_ref_707_);
return v_res_718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_725_, lean_object* v_e_726_, lean_object* v_stx_727_, uint8_t v_symm_728_, lean_object* v_config_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_739_ = lean_st_ref_get(v_a_735_);
v___x_740_ = lean_box(0);
v___x_741_ = 1;
lean_inc(v_stx_727_);
v___x_742_ = l_Lean_Elab_Tactic_elabTerm(v_stx_727_, v___x_740_, v___x_741_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_mctx_743_; lean_object* v_a_744_; lean_object* v_mvarCounter_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___x_817_; 
v_mctx_743_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_mctx_743_);
lean_dec(v___x_739_);
v_a_744_ = lean_ctor_get(v___x_742_, 0);
lean_inc_n(v_a_744_, 2);
lean_dec_ref_known(v___x_742_, 1);
v_mvarCounter_745_ = lean_ctor_get(v_mctx_743_, 3);
lean_inc(v_mvarCounter_745_);
lean_dec_ref(v_mctx_743_);
v___x_746_ = lean_box(v_symm_728_);
lean_inc_ref(v_e_726_);
lean_inc(v_mvarId_725_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_747_, 0, v_mvarId_725_);
lean_closure_set(v___f_747_, 1, v_e_726_);
lean_closure_set(v___f_747_, 2, v_a_744_);
lean_closure_set(v___f_747_, 3, v___x_746_);
lean_closure_set(v___f_747_, 4, v_config_729_);
v___x_817_ = l_Lean_Expr_hasSyntheticSorry(v_a_744_);
if (v___x_817_ == 0)
{
v___y_781_ = v_a_730_;
v___y_782_ = v_a_731_;
v___y_783_ = v_a_732_;
v___y_784_ = v_a_733_;
v___y_785_ = v_a_734_;
v___y_786_ = v_a_735_;
v___y_787_ = v_a_736_;
v___y_788_ = v_a_737_;
goto v___jp_780_;
}
else
{
lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v___f_747_);
lean_dec(v_mvarCounter_745_);
lean_dec(v_a_744_);
lean_dec(v_stx_727_);
lean_dec_ref(v_e_726_);
lean_dec(v_mvarId_725_);
v___x_818_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
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
v___jp_748_:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_726_, v___f_747_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_779_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_779_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_779_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_779_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v_mctx_763_; lean_object* v_eNew_764_; lean_object* v_eqProof_765_; lean_object* v_mvarIds_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_778_; 
v___x_762_ = lean_st_ref_get(v___y_754_);
v_mctx_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_mctx_763_);
lean_dec(v___x_762_);
v_eNew_764_ = lean_ctor_get(v_a_758_, 0);
v_eqProof_765_ = lean_ctor_get(v_a_758_, 1);
v_mvarIds_766_ = lean_ctor_get(v_a_758_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_778_ == 0)
{
v___x_768_ = v_a_758_;
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_mvarIds_766_);
lean_inc(v_eqProof_765_);
lean_inc(v_eNew_764_);
lean_dec(v_a_758_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_box(0);
v___x_771_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_763_, v_mvarCounter_745_, v_mvarIds_766_, v___x_770_);
lean_dec(v_mvarCounter_745_);
lean_dec_ref(v_mctx_763_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 2, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_eNew_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_eqProof_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_773_);
v___x_775_ = v___x_760_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_745_);
return v___x_757_;
}
}
v___jp_780_:
{
lean_object* v___x_789_; 
lean_inc(v_a_744_);
v___x_789_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_725_, v_a_744_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unbox(v_a_790_);
lean_dec(v_a_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v___f_747_);
lean_dec(v_mvarCounter_745_);
lean_dec_ref(v_e_726_);
v___x_792_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_793_ = l_Lean_indentExpr(v_a_744_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_Expr_mvar___override(v_mvarId_725_);
v___x_798_ = l_Lean_MessageData_ofExpr(v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_727_, v___x_799_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v_stx_727_);
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_dec(v_a_744_);
lean_dec(v_stx_727_);
lean_dec(v_mvarId_725_);
v___y_749_ = v___y_781_;
v___y_750_ = v___y_782_;
v___y_751_ = v___y_783_;
v___y_752_ = v___y_784_;
v___y_753_ = v___y_785_;
v___y_754_ = v___y_786_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v___f_747_);
lean_dec(v_mvarCounter_745_);
lean_dec(v_a_744_);
lean_dec(v_stx_727_);
lean_dec_ref(v_e_726_);
lean_dec(v_mvarId_725_);
v_a_809_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_789_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_789_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___x_739_);
lean_dec_ref(v_config_729_);
lean_dec(v_stx_727_);
lean_dec_ref(v_e_726_);
lean_dec(v_mvarId_725_);
v_a_827_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_742_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_742_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_835_, lean_object* v_e_836_, lean_object* v_stx_837_, lean_object* v_symm_838_, lean_object* v_config_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_symm_boxed_849_; lean_object* v_res_850_; 
v_symm_boxed_849_ = lean_unbox(v_symm_838_);
v_res_850_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_835_, v_e_836_, v_stx_837_, v_symm_boxed_849_, v_config_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_851_, lean_object* v_ref_852_, lean_object* v_msg_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_852_, v_msg_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_864_, lean_object* v_ref_865_, lean_object* v_msg_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_864_, v_ref_865_, v_msg_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_ref_865_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_878_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_889_, v_msg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_901_, lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_902_, v_a_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_905_, lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_905_, v_m_906_, v_a_907_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_m_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_910_, lean_object* v_m_911_, lean_object* v_a_912_, lean_object* v_b_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_911_, v_a_912_, v_b_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_915_, v___y_916_, v___y_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v_mvarId_927_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_939_, v___y_940_, v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v_mvarId_951_);
return v_res_962_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_963_, lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_967_, lean_object* v_a_968_, lean_object* v_x_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_967_, v_a_968_, v_x_969_);
lean_dec(v_x_969_);
lean_dec_ref(v_a_968_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_972_, lean_object* v_data_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_975_, lean_object* v_i_976_, lean_object* v_source_977_, lean_object* v_target_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_976_, v_source_977_, v_target_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_984_, lean_object* v_x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_984_, v_x_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_991_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_991_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1008_, v_x_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1016_, lean_object* v_mvarId_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_mvarId_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1025_, v_mvarId_1026_, v_x_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = lean_array_get_size(v_keys_1034_);
v___x_1038_ = lean_nat_dec_lt(v_i_1035_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v_i_1035_);
return v___x_1038_;
}
else
{
lean_object* v_k_x27_1039_; uint8_t v___x_1040_; 
v_k_x27_1039_ = lean_array_fget_borrowed(v_keys_1034_, v_i_1035_);
v___x_1040_ = l_Lean_instBEqMVarId_beq(v_k_1036_, v_k_x27_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = lean_nat_add(v_i_1035_, v___x_1041_);
lean_dec(v_i_1035_);
v_i_1035_ = v___x_1042_;
goto _start;
}
else
{
lean_dec(v_i_1035_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1044_, v_i_1045_, v_k_1046_);
lean_dec(v_k_1046_);
lean_dec_ref(v_keys_1044_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1049_, size_t v_x_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1049_) == 0)
{
lean_object* v_es_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v_j_1056_; lean_object* v___x_1057_; 
v_es_1052_ = lean_ctor_get(v_x_1049_, 0);
v___x_1053_ = lean_box(2);
v___x_1054_ = ((size_t)31ULL);
v___x_1055_ = lean_usize_land(v_x_1050_, v___x_1054_);
v_j_1056_ = lean_usize_to_nat(v___x_1055_);
v___x_1057_ = lean_array_get_borrowed(v___x_1053_, v_es_1052_, v_j_1056_);
lean_dec(v_j_1056_);
switch(lean_obj_tag(v___x_1057_))
{
case 0:
{
lean_object* v_key_1058_; uint8_t v___x_1059_; 
v_key_1058_ = lean_ctor_get(v___x_1057_, 0);
v___x_1059_ = l_Lean_instBEqMVarId_beq(v_x_1051_, v_key_1058_);
return v___x_1059_;
}
case 1:
{
lean_object* v_node_1060_; size_t v___x_1061_; size_t v___x_1062_; 
v_node_1060_ = lean_ctor_get(v___x_1057_, 0);
v___x_1061_ = ((size_t)5ULL);
v___x_1062_ = lean_usize_shift_right(v_x_1050_, v___x_1061_);
v_x_1049_ = v_node_1060_;
v_x_1050_ = v___x_1062_;
goto _start;
}
default: 
{
uint8_t v___x_1064_; 
v___x_1064_ = 0;
return v___x_1064_;
}
}
}
else
{
lean_object* v_ks_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_ks_1065_ = lean_ctor_get(v_x_1049_, 0);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1065_, v___x_1066_, v_x_1051_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
size_t v_x_1908__boxed_1071_; uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_x_1908__boxed_1071_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1072_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1068_, v_x_1908__boxed_1071_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_x_1068_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint64_t v___x_1076_; size_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = l_Lean_instHashableMVarId_hash(v_x_1075_);
v___x_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1074_, v___x_1077_, v_x_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1079_, v_x_1080_);
lean_dec(v_x_1080_);
lean_dec_ref(v_x_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v_mctx_1087_; lean_object* v_eAssignment_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = lean_st_ref_get(v___y_1084_);
v_mctx_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_mctx_1087_);
lean_dec(v___x_1086_);
v_eAssignment_1088_ = lean_ctor_get(v_mctx_1087_, 8);
lean_inc_ref(v_eAssignment_1088_);
lean_dec_ref(v_mctx_1087_);
v___x_1089_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1088_, v_mvarId_1083_);
lean_dec_ref(v_eAssignment_1088_);
v___x_1090_ = lean_box(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec(v_mvarId_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_x_1097_);
return v___x_1103_;
}
else
{
lean_object* v_head_1104_; lean_object* v_tail_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1118_; 
v_head_1104_ = lean_ctor_get(v_x_1096_, 0);
v_tail_1105_ = lean_ctor_get(v_x_1096_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1107_ = v_x_1096_;
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_tail_1105_);
lean_inc(v_head_1104_);
lean_dec(v_x_1096_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1114_; lean_object* v_a_1115_; uint8_t v___x_1116_; 
v___x_1114_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1104_, v___y_1099_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1116_ == 0)
{
goto v___jp_1109_;
}
else
{
lean_del_object(v___x_1107_);
lean_dec(v_head_1104_);
v_x_1096_ = v_tail_1105_;
goto _start;
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v_x_1097_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_head_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_x_1097_);
v___x_1111_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_x_1096_ = v_tail_1105_;
v_x_1097_ = v___x_1111_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1119_, v_x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
lean_inc(v_head_1127_);
v___x_1133_ = l_Lean_MVarId_getType(v_head_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_Lean_Meta_isProp(v_a_1134_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1147_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_unbox(v_a_1136_);
lean_dec(v_a_1136_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_head_1127_);
v___x_1141_ = lean_box(0);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
uint8_t v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1138_);
v___x_1145_ = 2;
v___x_1146_ = l_Lean_MVarId_setKind___redArg(v_head_1127_, v___x_1145_, v___y_1129_);
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_head_1127_);
v_a_1148_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1135_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1135_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_head_1127_);
v_a_1156_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1133_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1133_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
if (lean_obj_tag(v_as_1171_) == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v_head_1179_; lean_object* v_tail_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v_head_1179_ = lean_ctor_get(v_as_1171_, 0);
lean_inc_n(v_head_1179_, 2);
v_tail_1180_ = lean_ctor_get(v_as_1171_, 1);
lean_inc(v_tail_1180_);
lean_dec_ref_known(v_as_1171_, 2);
v___f_1181_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1181_, 0, v_head_1179_);
v___x_1182_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1179_, v___f_1181_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_dec_ref_known(v___x_1182_, 1);
v_as_1171_ = v_tail_1180_;
goto _start;
}
else
{
lean_dec(v_tail_1180_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_eNew_1197_; lean_object* v_eqProof_1198_; lean_object* v_mvarIds_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1238_; 
v_eNew_1197_ = lean_ctor_get(v_r_1191_, 0);
v_eqProof_1198_ = lean_ctor_get(v_r_1191_, 1);
v_mvarIds_1199_ = lean_ctor_get(v_r_1191_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_r_1191_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1201_ = v_r_1191_;
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_mvarIds_1199_);
lean_inc(v_eqProof_1198_);
lean_inc(v_eNew_1197_);
lean_dec(v_r_1191_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_a_1204_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1199_, v___x_1225_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1228_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = l_List_reverse___redArg(v_a_1227_);
v_a_1204_ = v___x_1228_;
goto v___jp_1203_;
}
else
{
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1226_, 1);
v_a_1204_ = v_a_1229_;
goto v___jp_1203_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_del_object(v___x_1201_);
lean_dec_ref(v_eqProof_1198_);
lean_dec_ref(v_eNew_1197_);
v_a_1230_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1226_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1226_);
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
v___jp_1203_:
{
lean_object* v___x_1205_; 
lean_inc(v_a_1204_);
v___x_1205_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1204_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1215_; 
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1205_, 0);
lean_dec(v_unused_1216_);
v___x_1207_ = v___x_1205_;
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v___x_1205_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 2, v_a_1204_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_eNew_1197_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_eqProof_1198_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_a_1204_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1210_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1204_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_eqProof_1198_);
lean_dec_ref(v_eNew_1197_);
v_a_1217_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1205_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1205_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1246_, v___y_1248_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v_mvarId_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1264_, v_x_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1265_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1269_, lean_object* v_x_1270_, size_t v_x_1271_, lean_object* v_x_1272_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1270_, v_x_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
size_t v_x_2247__boxed_1278_; uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_x_2247__boxed_1278_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_res_1279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1274_, v_x_1275_, v_x_2247__boxed_1278_, v_x_1277_);
lean_dec(v_x_1277_);
lean_dec_ref(v_x_1275_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_heq_1284_, lean_object* v_i_1285_, lean_object* v_k_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1282_, v_i_1285_, v_k_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_k_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1288_, v_keys_1289_, v_vals_1290_, v_heq_1291_, v_i_1292_, v_k_1293_);
lean_dec(v_k_1293_);
lean_dec_ref(v_vals_1290_);
lean_dec_ref(v_keys_1289_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1296_, uint8_t v_symm_1297_, lean_object* v_config_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1309_, v_a_1311_, v_stx_1296_, v_symm_1297_, v_config_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1312_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_config_1298_);
lean_dec(v_stx_1296_);
v_a_1313_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1310_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1310_);
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
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_config_1298_);
lean_dec(v_stx_1296_);
v_a_1321_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1308_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1308_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1329_, lean_object* v_symm_1330_, lean_object* v_config_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_symm_boxed_1341_; lean_object* v_res_1342_; 
v_symm_boxed_1341_ = lean_unbox(v_symm_1330_);
v_res_1342_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1329_, v_symm_boxed_1341_, v_config_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1343_, uint8_t v_symm_1344_, lean_object* v_config_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___f_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1355_ = lean_box(v_symm_1344_);
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1356_, 0, v_stx_1343_);
lean_closure_set(v___f_1356_, 1, v___x_1355_);
lean_closure_set(v___f_1356_, 2, v_config_1345_);
v___x_1357_ = 1;
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
v___x_1358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1358_, 0, lean_box(0));
lean_closure_set(v___x_1358_, 1, v___f_1356_);
lean_closure_set(v___x_1358_, 2, v_a_1346_);
lean_closure_set(v___x_1358_, 3, v_a_1347_);
v___x_1359_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1358_, v___x_1357_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1360_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1347_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_eNew_1365_; lean_object* v_eqProof_1366_; lean_object* v_mvarIds_1367_; lean_object* v___x_1368_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v_eNew_1365_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref(v_eNew_1365_);
v_eqProof_1366_ = lean_ctor_get(v_a_1362_, 1);
lean_inc_ref(v_eqProof_1366_);
v_mvarIds_1367_ = lean_ctor_get(v_a_1362_, 2);
lean_inc(v_mvarIds_1367_);
lean_dec(v_a_1362_);
v___x_1368_ = l_Lean_MVarId_replaceTargetEq(v_a_1364_, v_eNew_1365_, v_eqProof_1366_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1369_);
lean_ctor_set(v___x_1370_, 1, v_mvarIds_1367_);
v___x_1371_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1370_, v_a_1347_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1371_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_mvarIds_1367_);
v_a_1372_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1368_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_a_1362_);
v_a_1380_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1363_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1363_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1361_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1361_);
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
v_a_1396_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1359_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1359_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1404_, lean_object* v_symm_1405_, lean_object* v_config_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
uint8_t v_symm_boxed_1416_; lean_object* v_res_1417_; 
v_symm_boxed_1416_ = lean_unbox(v_symm_1405_);
v_res_1417_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1404_, v_symm_boxed_1416_, v_config_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(lean_object* v_fvarId_1418_, lean_object* v_stx_1419_, uint8_t v_symm_1420_, lean_object* v_config_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1418_, v___y_1426_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1423_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l_Lean_LocalDecl_type(v_a_1432_);
lean_dec(v_a_1432_);
v___x_1436_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1434_, v___x_1435_, v_stx_1419_, v_symm_1420_, v_config_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1436_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_a_1432_);
lean_dec_ref(v_config_1421_);
lean_dec(v_stx_1419_);
v_a_1437_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1433_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1433_);
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
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_config_1421_);
lean_dec(v_stx_1419_);
v_a_1445_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1431_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1431_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed(lean_object* v_fvarId_1453_, lean_object* v_stx_1454_, lean_object* v_symm_1455_, lean_object* v_config_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_symm_boxed_1466_; lean_object* v_res_1467_; 
v_symm_boxed_1466_ = lean_unbox(v_symm_1455_);
v_res_1467_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0(v_fvarId_1453_, v_stx_1454_, v_symm_boxed_1466_, v_config_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(lean_object* v_eqProof_1468_, lean_object* v___x_1469_, lean_object* v_eNew_1470_, lean_object* v_a_1471_, lean_object* v_fvarId_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_mkEqMP(v_eqProof_1468_, v___x_1469_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_eNew_1470_);
v___x_1481_ = lean_box(0);
v___x_1482_ = l_Lean_MVarId_replace(v_a_1471_, v_fvarId_1472_, v_a_1479_, v___x_1480_, v___x_1481_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1482_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_fvarId_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_eNew_1470_);
v_a_1483_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1478_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1478_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed(lean_object* v_eqProof_1491_, lean_object* v___x_1492_, lean_object* v_eNew_1493_, lean_object* v_a_1494_, lean_object* v_fvarId_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1(v_eqProof_1491_, v___x_1492_, v_eNew_1493_, v_a_1494_, v_fvarId_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(lean_object* v___f_1502_, uint8_t v___x_1503_, lean_object* v_fvarId_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_inc(v___y_1506_);
v___x_1514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1514_, 0, lean_box(0));
lean_closure_set(v___x_1514_, 1, v___f_1502_);
lean_closure_set(v___x_1514_, 2, v___y_1505_);
lean_closure_set(v___x_1514_, 3, v___y_1506_);
v___x_1515_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1514_, v___x_1503_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1516_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1506_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v_eNew_1521_; lean_object* v_eqProof_1522_; lean_object* v_mvarIds_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_n(v_a_1520_, 2);
lean_dec_ref_known(v___x_1519_, 1);
v_eNew_1521_ = lean_ctor_get(v_a_1518_, 0);
lean_inc_ref(v_eNew_1521_);
v_eqProof_1522_ = lean_ctor_get(v_a_1518_, 1);
lean_inc_ref(v_eqProof_1522_);
v_mvarIds_1523_ = lean_ctor_get(v_a_1518_, 2);
lean_inc(v_mvarIds_1523_);
lean_dec(v_a_1518_);
lean_inc(v_fvarId_1504_);
v___x_1524_ = l_Lean_mkFVar(v_fvarId_1504_);
v___f_1525_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1525_, 0, v_eqProof_1522_);
lean_closure_set(v___f_1525_, 1, v___x_1524_);
lean_closure_set(v___f_1525_, 2, v_eNew_1521_);
lean_closure_set(v___f_1525_, 3, v_a_1520_);
lean_closure_set(v___f_1525_, 4, v_fvarId_1504_);
v___x_1526_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1520_, v___f_1525_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_fvarId_1528_; lean_object* v_mvarId_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_fvarId_1528_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_fvarId_1528_);
v_mvarId_1529_ = lean_ctor_get(v_a_1527_, 1);
lean_inc(v_mvarId_1529_);
lean_dec(v_a_1527_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_mvarId_1529_);
lean_ctor_set(v___x_1530_, 1, v_mvarIds_1523_);
v___x_1531_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1530_, v___y_1506_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1506_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1531_, 0);
lean_dec(v_unused_1539_);
v___x_1533_ = v___x_1531_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v___x_1531_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_fvarId_1528_);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_fvarId_1528_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_fvarId_1528_);
v_a_1540_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1531_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1531_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_mvarIds_1523_);
lean_dec(v___y_1506_);
v_a_1548_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1526_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1526_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1518_);
lean_dec(v___y_1506_);
lean_dec(v_fvarId_1504_);
v_a_1556_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1519_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1519_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v___y_1506_);
lean_dec(v_fvarId_1504_);
v_a_1564_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1517_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1517_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v___y_1506_);
lean_dec(v_fvarId_1504_);
v_a_1572_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1515_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1515_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed(lean_object* v___f_1580_, lean_object* v___x_1581_, lean_object* v_fvarId_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v___x_1614__boxed_1592_; lean_object* v_res_1593_; 
v___x_1614__boxed_1592_ = lean_unbox(v___x_1581_);
v_res_1593_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2(v___f_1580_, v___x_1614__boxed_1592_, v_fvarId_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore(lean_object* v_stx_1594_, uint8_t v_symm_1595_, lean_object* v_fvarId_1596_, lean_object* v_config_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___f_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; 
v___x_1607_ = lean_box(v_symm_1595_);
lean_inc(v_fvarId_1596_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1608_, 0, v_fvarId_1596_);
lean_closure_set(v___f_1608_, 1, v_stx_1594_);
lean_closure_set(v___f_1608_, 2, v___x_1607_);
lean_closure_set(v___f_1608_, 3, v_config_1597_);
v___x_1609_ = 1;
v___x_1610_ = lean_box(v___x_1609_);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclCore___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1611_, 0, v___f_1608_);
lean_closure_set(v___f_1611_, 1, v___x_1610_);
lean_closure_set(v___f_1611_, 2, v_fvarId_1596_);
v___x_1612_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1611_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore___boxed(lean_object* v_stx_1613_, lean_object* v_symm_1614_, lean_object* v_fvarId_1615_, lean_object* v_config_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
uint8_t v_symm_boxed_1626_; lean_object* v_res_1627_; 
v_symm_boxed_1626_ = lean_unbox(v_symm_1614_);
v_res_1627_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1613_, v_symm_boxed_1626_, v_fvarId_1615_, v_config_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1628_, uint8_t v_symm_1629_, lean_object* v_fvarId_1630_, lean_object* v_config_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_stx_1628_, v_symm_1629_, v_fvarId_1630_, v_config_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1650_);
v___x_1643_ = v___x_1641_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v___x_1641_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_box(0);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1641_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1641_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1659_, lean_object* v_symm_1660_, lean_object* v_fvarId_1661_, lean_object* v_config_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
uint8_t v_symm_boxed_1672_; lean_object* v_res_1673_; 
v_symm_boxed_1672_ = lean_unbox(v_symm_1660_);
v_res_1673_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1659_, v_symm_boxed_1672_, v_fvarId_1661_, v_config_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
return v_res_1673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__0));
v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__2));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(lean_object* v_x_1680_, lean_object* v_acc_1681_, uint8_t v_symm_1682_, lean_object* v_id_1683_, lean_object* v_declName_1684_, lean_object* v_hint_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
if (lean_obj_tag(v_a_1686_) == 0)
{
lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_acc_1681_);
lean_dec_ref(v_x_1680_);
v___x_1696_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__1);
v___x_1697_ = 0;
v___x_1698_ = l_Lean_MessageData_ofConstName(v_declName_1684_, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_hint_1685_);
v___x_1703_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1702_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
return v___x_1703_;
}
else
{
lean_object* v_head_1704_; lean_object* v_tail_1705_; lean_object* v___x_1706_; 
v_head_1704_ = lean_ctor_get(v_a_1686_, 0);
lean_inc(v_head_1704_);
v_tail_1705_ = lean_ctor_get(v_a_1686_, 1);
lean_inc(v_tail_1705_);
lean_dec_ref_known(v_a_1686_, 2);
v___x_1706_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1688_, v_a_1690_, v_a_1692_, v_a_1694_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = 0;
v___x_1709_ = l_Lean_mkCIdentFrom(v_id_1683_, v_head_1704_, v___x_1708_);
v___x_1710_ = lean_box(v_symm_1682_);
lean_inc_ref(v_x_1680_);
lean_inc(v_acc_1681_);
v___x_1711_ = lean_apply_3(v_x_1680_, v_acc_1681_, v___x_1710_, v___x_1709_);
v___x_1712_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1711_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_dec(v_a_1707_);
lean_dec(v_tail_1705_);
lean_dec_ref(v_hint_1685_);
lean_dec(v_declName_1684_);
lean_dec(v_acc_1681_);
lean_dec_ref(v_x_1680_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; uint8_t v___y_1715_; uint8_t v___x_1726_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
v___x_1726_ = l_Lean_Exception_isInterrupt(v_a_1713_);
if (v___x_1726_ == 0)
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Lean_Exception_isRuntime(v_a_1713_);
v___y_1715_ = v___x_1727_;
goto v___jp_1714_;
}
else
{
lean_dec(v_a_1713_);
v___y_1715_ = v___x_1726_;
goto v___jp_1714_;
}
v___jp_1714_:
{
if (v___y_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1712_, 1);
v___x_1716_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1707_, v___y_1715_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_dec_ref_known(v___x_1716_, 1);
v_a_1686_ = v_tail_1705_;
goto _start;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_tail_1705_);
lean_dec_ref(v_hint_1685_);
lean_dec(v_declName_1684_);
lean_dec(v_acc_1681_);
lean_dec_ref(v_x_1680_);
v_a_1718_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1716_);
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
else
{
lean_dec(v_a_1707_);
lean_dec(v_tail_1705_);
lean_dec_ref(v_hint_1685_);
lean_dec(v_declName_1684_);
lean_dec(v_acc_1681_);
lean_dec_ref(v_x_1680_);
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_tail_1705_);
lean_dec(v_head_1704_);
lean_dec_ref(v_hint_1685_);
lean_dec(v_declName_1684_);
lean_dec(v_acc_1681_);
lean_dec_ref(v_x_1680_);
v_a_1728_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1706_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1706_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___boxed(lean_object* v_x_1736_, lean_object* v_acc_1737_, lean_object* v_symm_1738_, lean_object* v_id_1739_, lean_object* v_declName_1740_, lean_object* v_hint_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
uint8_t v_symm_boxed_1752_; lean_object* v_res_1753_; 
v_symm_boxed_1752_ = lean_unbox(v_symm_1738_);
v_res_1753_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1736_, v_acc_1737_, v_symm_boxed_1752_, v_id_1739_, v_declName_1740_, v_hint_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_id_1739_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(lean_object* v_00_u03b1_1754_, lean_object* v_x_1755_, lean_object* v_acc_1756_, uint8_t v_symm_1757_, lean_object* v_id_1758_, lean_object* v_declName_1759_, lean_object* v_hint_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_1755_, v_acc_1756_, v_symm_1757_, v_id_1758_, v_declName_1759_, v_hint_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___boxed(lean_object** _args){
lean_object* v_00_u03b1_1772_ = _args[0];
lean_object* v_x_1773_ = _args[1];
lean_object* v_acc_1774_ = _args[2];
lean_object* v_symm_1775_ = _args[3];
lean_object* v_id_1776_ = _args[4];
lean_object* v_declName_1777_ = _args[5];
lean_object* v_hint_1778_ = _args[6];
lean_object* v_a_1779_ = _args[7];
lean_object* v_a_1780_ = _args[8];
lean_object* v_a_1781_ = _args[9];
lean_object* v_a_1782_ = _args[10];
lean_object* v_a_1783_ = _args[11];
lean_object* v_a_1784_ = _args[12];
lean_object* v_a_1785_ = _args[13];
lean_object* v_a_1786_ = _args[14];
lean_object* v_a_1787_ = _args[15];
lean_object* v_a_1788_ = _args[16];
_start:
{
uint8_t v_symm_boxed_1789_; lean_object* v_res_1790_; 
v_symm_boxed_1789_ = lean_unbox(v_symm_1775_);
v_res_1790_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go(v_00_u03b1_1772_, v_x_1773_, v_acc_1774_, v_symm_boxed_1789_, v_id_1776_, v_declName_1777_, v_hint_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_id_1776_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(lean_object* v_a_1791_, lean_object* v_trees_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1802_ = lean_apply_9(v_a_1791_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1811_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1803_);
lean_ctor_set(v___x_1807_, 1, v_trees_1792_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_trees_1792_);
v_a_1812_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1802_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1802_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed(lean_object* v_a_1820_, lean_object* v_trees_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0(v_a_1820_, v_trees_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(lean_object* v___x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1832_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1___boxed(lean_object* v___x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__1(v___x_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_unsigned_to_nat(32u);
v___x_1855_ = lean_mk_empty_array_with_capacity(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = ((size_t)5ULL);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_unsigned_to_nat(32u);
v___x_1860_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
lean_ctor_set(v___x_1862_, 2, v___x_1858_);
lean_ctor_set(v___x_1862_, 3, v___x_1858_);
lean_ctor_set_usize(v___x_1862_, 4, v___x_1857_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_infoState_1866_; lean_object* v_trees_1867_; lean_object* v___x_1868_; lean_object* v_infoState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_traceState_1874_; lean_object* v_cache_1875_; lean_object* v_messages_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1898_; 
v___x_1865_ = lean_st_ref_get(v___y_1863_);
v_infoState_1866_ = lean_ctor_get(v___x_1865_, 7);
lean_inc_ref(v_infoState_1866_);
lean_dec(v___x_1865_);
v_trees_1867_ = lean_ctor_get(v_infoState_1866_, 2);
lean_inc_ref(v_trees_1867_);
lean_dec_ref(v_infoState_1866_);
v___x_1868_ = lean_st_ref_take(v___y_1863_);
v_infoState_1869_ = lean_ctor_get(v___x_1868_, 7);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_traceState_1874_ = lean_ctor_get(v___x_1868_, 4);
v_cache_1875_ = lean_ctor_get(v___x_1868_, 5);
v_messages_1876_ = lean_ctor_get(v___x_1868_, 6);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1868_, 8);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1898_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1869_);
lean_inc(v_messages_1876_);
lean_inc(v_cache_1875_);
lean_inc(v_traceState_1874_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1898_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
uint8_t v_enabled_1881_; lean_object* v_assignment_1882_; lean_object* v_lazyAssignment_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1896_; 
v_enabled_1881_ = lean_ctor_get_uint8(v_infoState_1869_, sizeof(void*)*3);
v_assignment_1882_ = lean_ctor_get(v_infoState_1869_, 0);
v_lazyAssignment_1883_ = lean_ctor_get(v_infoState_1869_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_infoState_1869_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v_infoState_1869_, 2);
lean_dec(v_unused_1897_);
v___x_1885_ = v_infoState_1869_;
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_lazyAssignment_1883_);
lean_inc(v_assignment_1882_);
lean_dec(v_infoState_1869_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 2, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_assignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_lazyAssignment_1883_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v___x_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*3, v_enabled_1881_);
v___x_1889_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 7, v___x_1889_);
v___x_1891_ = v___x_1879_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_traceState_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v_cache_1875_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_messages_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_snapshotTasks_1877_);
v___x_1891_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_st_ref_put(v___y_1863_, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_trees_1867_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1899_);
lean_dec(v___y_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1902_, lean_object* v_mkInfoTree_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v_a_1911_, lean_object* v_a_x3f_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v_infoState_1915_; lean_object* v_trees_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_st_ref_get(v___y_1902_);
v_infoState_1915_ = lean_ctor_get(v___x_1914_, 7);
lean_inc_ref(v_infoState_1915_);
lean_dec(v___x_1914_);
v_trees_1916_ = lean_ctor_get(v_infoState_1915_, 2);
lean_inc_ref(v_trees_1916_);
lean_dec_ref(v_infoState_1915_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
v___x_1917_ = lean_apply_10(v_mkInfoTree_1903_, v_trees_1916_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1902_, lean_box(0));
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1956_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1956_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1956_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v_infoState_1923_; lean_object* v_env_1924_; lean_object* v_nextMacroScope_1925_; lean_object* v_ngen_1926_; lean_object* v_auxDeclNGen_1927_; lean_object* v_traceState_1928_; lean_object* v_cache_1929_; lean_object* v_messages_1930_; lean_object* v_snapshotTasks_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1955_; 
v___x_1922_ = lean_st_ref_take(v___y_1902_);
v_infoState_1923_ = lean_ctor_get(v___x_1922_, 7);
v_env_1924_ = lean_ctor_get(v___x_1922_, 0);
v_nextMacroScope_1925_ = lean_ctor_get(v___x_1922_, 1);
v_ngen_1926_ = lean_ctor_get(v___x_1922_, 2);
v_auxDeclNGen_1927_ = lean_ctor_get(v___x_1922_, 3);
v_traceState_1928_ = lean_ctor_get(v___x_1922_, 4);
v_cache_1929_ = lean_ctor_get(v___x_1922_, 5);
v_messages_1930_ = lean_ctor_get(v___x_1922_, 6);
v_snapshotTasks_1931_ = lean_ctor_get(v___x_1922_, 8);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1933_ = v___x_1922_;
v_isShared_1934_ = v_isSharedCheck_1955_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snapshotTasks_1931_);
lean_inc(v_infoState_1923_);
lean_inc(v_messages_1930_);
lean_inc(v_cache_1929_);
lean_inc(v_traceState_1928_);
lean_inc(v_auxDeclNGen_1927_);
lean_inc(v_ngen_1926_);
lean_inc(v_nextMacroScope_1925_);
lean_inc(v_env_1924_);
lean_dec(v___x_1922_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1955_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
uint8_t v_enabled_1935_; lean_object* v_assignment_1936_; lean_object* v_lazyAssignment_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1953_; 
v_enabled_1935_ = lean_ctor_get_uint8(v_infoState_1923_, sizeof(void*)*3);
v_assignment_1936_ = lean_ctor_get(v_infoState_1923_, 0);
v_lazyAssignment_1937_ = lean_ctor_get(v_infoState_1923_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_infoState_1923_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v_infoState_1923_, 2);
lean_dec(v_unused_1954_);
v___x_1939_ = v_infoState_1923_;
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_lazyAssignment_1937_);
lean_inc(v_assignment_1936_);
lean_dec(v_infoState_1923_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = l_Lean_PersistentArray_push___redArg(v_a_1911_, v_a_1918_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 2, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_assignment_1936_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_lazyAssignment_1937_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v___x_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1952_, sizeof(void*)*3, v_enabled_1935_);
v___x_1943_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1945_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 7, v___x_1943_);
v___x_1945_ = v___x_1933_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_env_1924_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_nextMacroScope_1925_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_ngen_1926_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_auxDeclNGen_1927_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_traceState_1928_);
lean_ctor_set(v_reuseFailAlloc_1951_, 5, v_cache_1929_);
lean_ctor_set(v_reuseFailAlloc_1951_, 6, v_messages_1930_);
lean_ctor_set(v_reuseFailAlloc_1951_, 7, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1951_, 8, v_snapshotTasks_1931_);
v___x_1945_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1946_ = lean_st_ref_put(v___y_1902_, v___x_1945_);
v___x_1947_ = lean_box(0);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1947_);
v___x_1949_ = v___x_1920_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_a_1911_);
v_a_1957_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1917_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1917_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1965_, lean_object* v_mkInfoTree_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v_a_1974_, lean_object* v_a_x3f_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1965_, v_mkInfoTree_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v_a_1974_, v_a_x3f_1975_);
lean_dec(v_a_x3f_1975_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1965_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(lean_object* v_x_1978_, lean_object* v_mkInfoTree_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v_infoState_1990_; uint8_t v_enabled_1991_; 
v___x_1989_ = lean_st_ref_get(v___y_1987_);
v_infoState_1990_ = lean_ctor_get(v___x_1989_, 7);
lean_inc_ref(v_infoState_1990_);
lean_dec(v___x_1989_);
v_enabled_1991_ = lean_ctor_get_uint8(v_infoState_1990_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1990_);
if (v_enabled_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref(v_mkInfoTree_1979_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
v___x_1992_ = lean_apply_9(v_x_1978_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, lean_box(0));
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; lean_object* v_a_1994_; lean_object* v_r_1995_; 
v___x_1993_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_1987_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref(v___x_1993_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
v_r_1995_ = lean_apply_9(v_x_1978_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, lean_box(0));
if (lean_obj_tag(v_r_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2020_; 
v_a_1996_ = lean_ctor_get(v_r_1995_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1998_ = v_r_1995_;
v_isShared_1999_ = v_isSharedCheck_2020_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v_r_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2020_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
lean_inc(v_a_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 1);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1987_, v_mkInfoTree_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v_a_1994_, v___x_2001_);
lean_dec_ref(v___x_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_2002_, 0);
lean_dec(v_unused_2010_);
v___x_2004_ = v___x_2002_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_dec(v___x_2002_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v_a_1996_);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_1996_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1996_);
v_a_2011_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2002_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2002_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2021_ = lean_ctor_get(v_r_1995_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v_r_1995_, 1);
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___lam__0(v___y_1987_, v_mkInfoTree_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v_a_1994_, v___x_2022_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_2023_, 0);
lean_dec(v_unused_2031_);
v___x_2025_ = v___x_2023_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v___x_2023_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 1);
lean_ctor_set(v___x_2025_, 0, v_a_2021_);
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2021_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2021_);
v_a_2032_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2023_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2023_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_2040_, lean_object* v_mkInfoTree_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2040_, v_mkInfoTree_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_2061_, uint8_t v___x_2062_, lean_object* v___x_2063_, lean_object* v_x_2064_, lean_object* v_b_2065_, uint8_t v___y_2066_, lean_object* v___x_2067_, lean_object* v___x_2068_, lean_object* v___f_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_toCold_2079_; lean_object* v_currRecDepth_2080_; lean_object* v_ref_2081_; uint8_t v_diag_2082_; uint8_t v_suppressElabErrors_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2101_; 
v_toCold_2079_ = lean_ctor_get(v___y_2076_, 0);
v_currRecDepth_2080_ = lean_ctor_get(v___y_2076_, 1);
v_ref_2081_ = lean_ctor_get(v___y_2076_, 2);
v_diag_2082_ = lean_ctor_get_uint8(v___y_2076_, sizeof(void*)*3);
v_suppressElabErrors_2083_ = lean_ctor_get_uint8(v___y_2076_, sizeof(void*)*3 + 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___y_2076_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2085_ = v___y_2076_;
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_ref_2081_);
lean_inc(v_currRecDepth_2080_);
lean_inc(v_toCold_2079_);
lean_dec(v___y_2076_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_ref_2087_; lean_object* v___x_2089_; 
v_ref_2087_ = l_Lean_replaceRef(v___x_2061_, v_ref_2081_);
lean_dec(v_ref_2081_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 2, v_ref_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_toCold_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_currRecDepth_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_ref_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*3, v_diag_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*3 + 1, v_suppressElabErrors_2083_);
v___x_2089_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
if (v___x_2062_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_2063_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v___x_2063_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref(v___f_2069_);
v___x_2092_ = lean_box(v___y_2066_);
v___x_2093_ = lean_apply_12(v_x_2064_, v_b_2065_, v___x_2092_, v___x_2063_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___x_2089_, v___y_2077_, lean_box(0));
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = l_Lean_Syntax_getArg(v___x_2063_, v___x_2067_);
lean_inc(v___x_2094_);
v___x_2095_ = l_Lean_Syntax_isOfKind(v___x_2094_, v___x_2068_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v___x_2094_);
lean_dec_ref(v___f_2069_);
v___x_2096_ = lean_box(v___y_2066_);
v___x_2097_ = lean_apply_12(v_x_2064_, v_b_2065_, v___x_2096_, v___x_2063_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___x_2089_, v___y_2077_, lean_box(0));
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_b_2065_);
lean_dec_ref(v_x_2064_);
lean_dec(v___x_2063_);
v___x_2098_ = lean_apply_10(v___f_2069_, v___x_2094_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___x_2089_, v___y_2077_, lean_box(0));
return v___x_2098_;
}
}
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_b_2065_);
lean_dec_ref(v_x_2064_);
v___x_2099_ = lean_apply_10(v___f_2069_, v___x_2063_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___x_2089_, v___y_2077_, lean_box(0));
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2102_ = _args[0];
lean_object* v___x_2103_ = _args[1];
lean_object* v___x_2104_ = _args[2];
lean_object* v_x_2105_ = _args[3];
lean_object* v_b_2106_ = _args[4];
lean_object* v___y_2107_ = _args[5];
lean_object* v___x_2108_ = _args[6];
lean_object* v___x_2109_ = _args[7];
lean_object* v___f_2110_ = _args[8];
lean_object* v___y_2111_ = _args[9];
lean_object* v___y_2112_ = _args[10];
lean_object* v___y_2113_ = _args[11];
lean_object* v___y_2114_ = _args[12];
lean_object* v___y_2115_ = _args[13];
lean_object* v___y_2116_ = _args[14];
lean_object* v___y_2117_ = _args[15];
lean_object* v___y_2118_ = _args[16];
lean_object* v___y_2119_ = _args[17];
_start:
{
uint8_t v___x_15826__boxed_2120_; uint8_t v___y_15828__boxed_2121_; lean_object* v_res_2122_; 
v___x_15826__boxed_2120_ = lean_unbox(v___x_2103_);
v___y_15828__boxed_2121_ = lean_unbox(v___y_2107_);
v_res_2122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3(v___x_2102_, v___x_15826__boxed_2120_, v___x_2104_, v_x_2105_, v_b_2106_, v___y_15828__boxed_2121_, v___x_2108_, v___x_2109_, v___f_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___x_2109_);
lean_dec(v___x_2108_);
lean_dec(v___x_2102_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2123_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1(v_id_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2144_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_2151_, lean_object* v_b_2152_, uint8_t v___y_2153_, lean_object* v___x_2154_, lean_object* v___x_2155_, lean_object* v_id_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___f_2166_; lean_object* v___x_2167_; 
lean_inc(v_id_2156_);
v___f_2166_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2166_, 0, v_id_2156_);
v___x_2167_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2166_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
if (lean_obj_tag(v_a_2168_) == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2158_, v___y_2160_, v___y_2162_, v___y_2164_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
lean_inc(v_id_2156_);
v___x_2171_ = l_Lean_realizeGlobalConstNoOverload(v_id_2156_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
lean_dec(v_a_2170_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc_n(v_a_2172_, 2);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2172_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
if (lean_obj_tag(v_a_2174_) == 1)
{
lean_object* v_val_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v___x_2155_);
v_val_2175_ = lean_ctor_get(v_a_2174_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_a_2174_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2177_ = v_a_2174_;
v_isShared_2178_ = v_isSharedCheck_2219_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_val_2175_);
lean_dec(v_a_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2219_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint8_t v___x_2179_; lean_object* v___y_2181_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2179_ = 0;
v___x_2208_ = lean_array_get_size(v_val_2175_);
v___x_2209_ = lean_nat_dec_eq(v___x_2208_, v___x_2154_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2210_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_2211_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2172_);
v___x_2212_ = l_Lean_Name_str___override(v_a_2172_, v___x_2211_);
v___x_2213_ = l_Lean_MessageData_ofName(v___x_2212_);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2210_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_MessageData_hint_x27(v___x_2216_);
v___y_2181_ = v___x_2217_;
goto v___jp_2180_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2181_ = v___x_2218_;
goto v___jp_2180_;
}
v___jp_2180_:
{
lean_object* v___x_2182_; 
lean_inc(v_a_2172_);
v___x_2182_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2172_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v_lctx_2184_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v_lctx_2184_ = lean_ctor_get(v___y_2161_, 2);
lean_inc_ref(v_lctx_2184_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v_lctx_2184_);
v___x_2186_ = v___x_2177_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_lctx_2184_);
v___x_2186_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_box(0);
lean_inc(v_id_2156_);
v___x_2188_ = l_Lean_Elab_Term_addTermInfo(v_id_2156_, v_a_2183_, v_a_2168_, v___x_2186_, v___x_2187_, v___x_2179_, v___x_2179_, v___x_2179_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref_known(v___x_2188_, 1);
v___x_2189_ = lean_array_to_list(v_val_2175_);
v___x_2190_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg(v_x_2151_, v_b_2152_, v___y_2153_, v_id_2156_, v_a_2172_, v___y_2181_, v___x_2189_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v_id_2156_);
return v___x_2190_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___y_2181_);
lean_dec(v_val_2175_);
lean_dec(v_a_2172_);
lean_dec(v_id_2156_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2191_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2188_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2188_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v___y_2181_);
lean_del_object(v___x_2177_);
lean_dec(v_val_2175_);
lean_dec(v_a_2172_);
lean_dec(v_id_2156_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2200_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2182_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2182_);
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
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_a_2174_);
lean_dec(v_a_2172_);
lean_dec(v_id_2156_);
v___x_2220_ = lean_box(v___y_2153_);
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2221_ = lean_apply_12(v_x_2151_, v_b_2152_, v___x_2220_, v___x_2155_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
return v___x_2221_;
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2172_);
lean_dec(v_id_2156_);
lean_dec(v___x_2155_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2222_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2173_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2173_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_id_2156_);
v_a_2230_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2232_ = v___x_2171_;
v_isShared_2233_ = v_isSharedCheck_2252_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2171_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2252_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___y_2235_; uint8_t v___x_2250_; 
v___x_2250_ = l_Lean_Exception_isInterrupt(v_a_2230_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
lean_inc(v_a_2230_);
v___x_2251_ = l_Lean_Exception_isRuntime(v_a_2230_);
v___y_2235_ = v___x_2251_;
goto v___jp_2234_;
}
else
{
v___y_2235_ = v___x_2250_;
goto v___jp_2234_;
}
v___jp_2234_:
{
if (v___y_2235_ == 0)
{
lean_object* v___x_2236_; 
lean_del_object(v___x_2232_);
lean_dec(v_a_2230_);
v___x_2236_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2170_, v___y_2235_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref_known(v___x_2236_, 1);
v___x_2237_ = lean_box(v___y_2153_);
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2238_ = lean_apply_12(v_x_2151_, v_b_2152_, v___x_2237_, v___x_2155_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
return v___x_2238_;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___x_2155_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2239_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2236_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2236_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v___x_2248_; 
lean_dec(v_a_2170_);
lean_dec(v___x_2155_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
if (v_isShared_2233_ == 0)
{
v___x_2248_ = v___x_2232_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2230_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_id_2156_);
lean_dec(v___x_2155_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2253_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2169_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2169_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref_known(v_a_2168_, 1);
lean_dec(v_id_2156_);
v___x_2261_ = lean_box(v___y_2153_);
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2262_ = lean_apply_12(v_x_2151_, v_b_2152_, v___x_2261_, v___x_2155_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
return v___x_2262_;
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_id_2156_);
lean_dec(v___x_2155_);
lean_dec(v_b_2152_);
lean_dec_ref(v_x_2151_);
v_a_2263_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2167_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2167_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v_id_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v___y_15960__boxed_2286_; lean_object* v_res_2287_; 
v___y_15960__boxed_2286_ = lean_unbox(v___y_2273_);
v_res_2287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2(v_x_2271_, v_b_2272_, v___y_15960__boxed_2286_, v___x_2274_, v___x_2275_, v_id_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___x_2274_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_2288_, lean_object* v_trees_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2295_);
lean_inc_ref(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
v___x_2299_ = lean_apply_9(v_a_2288_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, lean_box(0));
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2300_);
lean_ctor_set(v___x_2304_, 1, v_trees_2289_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
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
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_trees_2289_);
v_a_2309_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2299_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_2317_, lean_object* v_trees_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0(v_a_2317_, v_trees_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2335_, lean_object* v_rules_2336_, lean_object* v_x_2337_, lean_object* v_a_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_nat_dec_lt(v_a_2338_, v_upperBound_2335_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v_a_2338_);
lean_dec_ref(v_x_2337_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_b_2339_);
return v___x_2350_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___y_2358_; uint8_t v___y_2359_; lean_object* v___y_2384_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_nat_mul(v_a_2338_, v___x_2351_);
v___x_2356_ = lean_array_get_borrowed(v___x_2352_, v_rules_2336_, v___x_2355_);
v___x_2394_ = lean_nat_add(v___x_2355_, v___x_2353_);
lean_dec(v___x_2355_);
v___x_2395_ = lean_array_get_size(v_rules_2336_);
v___x_2396_ = lean_nat_dec_lt(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v___x_2394_);
v___y_2384_ = v___x_2352_;
goto v___jp_2383_;
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_array_fget_borrowed(v_rules_2336_, v___x_2394_);
lean_dec(v___x_2394_);
lean_inc(v___x_2397_);
v___y_2384_ = v___x_2397_;
goto v___jp_2383_;
}
v___jp_2357_:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2358_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___f_2362_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2362_, 0, v_a_2361_);
v___x_2363_ = l_Lean_Syntax_getArg(v___x_2356_, v___x_2353_);
v___x_2364_ = lean_box(v___y_2359_);
lean_inc_n(v___x_2363_, 2);
lean_inc(v_b_2339_);
lean_inc_ref_n(v_x_2337_, 2);
v___f_2365_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__2___boxed), 15, 5);
lean_closure_set(v___f_2365_, 0, v_x_2337_);
lean_closure_set(v___f_2365_, 1, v_b_2339_);
lean_closure_set(v___f_2365_, 2, v___x_2364_);
lean_closure_set(v___f_2365_, 3, v___x_2353_);
lean_closure_set(v___f_2365_, 4, v___x_2363_);
v___x_2366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__1));
v___x_2367_ = l_Lean_Syntax_isOfKind(v___x_2363_, v___x_2366_);
v___x_2368_ = lean_box(v___x_2367_);
v___x_2369_ = lean_box(v___y_2359_);
lean_inc(v___x_2356_);
v___f_2370_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___lam__3___boxed), 18, 9);
lean_closure_set(v___f_2370_, 0, v___x_2356_);
lean_closure_set(v___f_2370_, 1, v___x_2368_);
lean_closure_set(v___f_2370_, 2, v___x_2363_);
lean_closure_set(v___f_2370_, 3, v_x_2337_);
lean_closure_set(v___f_2370_, 4, v_b_2339_);
lean_closure_set(v___f_2370_, 5, v___x_2369_);
lean_closure_set(v___f_2370_, 6, v___x_2353_);
lean_closure_set(v___f_2370_, 7, v___x_2366_);
lean_closure_set(v___f_2370_, 8, v___f_2365_);
v___x_2371_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2370_, v___f_2362_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_nat_add(v_a_2338_, v___x_2353_);
lean_dec(v_a_2338_);
v_a_2338_ = v___x_2373_;
v_b_2339_ = v_a_2372_;
goto _start;
}
else
{
lean_dec(v_a_2338_);
lean_dec_ref(v_x_2337_);
return v___x_2371_;
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_b_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_x_2337_);
v_a_2375_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2360_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2360_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
v___jp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2385_ = lean_mk_empty_array_with_capacity(v___x_2351_);
lean_inc(v___x_2356_);
v___x_2386_ = lean_array_push(v___x_2385_, v___x_2356_);
v___x_2387_ = lean_array_push(v___x_2386_, v___y_2384_);
v___x_2388_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2389_ = lean_box(2);
v___x_2390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2388_);
lean_ctor_set(v___x_2390_, 2, v___x_2387_);
v___x_2391_ = l_Lean_Syntax_getArg(v___x_2356_, v___x_2354_);
v___x_2392_ = l_Lean_Syntax_isNone(v___x_2391_);
lean_dec(v___x_2391_);
if (v___x_2392_ == 0)
{
v___y_2358_ = v___x_2390_;
v___y_2359_ = v___x_2349_;
goto v___jp_2357_;
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
v___y_2358_ = v___x_2390_;
v___y_2359_ = v___x_2393_;
goto v___jp_2357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2398_, lean_object* v_rules_2399_, lean_object* v_x_2400_, lean_object* v_a_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2398_, v_rules_2399_, v_x_2400_, v_a_2401_, v_b_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_rules_2399_);
lean_dec(v_upperBound_2398_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(lean_object* v_token_2415_, lean_object* v_rwRulesSeqStx_2416_, lean_object* v_init_2417_, lean_object* v_x_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v_lbrak_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2428_ = lean_unsigned_to_nat(0u);
v_lbrak_2429_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2416_, v___x_2428_);
v___x_2430_ = lean_unsigned_to_nat(2u);
v___x_2431_ = lean_mk_empty_array_with_capacity(v___x_2430_);
v___x_2432_ = lean_array_push(v___x_2431_, v_token_2415_);
v___x_2433_ = lean_array_push(v___x_2432_, v_lbrak_2429_);
v___x_2434_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg___closed__3));
v___x_2435_ = lean_box(2);
v___x_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
lean_ctor_set(v___x_2436_, 2, v___x_2433_);
v___x_2437_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2436_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2439_, 0, v_a_2438_);
v___f_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___closed__0));
v___x_2441_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v___f_2440_, v___f_2439_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_rules_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref_known(v___x_2441_, 1);
v___x_2442_ = lean_unsigned_to_nat(1u);
v___x_2443_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2416_, v___x_2442_);
v_rules_2444_ = l_Lean_Syntax_getArgs(v___x_2443_);
lean_dec(v___x_2443_);
v___x_2445_ = lean_array_get_size(v_rules_2444_);
v___x_2446_ = lean_nat_add(v___x_2445_, v___x_2442_);
v___x_2447_ = lean_nat_shiftr(v___x_2446_, v___x_2442_);
lean_dec(v___x_2446_);
v___x_2448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v___x_2447_, v_rules_2444_, v_x_2418_, v___x_2428_, v_init_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec_ref(v_rules_2444_);
lean_dec(v___x_2447_);
return v___x_2448_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v_x_2418_);
lean_dec(v_init_2417_);
v_a_2449_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2441_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2441_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v_x_2418_);
lean_dec(v_init_2417_);
v_a_2457_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2437_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2437_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg___boxed(lean_object* v_token_2465_, lean_object* v_rwRulesSeqStx_2466_, lean_object* v_init_2467_, lean_object* v_x_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2465_, v_rwRulesSeqStx_2466_, v_init_2467_, v_x_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_rwRulesSeqStx_2466_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq(lean_object* v_00_u03b1_2479_, lean_object* v_token_2480_, lean_object* v_rwRulesSeqStx_2481_, lean_object* v_init_2482_, lean_object* v_x_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2480_, v_rwRulesSeqStx_2481_, v_init_2482_, v_x_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_token_2495_, lean_object* v_rwRulesSeqStx_2496_, lean_object* v_init_2497_, lean_object* v_x_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Elab_Tactic_foldRWRulesSeq(v_00_u03b1_2494_, v_token_2495_, v_rwRulesSeqStx_2496_, v_init_2497_, v_x_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_rwRulesSeqStx_2496_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___redArg(v___y_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0_spec__0(v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(lean_object* v_00_u03b1_2529_, lean_object* v_x_2530_, lean_object* v_mkInfoTree_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___redArg(v_x_2530_, v_mkInfoTree_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_x_2543_, lean_object* v_mkInfoTree_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__0(v_00_u03b1_2542_, v_x_2543_, v_mkInfoTree_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(lean_object* v_00_u03b1_2555_, lean_object* v_upperBound_2556_, lean_object* v_rules_2557_, lean_object* v_x_2558_, lean_object* v_inst_2559_, lean_object* v_R_2560_, lean_object* v_a_2561_, lean_object* v_b_2562_, lean_object* v_c_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___redArg(v_upperBound_2556_, v_rules_2557_, v_x_2558_, v_a_2561_, v_b_2562_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_2574_ = _args[0];
lean_object* v_upperBound_2575_ = _args[1];
lean_object* v_rules_2576_ = _args[2];
lean_object* v_x_2577_ = _args[3];
lean_object* v_inst_2578_ = _args[4];
lean_object* v_R_2579_ = _args[5];
lean_object* v_a_2580_ = _args[6];
lean_object* v_b_2581_ = _args[7];
lean_object* v_c_2582_ = _args[8];
lean_object* v___y_2583_ = _args[9];
lean_object* v___y_2584_ = _args[10];
lean_object* v___y_2585_ = _args[11];
lean_object* v___y_2586_ = _args[12];
lean_object* v___y_2587_ = _args[13];
lean_object* v___y_2588_ = _args[14];
lean_object* v___y_2589_ = _args[15];
lean_object* v___y_2590_ = _args[16];
lean_object* v___y_2591_ = _args[17];
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_foldRWRulesSeq_spec__1(v_00_u03b1_2574_, v_upperBound_2575_, v_rules_2576_, v_x_2577_, v_inst_2578_, v_R_2579_, v_a_2580_, v_b_2581_, v_c_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_rules_2576_);
lean_dec(v_upperBound_2575_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_x_2593_, lean_object* v_x_2594_, uint8_t v_symm_2595_, lean_object* v_term_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_box(v_symm_2595_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
v___x_2607_ = lean_apply_11(v_x_2593_, v___x_2606_, v_term_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_x_2608_, lean_object* v_x_2609_, lean_object* v_symm_2610_, lean_object* v_term_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v_symm_boxed_2621_; lean_object* v_res_2622_; 
v_symm_boxed_2621_ = lean_unbox(v_symm_2610_);
v_res_2622_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_x_2608_, v_x_2609_, v_symm_boxed_2621_, v_term_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2623_, lean_object* v_rwRulesSeqStx_2624_, lean_object* v_x_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2635_, 0, v_x_2625_);
v___x_2636_ = lean_box(0);
v___x_2637_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v_token_2623_, v_rwRulesSeqStx_2624_, v___x_2636_, v___f_2635_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; 
v_unused_2645_ = lean_ctor_get(v___x_2637_, 0);
lean_dec(v_unused_2645_);
v___x_2639_ = v___x_2637_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_dec(v___x_2637_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2636_);
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2636_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
else
{
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2646_, lean_object* v_rwRulesSeqStx_2647_, lean_object* v_x_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2646_, v_rwRulesSeqStx_2647_, v_x_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_rwRulesSeqStx_2647_);
return v_res_2658_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_box(0);
v___x_2660_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
lean_ctor_set(v___x_2661_, 1, v___x_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_ref_2687_; lean_object* v___x_2688_; lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2697_; 
v_ref_2687_ = lean_ctor_get(v___y_2684_, 2);
v___x_2688_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2697_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2697_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_inc(v_ref_2687_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_ref_2687_);
lean_ctor_set(v___x_2693_, 1, v_a_2689_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 1);
lean_ctor_set(v___x_2691_, 0, v___x_2693_);
v___x_2695_ = v___x_2691_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2704_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_2709_, lean_object* v_ctor_2710_, lean_object* v_args_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2778_ = lean_string_dec_eq(v_ctor_2710_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2779_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2780_ = lean_array_get_size(v_args_2711_);
v___x_2781_ = lean_unsigned_to_nat(4u);
v___x_2782_ = lean_nat_dec_eq(v___x_2780_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
v___x_2783_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2784_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2783_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
else
{
goto v___jp_2717_;
}
}
v___jp_2717_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = lean_array_get_borrowed(v___x_2709_, v_args_2711_, v___x_2718_);
lean_inc(v___x_2719_);
v___x_2720_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2719_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_array_get_borrowed(v___x_2709_, v_args_2711_, v___x_2722_);
lean_inc(v___x_2723_);
v___x_2724_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2723_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = lean_unsigned_to_nat(2u);
v___x_2727_ = lean_array_get_borrowed(v___x_2709_, v_args_2711_, v___x_2726_);
lean_inc(v___x_2727_);
v___x_2728_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2727_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = lean_unsigned_to_nat(3u);
v___x_2731_ = lean_array_get_borrowed(v___x_2709_, v_args_2711_, v___x_2730_);
lean_inc(v___x_2731_);
v___x_2732_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2731_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2744_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; uint8_t v___x_2738_; uint8_t v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2742_; 
v___x_2737_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2737_, 0, v_a_2729_);
v___x_2738_ = lean_unbox(v_a_2721_);
lean_dec(v_a_2721_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*1, v___x_2738_);
v___x_2739_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*1 + 1, v___x_2739_);
v___x_2740_ = lean_unbox(v_a_2733_);
lean_dec(v_a_2733_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*1 + 2, v___x_2740_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2737_);
v___x_2742_ = v___x_2735_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2729_);
lean_dec(v_a_2725_);
lean_dec(v_a_2721_);
v_a_2745_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2732_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2732_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2725_);
lean_dec(v_a_2721_);
v_a_2753_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2728_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2728_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2721_);
v_a_2761_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2724_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2724_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
v_a_2769_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2720_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2720_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_2793_, lean_object* v_ctor_2794_, lean_object* v_args_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v___x_2793_, v_ctor_2794_, v_args_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_args_2795_);
lean_dec_ref(v_ctor_2794_);
lean_dec_ref(v___x_2793_);
return v_res_2801_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___f_2803_; 
v___x_2802_ = l_Lean_instInhabitedExpr;
v___f_2803_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2803_, 0, v___x_2802_);
return v___f_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v___f_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___f_2818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0);
v___x_2819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2820_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2819_, v___f_2818_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2828_, lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2836_, v_msg_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
return v_res_2843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = lean_box(0);
v___x_2846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2847_ = l_Lean_Expr_const___override(v___x_2846_, v___x_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2850_);
return v___x_2852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2853_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_box(1);
v___x_2855_ = l_Lean_MessageData_ofFormat(v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2860_ = l_Lean_MessageData_ofFormat(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2861_, lean_object* v_x_2862_){
_start:
{
if (lean_obj_tag(v_x_2862_) == 0)
{
return v_x_2861_;
}
else
{
lean_object* v_head_2863_; lean_object* v_tail_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2886_; 
v_head_2863_ = lean_ctor_get(v_x_2862_, 0);
v_tail_2864_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2866_ = v_x_2862_;
v_isShared_2867_ = v_isSharedCheck_2886_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_tail_2864_);
lean_inc(v_head_2863_);
lean_dec(v_x_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2886_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_before_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2884_; 
v_before_2868_ = lean_ctor_get(v_head_2863_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_head_2863_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_head_2863_, 1);
lean_dec(v_unused_2885_);
v___x_2870_ = v_head_2863_;
v_isShared_2871_ = v_isSharedCheck_2884_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_before_2868_);
lean_dec(v_head_2863_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2884_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 7);
lean_ctor_set(v___x_2870_, 1, v___x_2872_);
lean_ctor_set(v___x_2870_, 0, v_x_2861_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_x_2861_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2867_ == 0)
{
lean_ctor_set_tag(v___x_2866_, 7);
lean_ctor_set(v___x_2866_, 1, v___x_2875_);
lean_ctor_set(v___x_2866_, 0, v___x_2874_);
v___x_2877_ = v___x_2866_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = l_Lean_MessageData_ofSyntax(v_before_2868_);
v___x_2879_ = l_Lean_indentD(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2877_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v_x_2861_ = v___x_2880_;
v_x_2862_ = v_tail_2864_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2887_, lean_object* v_opt_2888_){
_start:
{
lean_object* v_name_2889_; lean_object* v_defValue_2890_; lean_object* v_map_2891_; lean_object* v___x_2892_; 
v_name_2889_ = lean_ctor_get(v_opt_2888_, 0);
v_defValue_2890_ = lean_ctor_get(v_opt_2888_, 1);
v_map_2891_ = lean_ctor_get(v_opts_2887_, 0);
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2891_, v_name_2889_);
if (lean_obj_tag(v___x_2892_) == 0)
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_unbox(v_defValue_2890_);
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; 
v_val_2894_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_val_2894_);
lean_dec_ref_known(v___x_2892_, 1);
if (lean_obj_tag(v_val_2894_) == 1)
{
uint8_t v_v_2895_; 
v_v_2895_ = lean_ctor_get_uint8(v_val_2894_, 0);
lean_dec_ref_known(v_val_2894_, 0);
return v_v_2895_;
}
else
{
uint8_t v___x_2896_; 
lean_dec(v_val_2894_);
v___x_2896_ = lean_unbox(v_defValue_2890_);
return v___x_2896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2897_, lean_object* v_opt_2898_){
_start:
{
uint8_t v_res_2899_; lean_object* v_r_2900_; 
v_res_2899_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2897_, v_opt_2898_);
lean_dec_ref(v_opt_2898_);
lean_dec_ref(v_opts_2897_);
v_r_2900_ = lean_box(v_res_2899_);
return v_r_2900_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2905_ = l_Lean_MessageData_ofFormat(v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2906_, lean_object* v_macroStack_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_toCold_2910_; lean_object* v_options_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v_toCold_2910_ = lean_ctor_get(v___y_2908_, 0);
v_options_2911_ = lean_ctor_get(v_toCold_2910_, 2);
v___x_2912_ = l_Lean_Elab_pp_macroStack;
v___x_2913_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_2911_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; 
lean_dec(v_macroStack_2907_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_msgData_2906_);
return v___x_2914_;
}
else
{
if (lean_obj_tag(v_macroStack_2907_) == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_msgData_2906_);
return v___x_2915_;
}
else
{
lean_object* v_head_2916_; lean_object* v_after_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2932_; 
v_head_2916_ = lean_ctor_get(v_macroStack_2907_, 0);
lean_inc(v_head_2916_);
v_after_2917_ = lean_ctor_get(v_head_2916_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_head_2916_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v_head_2916_, 0);
lean_dec(v_unused_2933_);
v___x_2919_ = v_head_2916_;
v_isShared_2920_ = v_isSharedCheck_2932_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_after_2917_);
lean_dec(v_head_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2932_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2921_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 7);
lean_ctor_set(v___x_2919_, 1, v___x_2921_);
lean_ctor_set(v___x_2919_, 0, v_msgData_2906_);
v___x_2923_ = v___x_2919_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_msgData_2906_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v_msgData_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2924_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l_Lean_MessageData_ofSyntax(v_after_2917_);
v___x_2927_ = l_Lean_indentD(v___x_2926_);
v_msgData_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2928_, 0, v___x_2925_);
lean_ctor_set(v_msgData_2928_, 1, v___x_2927_);
v___x_2929_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_2928_, v_macroStack_2907_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_2934_, lean_object* v_macroStack_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2934_, v_macroStack_2935_, v___y_2936_);
lean_dec_ref(v___y_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_ref_2947_; lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v_macroStack_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
v_ref_2947_ = lean_ctor_get(v___y_2944_, 2);
v___x_2948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2939_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v_macroStack_2950_ = lean_ctor_get(v___y_2940_, 1);
v___x_2951_ = l_Lean_Elab_getBetterRef(v_ref_2947_, v_macroStack_2950_);
lean_inc(v_macroStack_2950_);
v___x_2952_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_2949_, v_macroStack_2950_, v___y_2944_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2951_);
lean_ctor_set(v___x_2957_, 1, v_a_2953_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 1);
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v___x_2974_; 
v___x_2974_ = l_Lean_Expr_hasMVar(v_e_2971_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_e_2971_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v_mctx_2977_; lean_object* v___x_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2981_; lean_object* v_cache_2982_; lean_object* v_zetaDeltaFVarIds_2983_; lean_object* v_postponed_2984_; lean_object* v_diag_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2994_; 
v___x_2976_ = lean_st_ref_get(v___y_2972_);
v_mctx_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_mctx_2977_);
lean_dec(v___x_2976_);
v___x_2978_ = l_Lean_instantiateMVarsCore(v_mctx_2977_, v_e_2971_);
v_fst_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_fst_2979_);
v_snd_2980_ = lean_ctor_get(v___x_2978_, 1);
lean_inc(v_snd_2980_);
lean_dec_ref(v___x_2978_);
v___x_2981_ = lean_st_ref_take(v___y_2972_);
v_cache_2982_ = lean_ctor_get(v___x_2981_, 1);
v_zetaDeltaFVarIds_2983_ = lean_ctor_get(v___x_2981_, 2);
v_postponed_2984_ = lean_ctor_get(v___x_2981_, 3);
v_diag_2985_ = lean_ctor_get(v___x_2981_, 4);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2995_);
v___x_2987_ = v___x_2981_;
v_isShared_2988_ = v_isSharedCheck_2994_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_diag_2985_);
lean_inc(v_postponed_2984_);
lean_inc(v_zetaDeltaFVarIds_2983_);
lean_inc(v_cache_2982_);
lean_dec(v___x_2981_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2994_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v_snd_2980_);
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_snd_2980_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_cache_2982_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_zetaDeltaFVarIds_2983_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_postponed_2984_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_diag_2985_);
v___x_2990_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_st_ref_put(v___y_2972_, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_fst_2979_);
return v___x_2992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_2996_, v___y_2997_);
lean_dec(v___y_2997_);
return v_res_2999_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = l_Lean_Elab_abortTermExceptionId;
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___x_3000_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_3007_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_3015_ = l_Lean_Expr_const___override(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3016_; lean_object* v_ty_x3f_3017_; 
v___x_3016_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3017_, 0, v___x_3016_);
return v_ty_x3f_3017_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_3022_ = l_Lean_MessageData_ofExpr(v___x_3021_);
return v___x_3022_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_3024_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3023_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3027_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_3034_ = l_Lean_stringToMessageData(v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_ty_x3f_3043_; uint8_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_toCold_3049_; lean_object* v_currRecDepth_3050_; lean_object* v_ref_3051_; uint8_t v_diag_3052_; uint8_t v_suppressElabErrors_3053_; uint8_t v___x_3054_; lean_object* v_ref_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_ty_x3f_3043_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_3044_ = 1;
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_box(v___x_3044_);
v___x_3047_ = lean_box(v___x_3044_);
lean_inc(v_stx_3035_);
v___x_3048_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3048_, 0, v_stx_3035_);
lean_closure_set(v___x_3048_, 1, v_ty_x3f_3043_);
lean_closure_set(v___x_3048_, 2, v___x_3046_);
lean_closure_set(v___x_3048_, 3, v___x_3047_);
lean_closure_set(v___x_3048_, 4, v___x_3045_);
v_toCold_3049_ = lean_ctor_get(v_a_3040_, 0);
v_currRecDepth_3050_ = lean_ctor_get(v_a_3040_, 1);
v_ref_3051_ = lean_ctor_get(v_a_3040_, 2);
v_diag_3052_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*3);
v_suppressElabErrors_3053_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*3 + 1);
v___x_3054_ = 1;
v_ref_3055_ = l_Lean_replaceRef(v_stx_3035_, v_ref_3051_);
lean_dec(v_stx_3035_);
lean_inc(v_currRecDepth_3050_);
lean_inc_ref(v_toCold_3049_);
v___x_3056_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3056_, 0, v_toCold_3049_);
lean_ctor_set(v___x_3056_, 1, v_currRecDepth_3050_);
lean_ctor_set(v___x_3056_, 2, v_ref_3055_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*3, v_diag_3052_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*3 + 1, v_suppressElabErrors_3053_);
v___x_3057_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3048_, v___x_3054_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v___x_3056_, v_a_3041_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v_a_3060_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; uint8_t v___x_3155_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3058_, v_a_3039_);
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3155_ = l_Lean_Expr_hasSorry(v_a_3060_);
if (v___x_3155_ == 0)
{
v___y_3100_ = v_a_3036_;
v___y_3101_ = v_a_3037_;
v___y_3102_ = v_a_3038_;
v___y_3103_ = v_a_3039_;
v___y_3104_ = v___x_3056_;
v___y_3105_ = v_a_3041_;
goto v___jp_3099_;
}
else
{
uint8_t v___x_3156_; 
v___x_3156_ = l_Lean_Expr_hasSyntheticSorry(v_a_3060_);
if (v___x_3156_ == 0)
{
v___y_3137_ = v_a_3036_;
v___y_3138_ = v_a_3037_;
v___y_3139_ = v_a_3038_;
v___y_3140_ = v_a_3039_;
v___y_3141_ = v___x_3056_;
v___y_3142_ = v_a_3041_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3157_; lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_a_3060_);
lean_dec_ref_known(v___x_3056_, 3);
v___x_3157_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
v___jp_3061_:
{
if (v___y_3071_ == 0)
{
if (lean_obj_tag(v___y_3062_) == 0)
{
lean_dec_ref_known(v___y_3062_, 2);
lean_dec_ref(v___y_3065_);
lean_dec(v_a_3060_);
return v___y_3070_;
}
else
{
lean_object* v_id_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3085_; 
v_id_3072_ = lean_ctor_get(v___y_3062_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___y_3062_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___y_3062_, 1);
lean_dec(v_unused_3086_);
v___x_3074_ = v___y_3062_;
v_isShared_3075_ = v_isSharedCheck_3085_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_id_3072_);
lean_dec(v___y_3062_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3085_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
uint8_t v___x_3076_; 
v___x_3076_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3068_, v_id_3072_);
lean_dec(v_id_3072_);
if (v___x_3076_ == 0)
{
lean_del_object(v___x_3074_);
lean_dec_ref(v___y_3065_);
lean_dec(v_a_3060_);
return v___y_3070_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
lean_dec_ref(v___y_3070_);
v___x_3077_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_3078_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3079_ = l_Lean_indentExpr(v_a_3060_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 7);
lean_ctor_set(v___x_3074_, 1, v___x_3079_);
lean_ctor_set(v___x_3074_, 0, v___x_3078_);
v___x_3081_ = v___x_3074_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3077_);
v___x_3083_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3082_, v___y_3063_, v___y_3067_, v___y_3066_, v___y_3069_, v___y_3065_, v___y_3064_);
lean_dec_ref(v___y_3065_);
return v___x_3083_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v_a_3060_);
return v___y_3070_;
}
}
v___jp_3087_:
{
lean_object* v___x_3094_; 
lean_inc(v_a_3060_);
v___x_3094_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_3060_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_dec_ref(v___y_3092_);
lean_dec(v_a_3060_);
return v___x_3094_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
v___x_3096_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3097_ = l_Lean_Exception_isInterrupt(v_a_3095_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; 
lean_inc(v_a_3095_);
v___x_3098_ = l_Lean_Exception_isRuntime(v_a_3095_);
v___y_3062_ = v_a_3095_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3093_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3090_;
v___y_3067_ = v___y_3089_;
v___y_3068_ = v___x_3096_;
v___y_3069_ = v___y_3091_;
v___y_3070_ = v___x_3094_;
v___y_3071_ = v___x_3098_;
goto v___jp_3061_;
}
else
{
v___y_3062_ = v_a_3095_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3093_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3090_;
v___y_3067_ = v___y_3089_;
v___y_3068_ = v___x_3096_;
v___y_3069_ = v___y_3091_;
v___y_3070_ = v___x_3094_;
v___y_3071_ = v___x_3097_;
goto v___jp_3061_;
}
}
}
v___jp_3099_:
{
lean_object* v___x_3106_; 
lean_inc(v_a_3060_);
v___x_3106_ = l_Lean_Meta_getMVars(v_a_3060_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3107_, v___x_3045_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v_a_3107_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; uint8_t v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = lean_unbox(v_a_3109_);
lean_dec(v_a_3109_);
if (v___x_3110_ == 0)
{
v___y_3088_ = v___y_3100_;
v___y_3089_ = v___y_3101_;
v___y_3090_ = v___y_3102_;
v___y_3091_ = v___y_3103_;
v___y_3092_ = v___y_3104_;
v___y_3093_ = v___y_3105_;
goto v___jp_3087_;
}
else
{
lean_object* v___x_3111_; lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___y_3104_);
lean_dec(v_a_3060_);
v___x_3111_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v___y_3104_);
lean_dec(v_a_3060_);
v_a_3120_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3108_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3108_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v___y_3104_);
lean_dec(v_a_3060_);
v_a_3128_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3106_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3106_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
v___jp_3136_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v___x_3143_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3144_ = l_Lean_indentExpr(v_a_3060_);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3145_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref(v___y_3141_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref_known(v___x_3056_, 3);
v_a_3166_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3057_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3057_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_toCold_3191_; lean_object* v_currRecDepth_3192_; lean_object* v_ref_3193_; uint8_t v_diag_3194_; uint8_t v_suppressElabErrors_3195_; lean_object* v_ref_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_toCold_3191_ = lean_ctor_get(v_a_3188_, 0);
v_currRecDepth_3192_ = lean_ctor_get(v_a_3188_, 1);
v_ref_3193_ = lean_ctor_get(v_a_3188_, 2);
v_diag_3194_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*3);
v_suppressElabErrors_3195_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*3 + 1);
v_ref_3196_ = l_Lean_replaceRef(v_stx_3183_, v_ref_3193_);
lean_inc(v_currRecDepth_3192_);
lean_inc_ref(v_toCold_3191_);
v___x_3197_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3197_, 0, v_toCold_3191_);
lean_ctor_set(v___x_3197_, 1, v_currRecDepth_3192_);
lean_ctor_set(v___x_3197_, 2, v_ref_3196_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*3, v_diag_3194_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*3 + 1, v_suppressElabErrors_3195_);
lean_inc(v_stx_3183_);
v___x_3198_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v___x_3197_, v_a_3189_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref_known(v___x_3197_, 3);
lean_dec(v_stx_3183_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_fst_3203_; lean_object* v___x_3205_; 
v_fst_3203_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_fst_3203_);
lean_dec(v_a_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_fst_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_fst_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3223_; 
v_a_3208_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3210_ = v___x_3198_;
v_isShared_3211_ = v_isSharedCheck_3223_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3198_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3223_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3208_);
if (v_isShared_3211_ == 0)
{
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3208_);
v___x_3214_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
uint8_t v___y_3216_; uint8_t v___x_3220_; 
v___x_3220_ = l_Lean_Exception_isInterrupt(v_a_3208_);
if (v___x_3220_ == 0)
{
uint8_t v___x_3221_; 
lean_inc(v_a_3208_);
v___x_3221_ = l_Lean_Exception_isRuntime(v_a_3208_);
v___y_3216_ = v___x_3221_;
goto v___jp_3215_;
}
else
{
v___y_3216_ = v___x_3220_;
goto v___jp_3215_;
}
v___jp_3215_:
{
if (v___y_3216_ == 0)
{
if (lean_obj_tag(v_a_3208_) == 0)
{
lean_dec_ref_known(v_a_3208_, 2);
lean_dec_ref_known(v___x_3197_, 3);
lean_dec(v_stx_3183_);
return v___x_3214_;
}
else
{
lean_object* v_id_3217_; uint8_t v___x_3218_; 
v_id_3217_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_id_3217_);
lean_dec_ref_known(v_a_3208_, 2);
v___x_3218_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3212_, v_id_3217_);
lean_dec(v_id_3217_);
if (v___x_3218_ == 0)
{
lean_dec_ref_known(v___x_3197_, 3);
lean_dec(v_stx_3183_);
return v___x_3214_;
}
else
{
lean_object* v___x_3219_; 
lean_dec_ref(v___x_3214_);
v___x_3219_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v___x_3197_, v_a_3189_);
lean_dec_ref_known(v___x_3197_, 3);
return v___x_3219_;
}
}
}
else
{
lean_dec(v_a_3208_);
lean_dec_ref_known(v___x_3197_, 3);
lean_dec(v_stx_3183_);
return v___x_3214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
return v_res_3232_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_box(0);
v___x_3239_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3240_ = l_Lean_Expr_const___override(v___x_3239_, v___x_3238_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3241_; lean_object* v_ty_x3f_3242_; 
v___x_3241_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3242_, 0, v___x_3241_);
return v_ty_x3f_3242_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3244_ = l_Lean_MessageData_ofExpr(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3246_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set(v___x_3247_, 1, v___x_3245_);
return v___x_3247_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3249_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v___x_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_ty_x3f_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_toCold_3265_; lean_object* v_currRecDepth_3266_; lean_object* v_ref_3267_; uint8_t v_diag_3268_; uint8_t v_suppressElabErrors_3269_; uint8_t v___x_3270_; lean_object* v_ref_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_ty_x3f_3259_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3260_ = 1;
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_box(v___x_3260_);
v___x_3263_ = lean_box(v___x_3260_);
lean_inc(v_stx_3251_);
v___x_3264_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3264_, 0, v_stx_3251_);
lean_closure_set(v___x_3264_, 1, v_ty_x3f_3259_);
lean_closure_set(v___x_3264_, 2, v___x_3262_);
lean_closure_set(v___x_3264_, 3, v___x_3263_);
lean_closure_set(v___x_3264_, 4, v___x_3261_);
v_toCold_3265_ = lean_ctor_get(v_a_3256_, 0);
v_currRecDepth_3266_ = lean_ctor_get(v_a_3256_, 1);
v_ref_3267_ = lean_ctor_get(v_a_3256_, 2);
v_diag_3268_ = lean_ctor_get_uint8(v_a_3256_, sizeof(void*)*3);
v_suppressElabErrors_3269_ = lean_ctor_get_uint8(v_a_3256_, sizeof(void*)*3 + 1);
v___x_3270_ = 1;
v_ref_3271_ = l_Lean_replaceRef(v_stx_3251_, v_ref_3267_);
lean_dec(v_stx_3251_);
lean_inc(v_currRecDepth_3266_);
lean_inc_ref(v_toCold_3265_);
v___x_3272_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3272_, 0, v_toCold_3265_);
lean_ctor_set(v___x_3272_, 1, v_currRecDepth_3266_);
lean_ctor_set(v___x_3272_, 2, v_ref_3271_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*3, v_diag_3268_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*3 + 1, v_suppressElabErrors_3269_);
v___x_3273_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3264_, v___x_3270_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v___x_3272_, v_a_3257_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; lean_object* v_a_3276_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; uint8_t v___y_3287_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; uint8_t v___x_3371_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v___x_3275_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3274_, v_a_3255_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref(v___x_3275_);
v___x_3371_ = l_Lean_Expr_hasSorry(v_a_3276_);
if (v___x_3371_ == 0)
{
v___y_3316_ = v_a_3252_;
v___y_3317_ = v_a_3253_;
v___y_3318_ = v_a_3254_;
v___y_3319_ = v_a_3255_;
v___y_3320_ = v___x_3272_;
v___y_3321_ = v_a_3257_;
goto v___jp_3315_;
}
else
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_Expr_hasSyntheticSorry(v_a_3276_);
if (v___x_3372_ == 0)
{
v___y_3353_ = v_a_3252_;
v___y_3354_ = v_a_3253_;
v___y_3355_ = v_a_3254_;
v___y_3356_ = v_a_3255_;
v___y_3357_ = v___x_3272_;
v___y_3358_ = v_a_3257_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3373_; lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_a_3276_);
lean_dec_ref_known(v___x_3272_, 3);
v___x_3373_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
v___jp_3277_:
{
if (v___y_3287_ == 0)
{
if (lean_obj_tag(v___y_3280_) == 0)
{
lean_dec_ref_known(v___y_3280_, 2);
lean_dec_ref(v___y_3283_);
lean_dec(v_a_3276_);
return v___y_3279_;
}
else
{
lean_object* v_id_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3301_; 
v_id_3288_ = lean_ctor_get(v___y_3280_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___y_3280_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___y_3280_, 1);
lean_dec(v_unused_3302_);
v___x_3290_ = v___y_3280_;
v_isShared_3291_ = v_isSharedCheck_3301_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_id_3288_);
lean_dec(v___y_3280_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3301_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
uint8_t v___x_3292_; 
v___x_3292_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3281_, v_id_3288_);
lean_dec(v_id_3288_);
if (v___x_3292_ == 0)
{
lean_del_object(v___x_3290_);
lean_dec_ref(v___y_3283_);
lean_dec(v_a_3276_);
return v___y_3279_;
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_dec_ref(v___y_3279_);
v___x_3293_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3294_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3295_ = l_Lean_indentExpr(v_a_3276_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 7);
lean_ctor_set(v___x_3290_, 1, v___x_3295_);
lean_ctor_set(v___x_3290_, 0, v___x_3294_);
v___x_3297_ = v___x_3290_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3293_);
v___x_3299_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3298_, v___y_3282_, v___y_3284_, v___y_3286_, v___y_3285_, v___y_3283_, v___y_3278_);
lean_dec_ref(v___y_3283_);
return v___x_3299_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3283_);
lean_dec_ref(v___y_3280_);
lean_dec(v_a_3276_);
return v___y_3279_;
}
}
v___jp_3303_:
{
lean_object* v___x_3310_; 
lean_inc(v_a_3276_);
v___x_3310_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3276_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_dec_ref(v___y_3308_);
lean_dec(v_a_3276_);
return v___x_3310_;
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
v___x_3312_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3313_ = l_Lean_Exception_isInterrupt(v_a_3311_);
if (v___x_3313_ == 0)
{
uint8_t v___x_3314_; 
lean_inc(v_a_3311_);
v___x_3314_ = l_Lean_Exception_isRuntime(v_a_3311_);
v___y_3278_ = v___y_3309_;
v___y_3279_ = v___x_3310_;
v___y_3280_ = v_a_3311_;
v___y_3281_ = v___x_3312_;
v___y_3282_ = v___y_3304_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3305_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___y_3306_;
v___y_3287_ = v___x_3314_;
goto v___jp_3277_;
}
else
{
v___y_3278_ = v___y_3309_;
v___y_3279_ = v___x_3310_;
v___y_3280_ = v_a_3311_;
v___y_3281_ = v___x_3312_;
v___y_3282_ = v___y_3304_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3305_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___y_3306_;
v___y_3287_ = v___x_3313_;
goto v___jp_3277_;
}
}
}
v___jp_3315_:
{
lean_object* v___x_3322_; 
lean_inc(v_a_3276_);
v___x_3322_ = l_Lean_Meta_getMVars(v_a_3276_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3323_, v___x_3261_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v_a_3323_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; uint8_t v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = lean_unbox(v_a_3325_);
lean_dec(v_a_3325_);
if (v___x_3326_ == 0)
{
v___y_3304_ = v___y_3316_;
v___y_3305_ = v___y_3317_;
v___y_3306_ = v___y_3318_;
v___y_3307_ = v___y_3319_;
v___y_3308_ = v___y_3320_;
v___y_3309_ = v___y_3321_;
goto v___jp_3303_;
}
else
{
lean_object* v___x_3327_; lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec_ref(v___y_3320_);
lean_dec(v_a_3276_);
v___x_3327_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___y_3320_);
lean_dec(v_a_3276_);
v_a_3336_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3324_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3324_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v___y_3320_);
lean_dec(v_a_3276_);
v_a_3344_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3322_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3322_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
v___jp_3352_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
v___x_3359_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3360_ = l_Lean_indentExpr(v_a_3276_);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3361_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec_ref(v___y_3357_);
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref_known(v___x_3272_, 3);
v_a_3382_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3273_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3273_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_toCold_3407_; lean_object* v_currRecDepth_3408_; lean_object* v_ref_3409_; uint8_t v_diag_3410_; uint8_t v_suppressElabErrors_3411_; lean_object* v_ref_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_toCold_3407_ = lean_ctor_get(v_a_3404_, 0);
v_currRecDepth_3408_ = lean_ctor_get(v_a_3404_, 1);
v_ref_3409_ = lean_ctor_get(v_a_3404_, 2);
v_diag_3410_ = lean_ctor_get_uint8(v_a_3404_, sizeof(void*)*3);
v_suppressElabErrors_3411_ = lean_ctor_get_uint8(v_a_3404_, sizeof(void*)*3 + 1);
v_ref_3412_ = l_Lean_replaceRef(v_stx_3399_, v_ref_3409_);
lean_inc(v_currRecDepth_3408_);
lean_inc_ref(v_toCold_3407_);
v___x_3413_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3413_, 0, v_toCold_3407_);
lean_ctor_set(v___x_3413_, 1, v_currRecDepth_3408_);
lean_ctor_set(v___x_3413_, 2, v_ref_3412_);
lean_ctor_set_uint8(v___x_3413_, sizeof(void*)*3, v_diag_3410_);
lean_ctor_set_uint8(v___x_3413_, sizeof(void*)*3 + 1, v_suppressElabErrors_3411_);
lean_inc(v_stx_3399_);
v___x_3414_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v___x_3413_, v_a_3405_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref_known(v___x_3413_, 3);
lean_dec(v_stx_3399_);
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v___x_3421_; 
v_fst_3419_ = lean_ctor_get(v_a_3415_, 0);
lean_inc(v_fst_3419_);
lean_dec(v_a_3415_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v_fst_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_fst_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3439_; 
v_a_3424_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3426_ = v___x_3414_;
v_isShared_3427_ = v_isSharedCheck_3439_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3414_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3439_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3428_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3424_);
if (v_isShared_3427_ == 0)
{
v___x_3430_ = v___x_3426_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3424_);
v___x_3430_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
uint8_t v___y_3432_; uint8_t v___x_3436_; 
v___x_3436_ = l_Lean_Exception_isInterrupt(v_a_3424_);
if (v___x_3436_ == 0)
{
uint8_t v___x_3437_; 
lean_inc(v_a_3424_);
v___x_3437_ = l_Lean_Exception_isRuntime(v_a_3424_);
v___y_3432_ = v___x_3437_;
goto v___jp_3431_;
}
else
{
v___y_3432_ = v___x_3436_;
goto v___jp_3431_;
}
v___jp_3431_:
{
if (v___y_3432_ == 0)
{
if (lean_obj_tag(v_a_3424_) == 0)
{
lean_dec_ref_known(v_a_3424_, 2);
lean_dec_ref_known(v___x_3413_, 3);
lean_dec(v_stx_3399_);
return v___x_3430_;
}
else
{
lean_object* v_id_3433_; uint8_t v___x_3434_; 
v_id_3433_ = lean_ctor_get(v_a_3424_, 0);
lean_inc(v_id_3433_);
lean_dec_ref_known(v_a_3424_, 2);
v___x_3434_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3428_, v_id_3433_);
lean_dec(v_id_3433_);
if (v___x_3434_ == 0)
{
lean_dec_ref_known(v___x_3413_, 3);
lean_dec(v_stx_3399_);
return v___x_3430_;
}
else
{
lean_object* v___x_3435_; 
lean_dec_ref(v___x_3430_);
v___x_3435_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v___x_3413_, v_a_3405_);
lean_dec_ref_known(v___x_3413_, 3);
return v___x_3435_;
}
}
}
else
{
lean_dec(v_a_3424_);
lean_dec_ref_known(v___x_3413_, 3);
lean_dec(v_stx_3399_);
return v___x_3430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
return v_res_3448_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3450_ = l_Lean_MessageData_ofExpr(v___x_3449_);
return v___x_3450_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3452_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v___x_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3455_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
lean_ctor_set(v___x_3456_, 1, v___x_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_ty_x3f_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v_toCold_3471_; lean_object* v_currRecDepth_3472_; lean_object* v_ref_3473_; uint8_t v_diag_3474_; uint8_t v_suppressElabErrors_3475_; uint8_t v___x_3476_; lean_object* v_ref_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_ty_x3f_3465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3466_ = 1;
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_box(v___x_3466_);
v___x_3469_ = lean_box(v___x_3466_);
lean_inc(v_stx_3457_);
v___x_3470_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3470_, 0, v_stx_3457_);
lean_closure_set(v___x_3470_, 1, v_ty_x3f_3465_);
lean_closure_set(v___x_3470_, 2, v___x_3468_);
lean_closure_set(v___x_3470_, 3, v___x_3469_);
lean_closure_set(v___x_3470_, 4, v___x_3467_);
v_toCold_3471_ = lean_ctor_get(v_a_3462_, 0);
v_currRecDepth_3472_ = lean_ctor_get(v_a_3462_, 1);
v_ref_3473_ = lean_ctor_get(v_a_3462_, 2);
v_diag_3474_ = lean_ctor_get_uint8(v_a_3462_, sizeof(void*)*3);
v_suppressElabErrors_3475_ = lean_ctor_get_uint8(v_a_3462_, sizeof(void*)*3 + 1);
v___x_3476_ = 1;
v_ref_3477_ = l_Lean_replaceRef(v_stx_3457_, v_ref_3473_);
lean_dec(v_stx_3457_);
lean_inc(v_currRecDepth_3472_);
lean_inc_ref(v_toCold_3471_);
v___x_3478_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3478_, 0, v_toCold_3471_);
lean_ctor_set(v___x_3478_, 1, v_currRecDepth_3472_);
lean_ctor_set(v___x_3478_, 2, v_ref_3477_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*3, v_diag_3474_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*3 + 1, v_suppressElabErrors_3475_);
v___x_3479_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3470_, v___x_3476_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v___x_3478_, v_a_3463_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v_a_3482_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; uint8_t v___x_3577_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3480_, v_a_3461_);
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3577_ = l_Lean_Expr_hasSorry(v_a_3482_);
if (v___x_3577_ == 0)
{
v___y_3522_ = v_a_3458_;
v___y_3523_ = v_a_3459_;
v___y_3524_ = v_a_3460_;
v___y_3525_ = v_a_3461_;
v___y_3526_ = v___x_3478_;
v___y_3527_ = v_a_3463_;
goto v___jp_3521_;
}
else
{
uint8_t v___x_3578_; 
v___x_3578_ = l_Lean_Expr_hasSyntheticSorry(v_a_3482_);
if (v___x_3578_ == 0)
{
v___y_3559_ = v_a_3458_;
v___y_3560_ = v_a_3459_;
v___y_3561_ = v_a_3460_;
v___y_3562_ = v_a_3461_;
v___y_3563_ = v___x_3478_;
v___y_3564_ = v_a_3463_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3579_; lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_a_3482_);
lean_dec_ref_known(v___x_3478_, 3);
v___x_3579_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
v___jp_3483_:
{
if (v___y_3493_ == 0)
{
if (lean_obj_tag(v___y_3490_) == 0)
{
lean_dec_ref_known(v___y_3490_, 2);
lean_dec_ref(v___y_3489_);
lean_dec(v_a_3482_);
return v___y_3487_;
}
else
{
lean_object* v_id_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3507_; 
v_id_3494_ = lean_ctor_get(v___y_3490_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___y_3490_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v___y_3490_, 1);
lean_dec(v_unused_3508_);
v___x_3496_ = v___y_3490_;
v_isShared_3497_ = v_isSharedCheck_3507_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_id_3494_);
lean_dec(v___y_3490_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3507_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
uint8_t v___x_3498_; 
v___x_3498_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3485_, v_id_3494_);
lean_dec(v_id_3494_);
if (v___x_3498_ == 0)
{
lean_del_object(v___x_3496_);
lean_dec_ref(v___y_3489_);
lean_dec(v_a_3482_);
return v___y_3487_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
lean_dec_ref(v___y_3487_);
v___x_3499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3500_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3501_ = l_Lean_indentExpr(v_a_3482_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 7);
lean_ctor_set(v___x_3496_, 1, v___x_3501_);
lean_ctor_set(v___x_3496_, 0, v___x_3500_);
v___x_3503_ = v___x_3496_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3499_);
v___x_3505_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3504_, v___y_3484_, v___y_3492_, v___y_3486_, v___y_3488_, v___y_3489_, v___y_3491_);
lean_dec_ref(v___y_3489_);
return v___x_3505_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v_a_3482_);
return v___y_3487_;
}
}
v___jp_3509_:
{
lean_object* v___x_3516_; 
lean_inc(v_a_3482_);
v___x_3516_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3482_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_dec_ref(v___y_3514_);
lean_dec(v_a_3482_);
return v___x_3516_;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
v___x_3518_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3519_ = l_Lean_Exception_isInterrupt(v_a_3517_);
if (v___x_3519_ == 0)
{
uint8_t v___x_3520_; 
lean_inc(v_a_3517_);
v___x_3520_ = l_Lean_Exception_isRuntime(v_a_3517_);
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___x_3518_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___x_3516_;
v___y_3488_ = v___y_3513_;
v___y_3489_ = v___y_3514_;
v___y_3490_ = v_a_3517_;
v___y_3491_ = v___y_3515_;
v___y_3492_ = v___y_3511_;
v___y_3493_ = v___x_3520_;
goto v___jp_3483_;
}
else
{
v___y_3484_ = v___y_3510_;
v___y_3485_ = v___x_3518_;
v___y_3486_ = v___y_3512_;
v___y_3487_ = v___x_3516_;
v___y_3488_ = v___y_3513_;
v___y_3489_ = v___y_3514_;
v___y_3490_ = v_a_3517_;
v___y_3491_ = v___y_3515_;
v___y_3492_ = v___y_3511_;
v___y_3493_ = v___x_3519_;
goto v___jp_3483_;
}
}
}
v___jp_3521_:
{
lean_object* v___x_3528_; 
lean_inc(v_a_3482_);
v___x_3528_ = l_Lean_Meta_getMVars(v_a_3482_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3529_, v___x_3467_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v_a_3529_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; uint8_t v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = lean_unbox(v_a_3531_);
lean_dec(v_a_3531_);
if (v___x_3532_ == 0)
{
v___y_3510_ = v___y_3522_;
v___y_3511_ = v___y_3523_;
v___y_3512_ = v___y_3524_;
v___y_3513_ = v___y_3525_;
v___y_3514_ = v___y_3526_;
v___y_3515_ = v___y_3527_;
goto v___jp_3509_;
}
else
{
lean_object* v___x_3533_; lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v___y_3526_);
lean_dec(v_a_3482_);
v___x_3533_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref(v___y_3526_);
lean_dec(v_a_3482_);
v_a_3542_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3530_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3530_);
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
lean_dec_ref(v___y_3526_);
lean_dec(v_a_3482_);
v_a_3550_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3528_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3528_);
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
v___jp_3558_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
v___x_3565_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3566_ = l_Lean_indentExpr(v_a_3482_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3567_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec_ref(v___y_3563_);
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
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref_known(v___x_3478_, 3);
v_a_3588_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3479_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3479_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3604_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = lean_box(0);
v___x_3611_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3612_ = l_Lean_Expr_const___override(v___x_3611_, v___x_3610_);
return v___x_3612_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3613_; lean_object* v_ty_x3f_3614_; 
v___x_3613_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3614_, 0, v___x_3613_);
return v_ty_x3f_3614_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3616_ = l_Lean_MessageData_ofExpr(v___x_3615_);
return v___x_3616_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3618_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
lean_ctor_set(v___x_3619_, 1, v___x_3617_);
return v___x_3619_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_foldRWRulesSeq_go___redArg___closed__3);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v___x_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_ty_x3f_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_toCold_3637_; lean_object* v_currRecDepth_3638_; lean_object* v_ref_3639_; uint8_t v_diag_3640_; uint8_t v_suppressElabErrors_3641_; uint8_t v___x_3642_; lean_object* v_ref_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_ty_x3f_3631_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3632_ = 1;
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_box(v___x_3632_);
v___x_3635_ = lean_box(v___x_3632_);
lean_inc(v_stx_3623_);
v___x_3636_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3636_, 0, v_stx_3623_);
lean_closure_set(v___x_3636_, 1, v_ty_x3f_3631_);
lean_closure_set(v___x_3636_, 2, v___x_3634_);
lean_closure_set(v___x_3636_, 3, v___x_3635_);
lean_closure_set(v___x_3636_, 4, v___x_3633_);
v_toCold_3637_ = lean_ctor_get(v_a_3628_, 0);
v_currRecDepth_3638_ = lean_ctor_get(v_a_3628_, 1);
v_ref_3639_ = lean_ctor_get(v_a_3628_, 2);
v_diag_3640_ = lean_ctor_get_uint8(v_a_3628_, sizeof(void*)*3);
v_suppressElabErrors_3641_ = lean_ctor_get_uint8(v_a_3628_, sizeof(void*)*3 + 1);
v___x_3642_ = 1;
v_ref_3643_ = l_Lean_replaceRef(v_stx_3623_, v_ref_3639_);
lean_dec(v_stx_3623_);
lean_inc(v_currRecDepth_3638_);
lean_inc_ref(v_toCold_3637_);
v___x_3644_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3644_, 0, v_toCold_3637_);
lean_ctor_set(v___x_3644_, 1, v_currRecDepth_3638_);
lean_ctor_set(v___x_3644_, 2, v_ref_3643_);
lean_ctor_set_uint8(v___x_3644_, sizeof(void*)*3, v_diag_3640_);
lean_ctor_set_uint8(v___x_3644_, sizeof(void*)*3 + 1, v_suppressElabErrors_3641_);
v___x_3645_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3636_, v___x_3642_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v___x_3644_, v_a_3629_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v_a_3648_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3659_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___x_3743_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3646_, v_a_3627_);
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref(v___x_3647_);
v___x_3743_ = l_Lean_Expr_hasSorry(v_a_3648_);
if (v___x_3743_ == 0)
{
v___y_3688_ = v_a_3624_;
v___y_3689_ = v_a_3625_;
v___y_3690_ = v_a_3626_;
v___y_3691_ = v_a_3627_;
v___y_3692_ = v___x_3644_;
v___y_3693_ = v_a_3629_;
goto v___jp_3687_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Lean_Expr_hasSyntheticSorry(v_a_3648_);
if (v___x_3744_ == 0)
{
v___y_3725_ = v_a_3624_;
v___y_3726_ = v_a_3625_;
v___y_3727_ = v_a_3626_;
v___y_3728_ = v_a_3627_;
v___y_3729_ = v___x_3644_;
v___y_3730_ = v_a_3629_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3745_; lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3648_);
lean_dec_ref_known(v___x_3644_, 3);
v___x_3745_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
v___jp_3649_:
{
if (v___y_3659_ == 0)
{
if (lean_obj_tag(v___y_3658_) == 0)
{
lean_dec_ref_known(v___y_3658_, 2);
lean_dec_ref(v___y_3657_);
lean_dec(v_a_3648_);
return v___y_3650_;
}
else
{
lean_object* v_id_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3673_; 
v_id_3660_ = lean_ctor_get(v___y_3658_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___y_3658_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___y_3658_, 1);
lean_dec(v_unused_3674_);
v___x_3662_ = v___y_3658_;
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_id_3660_);
lean_dec(v___y_3658_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
uint8_t v___x_3664_; 
v___x_3664_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3652_, v_id_3660_);
lean_dec(v_id_3660_);
if (v___x_3664_ == 0)
{
lean_del_object(v___x_3662_);
lean_dec_ref(v___y_3657_);
lean_dec(v_a_3648_);
return v___y_3650_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_dec_ref(v___y_3650_);
v___x_3665_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3666_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3667_ = l_Lean_indentExpr(v_a_3648_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set_tag(v___x_3662_, 7);
lean_ctor_set(v___x_3662_, 1, v___x_3667_);
lean_ctor_set(v___x_3662_, 0, v___x_3666_);
v___x_3669_ = v___x_3662_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___x_3665_);
v___x_3671_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3670_, v___y_3655_, v___y_3654_, v___y_3653_, v___y_3651_, v___y_3657_, v___y_3656_);
lean_dec_ref(v___y_3657_);
return v___x_3671_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v_a_3648_);
return v___y_3650_;
}
}
v___jp_3675_:
{
lean_object* v___x_3682_; 
lean_inc(v_a_3648_);
v___x_3682_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3648_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref(v___y_3680_);
lean_dec(v_a_3648_);
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
v___x_3684_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3685_ = l_Lean_Exception_isInterrupt(v_a_3683_);
if (v___x_3685_ == 0)
{
uint8_t v___x_3686_; 
lean_inc(v_a_3683_);
v___x_3686_ = l_Lean_Exception_isRuntime(v_a_3683_);
v___y_3650_ = v___x_3682_;
v___y_3651_ = v___y_3679_;
v___y_3652_ = v___x_3684_;
v___y_3653_ = v___y_3678_;
v___y_3654_ = v___y_3677_;
v___y_3655_ = v___y_3676_;
v___y_3656_ = v___y_3681_;
v___y_3657_ = v___y_3680_;
v___y_3658_ = v_a_3683_;
v___y_3659_ = v___x_3686_;
goto v___jp_3649_;
}
else
{
v___y_3650_ = v___x_3682_;
v___y_3651_ = v___y_3679_;
v___y_3652_ = v___x_3684_;
v___y_3653_ = v___y_3678_;
v___y_3654_ = v___y_3677_;
v___y_3655_ = v___y_3676_;
v___y_3656_ = v___y_3681_;
v___y_3657_ = v___y_3680_;
v___y_3658_ = v_a_3683_;
v___y_3659_ = v___x_3685_;
goto v___jp_3649_;
}
}
}
v___jp_3687_:
{
lean_object* v___x_3694_; 
lean_inc(v_a_3648_);
v___x_3694_ = l_Lean_Meta_getMVars(v_a_3648_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___x_3696_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3695_, v___x_3633_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v_a_3695_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; uint8_t v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
v___x_3698_ = lean_unbox(v_a_3697_);
lean_dec(v_a_3697_);
if (v___x_3698_ == 0)
{
v___y_3676_ = v___y_3688_;
v___y_3677_ = v___y_3689_;
v___y_3678_ = v___y_3690_;
v___y_3679_ = v___y_3691_;
v___y_3680_ = v___y_3692_;
v___y_3681_ = v___y_3693_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3699_; lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v___y_3692_);
lean_dec(v_a_3648_);
v___x_3699_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v___y_3692_);
lean_dec(v_a_3648_);
v_a_3708_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3696_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3696_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec_ref(v___y_3692_);
lean_dec(v_a_3648_);
v_a_3716_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3694_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3694_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
v___jp_3724_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v___x_3731_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3732_ = l_Lean_indentExpr(v_a_3648_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3733_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
lean_dec_ref(v___y_3729_);
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref_known(v___x_3644_, 3);
v_a_3754_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3645_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3645_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_toCold_3779_; lean_object* v_currRecDepth_3780_; lean_object* v_ref_3781_; uint8_t v_diag_3782_; uint8_t v_suppressElabErrors_3783_; lean_object* v_ref_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_toCold_3779_ = lean_ctor_get(v_a_3776_, 0);
v_currRecDepth_3780_ = lean_ctor_get(v_a_3776_, 1);
v_ref_3781_ = lean_ctor_get(v_a_3776_, 2);
v_diag_3782_ = lean_ctor_get_uint8(v_a_3776_, sizeof(void*)*3);
v_suppressElabErrors_3783_ = lean_ctor_get_uint8(v_a_3776_, sizeof(void*)*3 + 1);
v_ref_3784_ = l_Lean_replaceRef(v_stx_3771_, v_ref_3781_);
lean_inc(v_currRecDepth_3780_);
lean_inc_ref(v_toCold_3779_);
v___x_3785_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3785_, 0, v_toCold_3779_);
lean_ctor_set(v___x_3785_, 1, v_currRecDepth_3780_);
lean_ctor_set(v___x_3785_, 2, v_ref_3784_);
lean_ctor_set_uint8(v___x_3785_, sizeof(void*)*3, v_diag_3782_);
lean_ctor_set_uint8(v___x_3785_, sizeof(void*)*3 + 1, v_suppressElabErrors_3783_);
lean_inc(v_stx_3771_);
v___x_3786_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v___x_3785_, v_a_3777_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref_known(v___x_3785_, 3);
lean_dec(v_stx_3771_);
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_fst_3791_; lean_object* v___x_3793_; 
v_fst_3791_ = lean_ctor_get(v_a_3787_, 0);
lean_inc(v_fst_3791_);
lean_dec(v_a_3787_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v_fst_3791_);
v___x_3793_ = v___x_3789_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_fst_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3811_; 
v_a_3796_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3798_ = v___x_3786_;
v_isShared_3799_ = v_isSharedCheck_3811_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3786_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3811_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3800_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3796_);
if (v_isShared_3799_ == 0)
{
v___x_3802_ = v___x_3798_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3796_);
v___x_3802_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
uint8_t v___y_3804_; uint8_t v___x_3808_; 
v___x_3808_ = l_Lean_Exception_isInterrupt(v_a_3796_);
if (v___x_3808_ == 0)
{
uint8_t v___x_3809_; 
lean_inc(v_a_3796_);
v___x_3809_ = l_Lean_Exception_isRuntime(v_a_3796_);
v___y_3804_ = v___x_3809_;
goto v___jp_3803_;
}
else
{
v___y_3804_ = v___x_3808_;
goto v___jp_3803_;
}
v___jp_3803_:
{
if (v___y_3804_ == 0)
{
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_dec_ref_known(v_a_3796_, 2);
lean_dec_ref_known(v___x_3785_, 3);
lean_dec(v_stx_3771_);
return v___x_3802_;
}
else
{
lean_object* v_id_3805_; uint8_t v___x_3806_; 
v_id_3805_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_id_3805_);
lean_dec_ref_known(v_a_3796_, 2);
v___x_3806_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3800_, v_id_3805_);
lean_dec(v_id_3805_);
if (v___x_3806_ == 0)
{
lean_dec_ref_known(v___x_3785_, 3);
lean_dec(v_stx_3771_);
return v___x_3802_;
}
else
{
lean_object* v___x_3807_; 
lean_dec_ref(v___x_3802_);
v___x_3807_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v___x_3785_, v_a_3777_);
lean_dec_ref_known(v___x_3785_, 3);
return v___x_3807_;
}
}
}
else
{
lean_dec(v_a_3796_);
lean_dec_ref_known(v___x_3785_, 3);
lean_dec(v_stx_3771_);
return v___x_3802_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3852_, lean_object* v_item_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_item_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3872_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3853_, v___x_3871_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3872_) == 0)
{
uint8_t v___x_3873_; 
lean_dec_ref_known(v___x_3872_, 1);
v___x_3873_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3853_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3874_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3853_);
lean_inc_ref(v_item_3853_);
v___x_3875_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3853_);
v___x_3876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3877_ = lean_string_dec_eq(v___x_3874_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3879_ = lean_string_dec_eq(v___x_3874_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3881_ = lean_string_dec_eq(v___x_3874_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3883_ = lean_string_dec_eq(v___x_3874_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3885_ = lean_string_dec_eq(v___x_3874_, v___x_3884_);
lean_dec_ref(v___x_3874_);
if (v___x_3885_ == 0)
{
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3887_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3853_, v___x_3886_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3887_) == 0)
{
uint8_t v___x_3888_; 
lean_dec_ref_known(v___x_3887_, 1);
v___x_3888_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3875_);
if (v___x_3888_ == 0)
{
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3889_; 
lean_dec_ref(v___x_3875_);
lean_inc_ref(v_item_3853_);
v___x_3889_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_value_3890_; lean_object* v___x_3891_; 
lean_dec_ref_known(v___x_3889_, 1);
v_value_3890_ = lean_ctor_get(v_item_3853_, 2);
lean_inc(v_value_3890_);
lean_dec_ref(v_item_3853_);
v___x_3891_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3890_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3910_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3910_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3910_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
uint8_t v_offsetCnstrs_3896_; lean_object* v_occs_3897_; uint8_t v_newGoals_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3909_; 
v_offsetCnstrs_3896_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 1);
v_occs_3897_ = lean_ctor_get(v_config_3852_, 0);
v_newGoals_3898_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 2);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_config_3852_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3900_ = v_config_3852_;
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_occs_3897_);
lean_dec(v_config_3852_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_occs_3897_);
v___x_3903_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
uint8_t v___x_3904_; lean_object* v___x_3906_; 
v___x_3904_ = lean_unbox(v_a_3892_);
lean_dec(v_a_3892_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*1, v___x_3904_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*1 + 1, v_offsetCnstrs_3896_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*1 + 2, v_newGoals_3898_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3903_);
v___x_3906_ = v___x_3894_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3903_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec_ref(v_config_3852_);
v_a_3911_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3891_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3891_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
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
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_3919_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3889_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3889_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_3927_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3887_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3887_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec_ref(v___x_3874_);
v___x_3935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_3936_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3853_, v___x_3935_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3936_) == 0)
{
uint8_t v___x_3937_; 
lean_dec_ref_known(v___x_3936_, 1);
v___x_3937_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3875_);
if (v___x_3937_ == 0)
{
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3938_; 
lean_dec_ref(v___x_3875_);
v___x_3938_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3957_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3957_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3957_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
uint8_t v_transparency_3943_; lean_object* v_occs_3944_; uint8_t v_newGoals_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3956_; 
v_transparency_3943_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1);
v_occs_3944_ = lean_ctor_get(v_config_3852_, 0);
v_newGoals_3945_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 2);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_config_3852_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3947_ = v_config_3852_;
v_isShared_3948_ = v_isSharedCheck_3956_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_occs_3944_);
lean_dec(v_config_3852_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3956_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_occs_3944_);
lean_ctor_set_uint8(v_reuseFailAlloc_3955_, sizeof(void*)*1, v_transparency_3943_);
v___x_3950_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
uint8_t v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_unbox(v_a_3939_);
lean_dec(v_a_3939_);
lean_ctor_set_uint8(v___x_3950_, sizeof(void*)*1 + 1, v___x_3951_);
lean_ctor_set_uint8(v___x_3950_, sizeof(void*)*1 + 2, v_newGoals_3945_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3950_);
v___x_3953_ = v___x_3941_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3950_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec_ref(v_config_3852_);
v_a_3958_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3938_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3938_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_3966_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3936_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3936_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec_ref(v___x_3874_);
v___x_3974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_3975_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3853_, v___x_3974_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3975_) == 0)
{
uint8_t v___x_3976_; 
lean_dec_ref_known(v___x_3975_, 1);
v___x_3976_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3875_);
if (v___x_3976_ == 0)
{
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3977_; 
lean_dec_ref(v___x_3875_);
lean_inc_ref(v_item_3853_);
v___x_3977_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_value_3978_; lean_object* v___x_3979_; 
lean_dec_ref_known(v___x_3977_, 1);
v_value_3978_ = lean_ctor_get(v_item_3853_, 2);
lean_inc(v_value_3978_);
lean_dec_ref(v_item_3853_);
v___x_3979_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_3978_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3998_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_3998_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3998_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
uint8_t v_transparency_3984_; uint8_t v_offsetCnstrs_3985_; uint8_t v_newGoals_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3996_; 
v_transparency_3984_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1);
v_offsetCnstrs_3985_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 1);
v_newGoals_3986_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 2);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_config_3852_);
if (v_isSharedCheck_3996_ == 0)
{
lean_object* v_unused_3997_; 
v_unused_3997_ = lean_ctor_get(v_config_3852_, 0);
lean_dec(v_unused_3997_);
v___x_3988_ = v_config_3852_;
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
else
{
lean_dec(v_config_3852_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v_a_3980_);
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3995_, sizeof(void*)*1, v_transparency_3984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3995_, sizeof(void*)*1 + 1, v_offsetCnstrs_3985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3995_, sizeof(void*)*1 + 2, v_newGoals_3986_);
v___x_3991_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3993_; 
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3991_);
v___x_3993_ = v___x_3982_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec_ref(v_config_3852_);
v_a_3999_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3979_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3979_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_4007_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3977_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3977_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_4015_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3975_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3975_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec_ref(v___x_3874_);
v___x_4023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_4024_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3853_, v___x_4023_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_4024_) == 0)
{
uint8_t v___x_4025_; 
lean_dec_ref_known(v___x_4024_, 1);
v___x_4025_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3875_);
if (v___x_4025_ == 0)
{
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_4026_; 
lean_dec_ref(v___x_3875_);
lean_inc_ref(v_item_3853_);
v___x_4026_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_value_4027_; lean_object* v___x_4028_; 
lean_dec_ref_known(v___x_4026_, 1);
v_value_4027_ = lean_ctor_get(v_item_3853_, 2);
lean_inc(v_value_4027_);
lean_dec_ref(v_item_3853_);
v___x_4028_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_4027_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4047_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4047_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4047_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
uint8_t v_transparency_4033_; uint8_t v_offsetCnstrs_4034_; lean_object* v_occs_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4046_; 
v_transparency_4033_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1);
v_offsetCnstrs_4034_ = lean_ctor_get_uint8(v_config_3852_, sizeof(void*)*1 + 1);
v_occs_4035_ = lean_ctor_get(v_config_3852_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_config_3852_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4037_ = v_config_3852_;
v_isShared_4038_ = v_isSharedCheck_4046_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_occs_4035_);
lean_dec(v_config_3852_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4046_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_occs_4035_);
lean_ctor_set_uint8(v_reuseFailAlloc_4045_, sizeof(void*)*1, v_transparency_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4045_, sizeof(void*)*1 + 1, v_offsetCnstrs_4034_);
v___x_4040_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
uint8_t v___x_4041_; lean_object* v___x_4043_; 
v___x_4041_ = lean_unbox(v_a_4029_);
lean_dec(v_a_4029_);
lean_ctor_set_uint8(v___x_4040_, sizeof(void*)*1 + 2, v___x_4041_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4040_);
v___x_4043_ = v___x_4031_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4040_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec_ref(v_config_3852_);
v_a_4048_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4028_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4028_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_4056_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4026_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4026_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
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
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_4064_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4024_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4024_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
else
{
uint8_t v___x_4072_; 
lean_dec_ref(v___x_3874_);
lean_dec_ref(v_config_3852_);
v___x_4072_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3875_);
if (v___x_4072_ == 0)
{
lean_dec_ref(v_item_3853_);
v_item_3862_ = v___x_3875_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
lean_object* v_value_4073_; lean_object* v___x_4074_; 
lean_dec_ref(v___x_3875_);
v_value_4073_ = lean_ctor_get(v_item_3853_, 2);
lean_inc(v_value_4073_);
lean_dec_ref(v_item_3853_);
v___x_4074_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_4073_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_4074_;
}
}
}
else
{
lean_dec_ref(v_config_3852_);
v_item_3862_ = v_item_3853_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v_item_3853_);
lean_dec_ref(v_config_3852_);
v_a_4075_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_3872_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_3872_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
v___jp_3861_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3870_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3862_, v___x_3869_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_4083_, lean_object* v_item_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_4083_, v_item_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_4095_, v___y_4099_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4131_, lean_object* v_msg_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_msg_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4141_, v_msg_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4151_, lean_object* v_macroStack_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4151_, v_macroStack_4152_, v___y_4157_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4161_, lean_object* v_macroStack_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4161_, v_macroStack_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
return v_res_4170_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4171_ = lean_box(0);
v___x_4172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4173_ = l_Lean_mkConst(v___x_4172_, v___x_4171_);
return v___x_4173_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4176_, lean_object* v_cfgItem_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4185_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4186_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4176_, v_cfgItem_4177_, v___x_4185_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4187_, lean_object* v_cfgItem_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4187_, v_cfgItem_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v_cfgItem_4188_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4198_, lean_object* v_init_4199_, uint8_t v_logExceptions_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v_onErr_4205_; lean_object* v_eval_4206_; 
v_onErr_4205_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4200_ == 0)
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4206_, v_init_4199_, v_cfg_4198_, v_onErr_4205_, v_logExceptions_4200_, v_a_4202_, v_a_4203_);
return v___x_4207_;
}
else
{
uint8_t v_recover_4208_; lean_object* v___x_4209_; 
v_recover_4208_ = lean_ctor_get_uint8(v_a_4201_, sizeof(void*)*1);
v___x_4209_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4206_, v_init_4199_, v_cfg_4198_, v_onErr_4205_, v_recover_4208_, v_a_4202_, v_a_4203_);
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4210_, lean_object* v_init_4211_, lean_object* v_logExceptions_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
uint8_t v_logExceptions_boxed_4217_; lean_object* v_res_4218_; 
v_logExceptions_boxed_4217_ = lean_unbox(v_logExceptions_4212_);
v_res_4218_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4210_, v_init_4211_, v_logExceptions_boxed_4217_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec_ref(v_a_4213_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4219_, lean_object* v_init_4220_, uint8_t v_logExceptions_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4219_, v_init_4220_, v_logExceptions_4221_, v_a_4222_, v_a_4228_, v_a_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4232_, lean_object* v_init_4233_, lean_object* v_logExceptions_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
uint8_t v_logExceptions_boxed_4244_; lean_object* v_res_4245_; 
v_logExceptions_boxed_4244_ = lean_unbox(v_logExceptions_4234_);
v_res_4245_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4232_, v_init_4233_, v_logExceptions_boxed_4244_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
return v_res_4245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4253_ = l_Lean_MessageData_ofFormat(v___x_4252_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4267_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4268_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4266_, v_x_4256_, v___x_4267_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4280_, uint8_t v_symm_4281_, lean_object* v_a_4282_, lean_object* v_x_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4280_, v_symm_4281_, v_x_4283_, v_a_4282_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4294_, lean_object* v_symm_4295_, lean_object* v_a_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
uint8_t v_symm_boxed_4307_; lean_object* v_res_4308_; 
v_symm_boxed_4307_ = lean_unbox(v_symm_4295_);
v_res_4308_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4294_, v_symm_boxed_4307_, v_a_4296_, v_x_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4309_, lean_object* v___x_4310_, lean_object* v___f_4311_, uint8_t v_symm_4312_, lean_object* v_term_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___x_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4323_ = lean_box(v_symm_4312_);
lean_inc_ref(v_a_4309_);
lean_inc(v_term_4313_);
v___f_4324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4324_, 0, v_term_4313_);
lean_closure_set(v___f_4324_, 1, v___x_4323_);
lean_closure_set(v___f_4324_, 2, v_a_4309_);
v___x_4325_ = lean_box(v_symm_4312_);
v___x_4326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4326_, 0, v_term_4313_);
lean_closure_set(v___x_4326_, 1, v___x_4325_);
lean_closure_set(v___x_4326_, 2, v_a_4309_);
v___x_4327_ = l_Lean_Elab_Tactic_withLocation(v___x_4310_, v___f_4324_, v___x_4326_, v___f_4311_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4328_, lean_object* v___x_4329_, lean_object* v___f_4330_, lean_object* v_symm_4331_, lean_object* v_term_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v_symm_boxed_4342_; lean_object* v_res_4343_; 
v_symm_boxed_4342_ = lean_unbox(v_symm_4331_);
v_res_4343_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4328_, v___x_4329_, v___f_4330_, v_symm_boxed_4342_, v_term_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___x_4329_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4360_ = lean_unsigned_to_nat(1u);
v___x_4361_ = l_Lean_Syntax_getArg(v_stx_4350_, v___x_4360_);
v___x_4362_ = 1;
v___x_4363_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4364_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4361_, v___x_4363_, v___x_4362_, v_a_4351_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v___f_4366_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4367_ = lean_unsigned_to_nat(3u);
v___x_4368_ = l_Lean_Syntax_getArg(v_stx_4350_, v___x_4367_);
v___x_4369_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4368_);
lean_dec(v___x_4368_);
v___f_4370_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4370_, 0, v_a_4365_);
lean_closure_set(v___f_4370_, 1, v___x_4369_);
lean_closure_set(v___f_4370_, 2, v___f_4366_);
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = l_Lean_Syntax_getArg(v_stx_4350_, v___x_4371_);
v___x_4373_ = lean_unsigned_to_nat(2u);
v___x_4374_ = l_Lean_Syntax_getArg(v_stx_4350_, v___x_4373_);
v___x_4375_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4372_, v___x_4374_, v___f_4370_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v___x_4374_);
return v___x_4375_;
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v_a_4376_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4364_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4364_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_stx_4384_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4410_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4410_, v___x_4411_, v___x_4412_, v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4445_ = l_Lean_addBuiltinDeclarationRanges(v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4447_;
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
